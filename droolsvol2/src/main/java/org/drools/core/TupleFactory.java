package org.drools.core;

/**
 * Creates the correct concrete tuple type for a given downstream node.
 *
 * <p>Different node types require different tuple implementations:
 * <ul>
 *   <li>{@link NotNode} and {@link ExistsNode} need blockable/blocker variants
 *       that track right-match counts and linked-list pointers for blocking.
 *   <li>All other nodes use the plain {@link JoinTuple} / {@link ObjectHandleTuple}.
 * </ul>
 *
 * <p>The switch on {@link Vol2NodeTypeEnums} type integers avoids megamorphic
 * call sites at creation points in the evaluation engine — consistent with the
 * same pattern used in {@link NodeCaster} for dispatch.
 *
 * <p>Peer-tuple creation (for fan-out at shared nodes) is not yet implemented —
 * {@code TupleImpl} does not yet expose {@code initPeer}/{@code setPeer}. Add
 * {@code createPeer} here when the evaluation engine requires fan-out support.
 *
 * <p>Inspired by {@code TupleFactory} in vol1 ({@code drools-core}). Vol2's
 * tuple hierarchy ({@code JoinTuple}, {@code ObjectHandleTuple}, etc.) differs
 * from vol1's ({@code LeftTuple}, {@code NotNodeLeftTuple}, etc.) but the
 * node-type-driven dispatch pattern is the same.
 */
@SuppressWarnings("unchecked")
public class TupleFactory {

    /**
     * Creates a right-inlet handle tuple wrapping a raw fact handle.
     * Called when a handle arrives at the right inlet of a node from a DataSource.
     *
     * <p>Not/Exists nodes receive an {@link ObjectHandleTupleBlocker} — it will
     * block left-side matches. All other nodes receive a plain
     * {@link ObjectHandleTuple}.
     */
    public static <T> ObjectHandleTuple<T> createHandleTuple(ObjectHandleImpl<T> handle,
                                                              BaseNode node) {
        return switch (node.getType()) {
            case Vol2NodeTypeEnums.NotNode,
                 Vol2NodeTypeEnums.ExistsNode -> new ObjectHandleTupleBlocker<>(handle, node);
            default                           -> new ObjectHandleTuple<>(handle, node);
        };
    }

    /**
     * Creates a join-result tuple combining a left-side tuple and a right-side
     * tuple, propagating to the given downstream node.
     *
     * <p>Not/Exists nodes produce a {@link JoinTupleBlockable} — the result can
     * be blocked (for NotNode) or unblocked (for ExistsNode) as right-side facts
     * arrive or retract. All other nodes produce a plain {@link JoinTuple}.
     */
    public static <T> JoinTuple<T> createJoinTuple(TupleImpl<?> left,
                                                    TupleImpl<T> right,
                                                    BaseNode node) {
        return switch (node.getType()) {
            case Vol2NodeTypeEnums.NotNode,
                 Vol2NodeTypeEnums.ExistsNode -> new JoinTupleBlockable<>(left, right, node);
            default                           -> new JoinTuple<>(left, right, node);
        };
    }
}
