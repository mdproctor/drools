package org.drools.core;

/**
 * Casts BaseNode references to concrete types before calling methods on them.
 *
 * <p>When an evaluator iterates an outputs array and calls methods through a
 * BaseNode reference, the JVM call site becomes megamorphic if many concrete
 * types pass through it and the JIT will not inline. By switching on
 * {@link Vol2NodeTypeEnums#getType()} and casting to the concrete class inside
 * each arm, each arm's call site is monomorphic and JIT-inlineable.
 *
 * <p>Only cast a node after confirming its type via
 * {@link Vol2NodeTypeEnums#isBetaNode}, {@link Vol2NodeTypeEnums#isTerminalNode},
 * etc., or after a switch that already established the type.
 *
 * <p>Inspired by {@code SuperCacheFixer} in vol1 ({@code drools-core}), which
 * solved the same JVM secondary super cache problem for interface dispatch. Vol2
 * uses {@code BaseNode} (a class, not an interface) as its traversal type, so
 * the issue manifests as megamorphic call sites rather than secondary super cache
 * thrashing — but the fix is identical: cast to concrete before calling.
 */
@SuppressWarnings("unchecked")
public class NodeCaster {

    /**
     * Dispatches to the correct concrete type via a switch on node type.
     * Use the return value inside a switch arm — the JIT sees the concrete type
     * at each arm and can inline subsequent method calls.
     */
    public static BaseNode cast(BaseNode n) {
        return switch (n.getType()) {
            case Vol2NodeTypeEnums.EntryPointNode        -> (EntryPointNode) n;
            case Vol2NodeTypeEnums.ObjectTypeNode        -> (ObjectTypeNode) n;
            case Vol2NodeTypeEnums.AlphaNode             -> (AlphaNode) n;
            case Vol2NodeTypeEnums.FilterNode            -> (FilterNode<?, ?>) n;
            case Vol2NodeTypeEnums.WindowNode            -> (WindowNode) n;
            case Vol2NodeTypeEnums.LeftInputAdapterNode  -> (LeftInputAdapterNode) n;
            case Vol2NodeTypeEnums.EvalConditionNode     -> (EvalConditionNode) n;
            case Vol2NodeTypeEnums.ConditionalBranchNode -> (ConditionalBranchNode) n;
            case Vol2NodeTypeEnums.FromNode              -> (FromNode<?>) n;
            case Vol2NodeTypeEnums.QueryElementNode      -> (QueryElementNode) n;
            case Vol2NodeTypeEnums.AsyncSendNode         -> (AsyncSendNode) n;
            case Vol2NodeTypeEnums.AsyncReceiveNode      -> (AsyncReceiveNode) n;
            case Vol2NodeTypeEnums.TimerNode             -> (TimerNode) n;
            case Vol2NodeTypeEnums.TupleToObjectNode     -> (TupleToObjectNode) n;
            case Vol2NodeTypeEnums.JoinNode              -> (JoinNode) n;
            case Vol2NodeTypeEnums.NotNode               -> (NotNode) n;
            case Vol2NodeTypeEnums.ExistsNode            -> (ExistsNode) n;
            case Vol2NodeTypeEnums.AccumulateNode        -> (AccumulateNode) n;
            case Vol2NodeTypeEnums.TerminalNode          -> (TerminalNode) n;
            default -> throw new IllegalStateException("Unknown vol2 node type: " + n);
        };
    }

    /** Typed cast for use inside a switch arm or after isTerminalNode check. */
    public static TerminalNode asTerminalNode(BaseNode n)          { return (TerminalNode) n; }

    /** Typed cast for use inside a switch arm or after isLeftAndRightNode check. */
    public static LeftAndRightNode asLeftAndRightNode(BaseNode n)  { return (LeftAndRightNode) n; }

    /** Typed cast for use inside a switch arm or after isBetaNode check. */
    public static BetaNode asBetaNode(BaseNode n)                  { return (BetaNode) n; }
}
