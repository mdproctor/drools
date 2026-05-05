package org.drools.core;

import org.drools.base.common.NetworkNode;

/**
 * Vol2 node type constants and capability queries.
 *
 * <p>Vol2's model of beta vs alpha differs from vol1's — notably, EvalConditionNode
 * IS a beta node in vol2 (it operates on partial tuples), whereas vol1 did not
 * classify it as beta. The bitmask compositions here reflect vol2's model.
 * Do NOT use {@code NodeTypeEnums} utility methods on vol2 nodes; the bitmask
 * semantics are incompatible. The integer identity values (the {@code N << shift}
 * portion) do happen to match vol1 equivalents for familiar node types, but this
 * is for cross-reference clarity only — vol2 is not coupled to vol1's enumeration.
 *
 * <p>When vol1 is eventually removed, the constants and methods here are candidates
 * for migration into {@code NodeTypeEnums} in {@code drools-base}, which would
 * become the single shared registry.
 */
public class Vol2NodeTypeEnums {

    /** Shift that separates the node identity (high bits) from capability bitmasks (low bits). */
    public static final int shift = 15;

    // --- Capability bitmasks -----------------------------------------------

    /** Node operates on partial tuples — Forgy's "beta" phase. */
    public static final int BetaMask         = 1 << 9;

    /** Node has both a left inlet and a right inlet (LeftAndRightNode subclass). */
    public static final int LeftAndRightMask = 1 << 10;

    /** Node is a terminal node (produces agenda items / fires consequences). */
    public static final int TerminalMask     = 1 << 7;

    /** Node creates and owns a Memory instance. */
    public static final int MemoryMask       = 1 << 11;

    // --- Alpha network (single-fact processing) ----------------------------

    public static final int EntryPointNode       = (100 << shift);
    public static final int ObjectTypeNode       = (110 << shift);
    public static final int AlphaNode            = (120 << shift);
    public static final int FilterNode           = (125 << shift); // vol2-specific predicate filter
    public static final int WindowNode           = (130 << shift) | MemoryMask;
    public static final int LeftInputAdapterNode = (140 << shift) | MemoryMask;

    // --- Beta network — single-inlet (no right inlet) ----------------------

    public static final int EvalConditionNode    = (200 << shift) | BetaMask | MemoryMask;
    public static final int ConditionalBranchNode= (210 << shift) | BetaMask | MemoryMask;
    public static final int FromNode             = (220 << shift) | BetaMask | MemoryMask;
    public static final int QueryElementNode     = (230 << shift) | BetaMask | MemoryMask;
    public static final int AsyncSendNode        = (240 << shift) | BetaMask;
    public static final int AsyncReceiveNode     = (250 << shift) | BetaMask | MemoryMask;
    public static final int TimerNode            = (260 << shift) | BetaMask | MemoryMask;
    public static final int TupleToObjectNode    = (270 << shift) | BetaMask | MemoryMask;

    // --- Beta network — two-inlet (LeftAndRightNode subclasses) ------------

    public static final int JoinNode        = (300 << shift) | BetaMask | LeftAndRightMask | MemoryMask;
    public static final int NotNode         = (310 << shift) | BetaMask | LeftAndRightMask | MemoryMask;
    public static final int ExistsNode      = (320 << shift) | BetaMask | LeftAndRightMask | MemoryMask;
    public static final int AccumulateNode  = (330 << shift) | BetaMask | LeftAndRightMask | MemoryMask;

    // --- Terminal -----------------------------------------------------------

    public static final int TerminalNode    = (400 << shift) | TerminalMask;

    // --- Capability queries -------------------------------------------------

    /** True for all nodes operating on partial tuples (vol2's correct Forgy definition of beta). */
    public static boolean isBetaNode(NetworkNode node) {
        return (node.getType() & BetaMask) != 0;
    }

    /** True for two-inlet beta nodes: JoinNode, NotNode, ExistsNode, AccumulateNode. */
    public static boolean isLeftAndRightNode(NetworkNode node) {
        return (node.getType() & LeftAndRightMask) != 0;
    }

    public static boolean isTerminalNode(NetworkNode node) {
        return (node.getType() & TerminalMask) != 0;
    }

    public static boolean isMemoryFactory(NetworkNode node) {
        return (node.getType() & MemoryMask) != 0;
    }
}
