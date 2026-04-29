package org.drools.core;

/**
 * Base for all beta nodes — nodes that operate on partial tuples (Forgy's "second phase").
 * Two structural variants exist:
 *   - LeftAndRightNode: two-inlet nodes (JoinNode, NotNode, ExistsNode, AccumulateNode)
 *   - Single-inlet nodes: e.g. EvalConditionNode (filters partial tuples, no right input)
 */
public abstract class BetaNode extends BaseNode {

    public BetaNode() { }

    public BetaNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }
}
