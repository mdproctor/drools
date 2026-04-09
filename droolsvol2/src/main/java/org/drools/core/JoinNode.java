package org.drools.core;

/** Vol2 join node — extends BetaNode for bi-linear network joins. */
public class JoinNode extends BetaNode {
    public JoinNode() { }
    public JoinNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }
}
