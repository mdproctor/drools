package org.drools.core;

/** Vol2 join node — extends BetaNode for bi-linear network joins. */
public class JoinNode extends BetaNode implements MemoryFactory<JoinMemory> {
    public JoinNode() { }
    public JoinNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    @Override
    public int getMemoryId() { return getId(); }

    @Override
    public JoinMemory createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) {
        return new JoinMemory(getMemoryId());
    }
}
