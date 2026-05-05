package org.drools.core;

/** TODO #6650: Temporary stub — vol2 eval condition node not yet implemented. */
public class EvalConditionNode extends BaseNode {
    @Override public int getType() { return Vol2NodeTypeEnums.EvalConditionNode; }

    public EvalConditionNode() { }
    public EvalConditionNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }
}
