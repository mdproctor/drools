package org.drools.core;
/** TODO #6650: Temporary stub — vol2 exists node not yet implemented. */
public class ExistsNode extends LeftAndRightNode {
    @Override public int getType() { return Vol2NodeTypeEnums.ExistsNode; }

    public ExistsNode() { }
    public ExistsNode(int id, int pathIndex, int objectIndex) { super(id, pathIndex, objectIndex); }
}
