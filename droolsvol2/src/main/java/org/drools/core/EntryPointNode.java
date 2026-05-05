package org.drools.core;
/** TODO #6650: Temporary stub — vol2 entry point node not yet implemented. */
public class EntryPointNode extends BaseNode {
    @Override public int getType() { return Vol2NodeTypeEnums.EntryPointNode; }

    public EntryPointNode() { }
    public EntryPointNode(int id, int pathIndex, int objectIndex) { super(id, pathIndex, objectIndex); }
}
