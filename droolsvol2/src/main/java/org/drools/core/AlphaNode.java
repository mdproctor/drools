package org.drools.core;

public class AlphaNode extends BaseNode {
    public AlphaNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    public AlphaNode(int id, int pathIndex, int objectIndex, int size, int walkBack) {
        super(id, pathIndex, objectIndex, size, walkBack);
    }
}
