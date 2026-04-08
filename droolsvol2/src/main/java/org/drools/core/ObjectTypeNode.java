package org.drools.core;

public class ObjectTypeNode extends BaseNode {

    public ObjectTypeNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    public ObjectTypeNode(int id, int pathIndex, int objectIndex, int size, int walkBack) {
        super(id, pathIndex, objectIndex, size, walkBack);
    }
}
