package org.drools.core;

import org.drools.base.base.ObjectType;

public class ObjectTypeNode extends BaseNode {

    private ObjectType objectType;
    private long       expirationOffset = -1;

    public ObjectTypeNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    public ObjectTypeNode(int id, int pathIndex, int objectIndex, int size, int walkBack) {
        super(id, pathIndex, objectIndex, size, walkBack);
    }

    public ObjectType getObjectType() { return objectType; }
    public void setObjectType(ObjectType objectType) { this.objectType = objectType; }

    public long getExpirationOffset() { return expirationOffset; }
    public void setExpirationOffset(long expirationOffset) { this.expirationOffset = expirationOffset; }
}
