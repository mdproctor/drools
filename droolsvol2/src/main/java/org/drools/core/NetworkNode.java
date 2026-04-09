package org.drools.core;

/**
 * Vol2 NetworkNode extends drools-base NetworkNode so BaseNode is compatible
 * with NodeTypeEnums and other drools-base utilities that take NetworkNode.
 * Vol2-specific methods (pathIndex, size, objectIndex, walkBack) are added here.
 */
public interface NetworkNode extends org.drools.base.common.NetworkNode {
    int getPathIndex();
    int getSize();
    int getObjectIndex();
    int getWalkBack();
}
