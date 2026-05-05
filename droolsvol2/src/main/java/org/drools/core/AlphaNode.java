package org.drools.core;

import org.drools.base.rule.constraint.AlphaNodeFieldConstraint;
import org.drools.util.bitmask.BitMask;

public class AlphaNode extends BaseNode {
    private AlphaNodeFieldConstraint constraint;

    @Override public int getType() { return Vol2NodeTypeEnums.AlphaNode; }

    public AlphaNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    public AlphaNode(int id, int pathIndex, int objectIndex, int size, int walkBack) {
        super(id, pathIndex, objectIndex, size, walkBack);
    }

    public AlphaNodeFieldConstraint getConstraint() { return constraint; }
    public void setConstraint(AlphaNodeFieldConstraint constraint) { this.constraint = constraint; }

    /** TODO #6650: alpha node mask update not yet implemented in vol2 */
    public BitMask updateMask(BitMask mask) { return mask; }
}
