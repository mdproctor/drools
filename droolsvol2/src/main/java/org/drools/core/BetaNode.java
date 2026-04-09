package org.drools.core;

/**
 * Vol2 beta node — base class for join nodes (nodes with two inputs).
 * TODO #6650: implement vol2 BetaNode fully once join node design is settled.
 */
public class BetaNode extends BaseNode {

    private BaseNode rightInput;

    public BetaNode() { }

    public BetaNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    public BaseNode getRightInput() { return rightInput; }
    public void setRightInput(BaseNode rightInput) { this.rightInput = rightInput; }

    /** TODO #6650: beta constraints not yet integrated in vol2 */
    public BetaConstraints getConstraints() { return null; }
    public boolean isRightInputPassive() { return false; }
}
