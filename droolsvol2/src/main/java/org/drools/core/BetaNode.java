package org.drools.core;

/**
 * Vol2 beta node — base class for join nodes (nodes with two inputs).
 * TODO #6650: implement vol2 BetaNode fully once join node design is settled.
 */
public class BetaNode extends BaseNode {

    private BaseNode      rightInput;
    private BetaConstraints constraints;

    public BetaNode() { }

    public BetaNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    @Override
    public void setLeftInput(BaseNode leftInput) {
        super.setLeftInput(leftInput);
        updateHashCode();
    }

    public BaseNode getRightInput() { return rightInput; }
    public void setRightInput(BaseNode rightInput) {
        this.rightInput = rightInput;
        updateHashCode();
    }

    public BetaConstraints getConstraints() { return constraints; }
    public void setConstraints(BetaConstraints constraints) { this.constraints = constraints; }

    public boolean isRightInputPassive() { return false; }

    private void updateHashCode() {
        // hashcode is final in BaseNode — update it here when inputs are set
        int h = getClass().hashCode();
        h = 31 * h + (leftInput  != null ? leftInput.getId()  : 0);
        h = 31 * h + (rightInput != null ? rightInput.getId() : 0);
        this.hashcode = h;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        BetaNode other = (BetaNode) obj;
        return leftInput != null && rightInput != null
               && leftInput.getId()  == other.leftInput.getId()
               && rightInput.getId() == other.rightInput.getId();
    }
}
