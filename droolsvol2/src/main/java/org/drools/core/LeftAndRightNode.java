package org.drools.core;

/**
 * Abstract base for beta nodes with both a left and a right inlet:
 * JoinNode, NotNode, ExistsNode, AccumulateNode.
 *
 * Single-inlet beta nodes (e.g. EvalConditionNode) extend BetaNode directly.
 */
public abstract class LeftAndRightNode extends BetaNode {

    private BaseNode         rightInput;
    private BetaConstraints  constraints;

    public LeftAndRightNode() { }

    public LeftAndRightNode(int id, int pathIndex, int objectIndex) {
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

    private void updateHashCode() {
        int h = getClass().hashCode();
        h = 31 * h + (leftInput  != null ? leftInput.getId()  : 0);
        h = 31 * h + (rightInput != null ? rightInput.getId() : 0);
        this.hashcode = h;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        LeftAndRightNode other = (LeftAndRightNode) obj;
        return leftInput != null && rightInput != null
               && leftInput.getId()  == other.leftInput.getId()
               && rightInput.getId() == other.rightInput.getId();
    }
}
