package org.drools.core;

/** TODO #6650: Temporary stub — vol2 not/negation node not yet implemented. */
public class NotNode extends BetaNode {
    private boolean emptyBetaConstraints;

    public NotNode() { }
    public NotNode(int id, int pathIndex, int objectIndex) { super(id, pathIndex, objectIndex); }

    public boolean isEmptyBetaConstraints() { return emptyBetaConstraints; }
    public void setEmptyBetaConstraints(boolean empty) { this.emptyBetaConstraints = empty; }
}
