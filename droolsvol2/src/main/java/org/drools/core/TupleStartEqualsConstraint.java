package org.drools.core;
import org.drools.base.rule.constraint.BetaConstraint;
/** TODO #6650: Temporary stub. */
public class TupleStartEqualsConstraint implements BetaConstraint {
    private static final TupleStartEqualsConstraint INSTANCE = new TupleStartEqualsConstraint();
    public static TupleStartEqualsConstraint getInstance() { return INSTANCE; }
    @Override public BetaConstraint cloneIfInUse() { return this; }
}
