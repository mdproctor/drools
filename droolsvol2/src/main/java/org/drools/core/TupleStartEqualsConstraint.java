package org.drools.core;
import org.drools.base.rule.constraint.BetaConstraint;
import org.kie.api.runtime.rule.FactHandle;
import org.drools.base.reteoo.BaseTuple;
/** TODO #6650: Temporary stub. */
@SuppressWarnings("unchecked")
public class TupleStartEqualsConstraint implements BetaConstraint<Object> {
    private static final TupleStartEqualsConstraint INSTANCE = new TupleStartEqualsConstraint();
    public static TupleStartEqualsConstraint getInstance() { return INSTANCE; }
    @Override public boolean isAllowedCachedLeft(Object context, FactHandle handle) { return true; }
    @Override public boolean isAllowedCachedRight(BaseTuple tuple, Object context) { return true; }
    @Override public Object createContext() { return null; }
    @Override public BetaConstraint<Object> cloneIfInUse() { return this; }
    @Override public boolean isTemporal() { return false; }
}
