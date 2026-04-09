package org.drools.core;
import org.drools.base.rule.Declaration;
import org.drools.base.rule.constraint.BetaConstraint;
import org.drools.base.rule.constraint.Constraint;
import org.drools.base.reteoo.BaseTuple;
import org.kie.api.runtime.rule.FactHandle;
import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
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
    @Override public Declaration[] getRequiredDeclarations() { return new Declaration[0]; }
    @Override public void replaceDeclaration(Declaration oldDecl, Declaration newDecl) { }
    @Override public Constraint clone() { return this; }
    @Override public Constraint.ConstraintType getType() { return Constraint.ConstraintType.BETA; }
    @Override public void writeExternal(ObjectOutput out) throws IOException { }
    @Override public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException { }
}
