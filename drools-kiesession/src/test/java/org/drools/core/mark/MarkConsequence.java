package org.drools.core.mark;

import org.drools.base.base.ObjectType;
import org.drools.base.base.ValueResolver;
import org.drools.base.reteoo.BaseTuple;
import org.drools.base.rule.Declaration;
import org.drools.base.rule.MutableTypeConstraint;
import org.drools.base.rule.Pattern;
import org.drools.base.rule.consequence.Consequence;
import org.drools.base.rule.consequence.ConsequenceContext;
import org.drools.base.rule.constraint.BetaConstraint;
import org.drools.core.RuleBaseConfiguration;
import org.drools.core.common.BetaConstraints;
import org.drools.core.common.ReteEvaluator;
import org.drools.core.mark.Functions.Function1;
import org.drools.core.mark.Functions.Function2;
import org.drools.core.mark.Functions.Function3;
import org.drools.core.mark.Functions.Function4;
import org.drools.core.mark.IntFunctions.IntFunction1;
import org.drools.core.mark.IntFunctions.IntFunction2;
import org.drools.core.mark.IntFunctions.IntFunction3;
import org.drools.core.mark.IntFunctions.IntFunction4;
import org.drools.core.mark.MarkConstraint.MarkContextEntry;
import org.drools.core.mark.VoidFunctions.VoidFunction1;
import org.drools.core.mark.VoidFunctions.VoidFunction2;
import org.drools.core.mark.VoidFunctions.VoidFunction3;
import org.drools.core.mark.VoidFunctions.VoidFunction4;
import org.drools.core.reteoo.BetaMemory;
import org.drools.core.reteoo.Tuple;
import org.drools.core.reteoo.builder.BuildContext;
import org.drools.util.bitmask.BitMask;
import org.kie.api.runtime.rule.FactHandle;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class MarkConsequence<T extends ConsequenceContext> implements Consequence<T> {

    String name;

    protected final Declaration[] declarations;

    private VoidFunction1<Object>                          p1;
    private VoidFunction2<Object, Object>                 p2;
    private VoidFunction3<Object, Object, Object>         p3;
    private VoidFunction4<Object, Object, Object, Object> p4;


    private int pIndex;

    public MarkConsequence(String name, Declaration[] declarations) {
        this.declarations = declarations;
        this.name = name;
    }

    @Override
    public void evaluate(T helper, ValueResolver valueResolver) throws Exception {
        BaseTuple t = helper.getTuple();
        switch (pIndex) {
            case 1: {
                p1.apply(t.getFactHandle().getObject());
                return;
            }
            case 2: {
                p2.apply(t.getParent().getFactHandle().getObject(), t.getFactHandle().getObject());
                return;
            } case 3: {
                BaseTuple    v2 = t.getParent();
                p3.apply(v2.getParent().getFactHandle().getObject(),
                         v2.getFactHandle().getObject(),
                         t.getFactHandle().getObject());
                return;
            } case 4: {
                BaseTuple    v2 = t.getParent();
                BaseTuple    v3 = v2.getParent();
                p4.apply(v2.getParent().getFactHandle().getObject(),
                         v2.getFactHandle().getObject(),
                         v3.getFactHandle().getObject(),
                         t.getFactHandle().getObject());
                return;
            } default:
                throw new RuntimeException("No matching predicate on index: " + pIndex);
        }
    }

    @Override
    public String getName() {
        return name;
    }

    public Declaration[] getRequiredDeclarations() {
        return declarations;
    }

    public void replaceDeclaration(Declaration oldDecl, Declaration newDecl) {

    }


    public int getPIndex() {
        return pIndex;
    }

    public <A> void setFunction(VoidFunction1<A> p1) {
        this.p1 = (VoidFunction1<Object>) p1;
        pIndex = 1;
    }

    public <A, B> void setFunction(VoidFunction2<A, B> p2) {
        this.p2 = (VoidFunction2<Object, Object>) p2;
        pIndex = 2;
    }

    public <A, B, C> void setFunction(VoidFunction3<A, B, C> p3) {
        this.p3 = (VoidFunction3<Object, Object, Object>) p3;
        pIndex = 3;
    }

    public <A, B, C, D> void setFunction(VoidFunction4<A, B, C, D> p4) {
        this.p4 = (VoidFunction4<Object, Object, Object, Object>) p4;
        pIndex = 4;
    }

    @Override
    public MarkConsequence clone() {
        Declaration[]   clonedDeclrs = Arrays.stream(declarations).map(d -> d.clone()).collect(Collectors.toList()).toArray(new Declaration[0]);
        MarkConsequence clone        = new MarkConsequence(name, clonedDeclrs);
        clone.pIndex = pIndex;
        clone.p1 = p1;
        clone.p2 = p2;
        clone.p3 = p3;
        clone.p4 = p4;

        Declaration[] clonedDeclarations = new Declaration[declarations.length];
        for (int i = 0; i < declarations.length; i++) {
            clonedDeclarations[i] = declarations[i].clone();
        }

        return clone;
    }

}
