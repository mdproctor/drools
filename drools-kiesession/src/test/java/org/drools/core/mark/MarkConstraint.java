package org.drools.core.mark;

import org.drools.base.base.ObjectType;
import org.drools.base.base.ValueResolver;
import org.drools.base.reteoo.BaseTuple;
import org.drools.base.rule.Declaration;
import org.drools.base.rule.MutableTypeConstraint;
import org.drools.base.rule.Pattern;
import org.drools.base.rule.accessor.FieldValue;
import org.drools.base.rule.accessor.ReadAccessor;
import org.drools.base.rule.accessor.TupleValueExtractor;
import org.drools.base.rule.constraint.BetaConstraint;
import org.drools.base.rule.IndexableConstraint;
import org.drools.base.rule.IntervalProviderConstraint;
import org.drools.base.time.Interval;
import org.drools.base.util.FieldIndex;
import org.drools.base.util.index.ConstraintTypeOperator;
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
import org.drools.core.mark.Predicates.Predicate1;
import org.drools.core.mark.Predicates.Predicate2;
import org.drools.core.mark.Predicates.Predicate3;
import org.drools.core.mark.Predicates.Predicate4;
import org.drools.core.reteoo.BetaMemory;
import org.drools.core.reteoo.Tuple;
import org.drools.core.reteoo.TupleMemory;
import org.drools.core.reteoo.builder.BuildContext;
import org.drools.core.util.index.IndexFactory;
import org.drools.core.util.index.IndexMemory;
import org.drools.core.util.index.IndexSpec;
import org.drools.core.util.index.TupleList;
import org.drools.util.bitmask.BitMask;
import org.kie.api.KieBaseConfiguration;
import org.kie.api.runtime.rule.FactHandle;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class MarkConstraint extends MutableTypeConstraint<MarkContextEntry> implements BetaConstraints<MarkContextEntry>, IndexableConstraint, IntervalProviderConstraint  {

    protected final Declaration[] declarations;
    private final Pattern pattern;

    private ConstraintTypeOperator operatorType;

    private Index index;

    private Predicate1<Object>       p1;
    private Predicate2<Object, Object>    p2;
    private Predicate3<Object, Object, Object> p3;
    private Predicate4<Object, Object, Object, Object> p4;

    private int pIndex;

    public MarkConstraint(Declaration[] declarations, Pattern pattern) {
        this.declarations = declarations;
        this.pattern      = pattern;
    }

    @Override
    public Declaration[] getRequiredDeclarations() {
        return declarations;
    }

    @Override
    public void replaceDeclaration(Declaration oldDecl, Declaration newDecl) {

    }

    public Pattern getPattern() {
        return pattern;
    }

    public int getPIndex() {
        return pIndex;
    }

    public <A> void setPredicate(Predicate1<A> p1) {
        this.p1 = (Predicate1<Object>) p1;
        pIndex = 1;
    }

    public <A, B> void setPredicate(Predicate2<A, B> p2) {
        this.p2 = (Predicate2<Object, Object>) p2;
        pIndex = 2;
    }

    public <A, B, C> void setPredicate(Predicate3<A, B, C> p3) {
        this.p3 = (Predicate3<Object, Object, Object>) p3;
        pIndex = 3;
    }

    public <A, B, C, D> void setPredicate(Predicate4<A, B, C, D> p4) {
        this.p4 = (Predicate4<Object, Object, Object, Object>) p4;
        pIndex = 4;
    }

    @Override
    public MarkConstraint clone() {
        Declaration[] clonedDeclrs = Arrays.stream(declarations).map(d -> d.clone()).collect(Collectors.toList()).toArray(new Declaration[0]);
        MarkConstraint clone = new MarkConstraint(clonedDeclrs, pattern);
        clone.setType(getType());
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

    @Override
    public boolean isTemporal() {
        return false;
    }

    @Override
    public MarkContextEntry createContext() {
        return new MarkContextEntry();
    }

    @Override
    public void updateFromTuple(MarkContextEntry context, ReteEvaluator reteEvaluator, Tuple tuple) {
        context.tp = tuple;
    }

    @Override
    public void updateFromFactHandle(MarkContextEntry context, ReteEvaluator reteEvaluator, FactHandle handle) {
        context.fh = handle;
    }

    @Override
    public boolean isAllowed(FactHandle handle, ValueResolver valueResolver) {
        return p1.test(handle.getObject());
    }

    @Override
    public boolean isAllowedCachedLeft(MarkContextEntry context, FactHandle h) {
        return isAllowed(context.tp, h);
    }

    @Override
    public boolean isAllowedCachedRight(BaseTuple t, MarkContextEntry context) {
        return isAllowed(t, context.fh);
    }

    public boolean isAllowed(BaseTuple t, FactHandle h) {
        switch (pIndex) {
            case 2: {
                return p2.test(t.getFactHandle().getObject(), h.getObject());
            } case 3: {
                return p3.test(t.getParent().getFactHandle().getObject(),
                               t.getFactHandle().getObject(),
                               h.getObject());
            } case 4: {
                BaseTuple    v2 = t.getParent();
                return p4.test(v2.getParent(), v2, t, h.getObject());
            } default:
                throw new RuntimeException("No matching predicate on index: " + pIndex);
        }
    }

    @Override
    public BetaConstraint[] getConstraints() {
        return new BetaConstraint[] {this};
    }

    @Override
    public BetaConstraints getOriginalConstraint() {
        return this;
    }

    @Override
    public boolean isIndexed() {
        return p2 != null;
    }

    @Override
    public int getIndexCount() {
        return 0;
    }

    @Override
    public boolean isEmpty() {
        return false;
    }

    @Override
    public BetaMemory createBetaMemory(RuleBaseConfiguration config, short nodeType) {

        if (config.getCompositeKeyDepth() < 1) {
            return new BetaMemory( config.isSequential() ? null : new TupleList(),
                                   new TupleList(),
                                   createContext(),
                                   nodeType );
        }

        IndexSpec indexSpec = new IndexSpec(nodeType, new BetaConstraint[] {this}, config);
        return new BetaMemory( createLeftMemory(config, indexSpec),
                               createRightMemory(config, indexSpec),
                               createContext(),
                               nodeType );
    }

    private static TupleMemory createRightMemory(RuleBaseConfiguration config, IndexSpec indexSpec) {
        if ( !config.isIndexRightBetaMemory() || !indexSpec.getConstraintType().isIndexable() || indexSpec.getIndexes().length == 0 ) {
            return new TupleList();
        }

        if (indexSpec.getConstraintType() == ConstraintTypeOperator.EQUAL) {
            return IndexMemory.createEqualityMemory(indexSpec, false);
        }

        if (indexSpec.getConstraintType().isComparison()) {
            return IndexMemory.createComparisonMemory(indexSpec, false);
        }

        return new TupleList();
    }

    private static TupleMemory createLeftMemory(RuleBaseConfiguration config, IndexSpec indexSpec) {
        if (config.isSequential()) {
            return null;
        }
        if ( !config.isIndexLeftBetaMemory() || !indexSpec.getConstraintType().isIndexable() || indexSpec.getIndexes().length == 0 ) {
            return new TupleList();
        }

        if (indexSpec.getConstraintType() == ConstraintTypeOperator.EQUAL) {
            return IndexMemory.createEqualityMemory(indexSpec, true);
        }

        if (indexSpec.getConstraintType().isComparison()) {
            return IndexMemory.createComparisonMemory(indexSpec, true);
        }

        return new TupleList();
    }

    @Override
    public void resetTuple(MarkContextEntry context) {
        context.tp = null;
    }

    @Override
    public void resetFactHandle(MarkContextEntry context) {
        context.fh = null;
    }

    @Override
    public void init(BuildContext context, short betaNodeType) {

    }

    @Override
    public void initIndexes(int depth, short betaNodeType, RuleBaseConfiguration config) {
        throw new UnsupportedOperationException();
    }

    @Override
    public MutableTypeConstraint cloneIfInUse() {
        return super.cloneIfInUse();
    }



    @Override
    public boolean isLeftUpdateOptimizationAllowed() {
        return false;
    }

    @Override
    public void registerEvaluationContext(BuildContext buildContext) {

    }

    @Override
    public BitMask getListenedPropertyMask(Pattern pattern, ObjectType modifiedType, List settableProperties) {
        return null;
    }

    @Override
    public boolean isUnification() {
        return false;
    }

    @Override
    public boolean isIndexable(short nodeType, KieBaseConfiguration config) {
        return false;
    }

    @Override
    public ConstraintTypeOperator getConstraintType() {
        return operatorType;
    }

    public void setConstraintTypeOperator(ConstraintTypeOperator operatorType) {
        this.operatorType = operatorType;
    }

    @Override
    public FieldValue getField() {
        return null;
    }

    @Override
    public FieldIndex getFieldIndex() {
        return null;
    }

    @Override
    public ReadAccessor getFieldExtractor() {
        return null;
    }

    @Override
    public TupleValueExtractor getIndexExtractor() {
        return null;
    }

    @Override
    public Interval getInterval() {
        throw new UnsupportedOperationException();
    }

    @Override
    public void writeExternal(ObjectOutput out) throws IOException {

    }

    @Override
    public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {

    }

    public static class MarkContextEntry {
        public Tuple      tp;
        public FactHandle fh;
    }

    public static class Index { // p1.age + 1 ==  p2.age
        private IntFunction1<Object>                         hash1;
        private IntFunction2<Object, Object>                 hash2;
        private IntFunction3<Object, Object, Object>         hash3;
        private IntFunction4<Object, Object, Object, Object> hash4;

        private Function1<Object, Object>                         equals1;
        private Function2<Object, Object, Object>                 equals2;
        private Function3<Object, Object, Object, Object>         equals3;
        private Function4<Object, Object, Object, Object, Object> equals4;

        public IntFunction1<Object> getHash1() {
            return hash1;
        }

        public void setHash1(IntFunction1<Object> hash1) {
            this.hash1 = hash1;
        }

        public IntFunction2<Object, Object> getHash2() {
            return hash2;
        }

        public void setHash2(IntFunction2<Object, Object> hash2) {
            this.hash2 = hash2;
        }

        public IntFunction3<Object, Object, Object> getHash3() {
            return hash3;
        }

        public void setHash3(IntFunction3<Object, Object, Object> hash3) {
            this.hash3 = hash3;
        }

        public IntFunction4<Object, Object, Object, Object> getHash4() {
            return hash4;
        }

        public void setHash4(IntFunction4<Object, Object, Object, Object> hash4) {
            this.hash4 = hash4;
        }

        public Function1<Object, Object> getEquals1() {
            return equals1;
        }

        public void setEquals1(Function1<Object, Object> equals1) {
            this.equals1 = equals1;
        }

        public Function2<Object, Object, Object> getEquals2() {
            return equals2;
        }

        public void setEquals2(Function2<Object, Object, Object> equals2) {
            this.equals2 = equals2;
        }

        public Function3<Object, Object, Object, Object> getEquals3() {
            return equals3;
        }

        public void setEquals3(Function3<Object, Object, Object, Object> equals3) {
            this.equals3 = equals3;
        }

        public Function4<Object, Object, Object, Object, Object> getEquals4() {
            return equals4;
        }

        public void setEquals4(Function4<Object, Object, Object, Object, Object> equals4) {
            this.equals4 = equals4;
        }
    }
}
