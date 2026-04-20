package org.drools.core;

import io.quarkiverse.permuplate.Permute;
import io.quarkiverse.permuplate.PermuteDeclr;
import io.quarkiverse.permuplate.PermuteMethod;
import io.quarkiverse.permuplate.PermuteReturn;
import io.quarkiverse.permuplate.PermuteTypeParam;

import org.drools.api.data.DataSource;
import org.drools.base.base.ClassObjectType;
import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.base.rule.GroupElement;
import org.drools.base.rule.GroupElementFactory;
import org.drools.base.rule.Pattern;
import org.drools.core.RuleExtendsPoint.RuleExtendsPoint2;
import org.drools.core.RuleExtendsPoint.RuleExtendsPoint3;
import org.drools.core.RuleExtendsPoint.RuleExtendsPoint4;
import org.drools.core.RuleExtendsPoint.RuleExtendsPoint5;
import org.drools.core.RuleExtendsPoint.RuleExtendsPoint6;
import org.drools.core.RuleOOPathBuilder.Path2;
import org.drools.core.RuleOOPathBuilder.Path3;
import org.drools.core.RuleOOPathBuilder.Path4;
import org.drools.core.RuleOOPathBuilder.Path5;
import org.drools.core.RuleOOPathBuilder.Path6;
import org.drools.core.function.*;
import org.drools.core.function.BaseTuple.Tuple1;
import org.drools.core.function.BaseTuple.Tuple2;
import org.drools.core.function.BaseTuple.Tuple3;
import org.drools.core.function.BaseTuple.Tuple4;
import org.drools.core.function.BaseTuple.Tuple5;
import org.drools.core.function.BaseTuple.Tuple6;
import org.kie.api.definition.rule.Rule;

import java.lang.invoke.SerializedLambda;
import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.IdentityHashMap;

public class RuleBuilder<CTX> {

    public RuleBuilder() {
    }

    private String packageName;
    private Rule rule;

    public ParametersFirst<Void, CTX> rule(String ruleName) {
        rule = new RuleImpl(ruleName);
        ((RuleImpl) rule).setLhs(GroupElementFactory.newAndInstance());
        return new ParametersFirst<>(null, rule);
    }

    public <T> From1First<Void, CTX, T> from(Function1<CTX, DataSource<T>> f) {
        return new From1First<>(null, rule);
    }

    public <T> From1First<Void, CTX, T> from(DataSource<T> fromT) {
        return new From1First<>(null, rule);
    }

    // -------------------------------------------------------------------------
    // Base
    // -------------------------------------------------------------------------

    /** Carries the evaluation-ready state for one rule: ordered source refs and the consequence. */
    public static class RuleDescriptor<CTX> {
        private final RuleImpl rule;
        private final List<Function1<CTX, DataSource<?>>> sources;
        private final Object consequence;

        @SuppressWarnings("unchecked")
        RuleDescriptor(Rule rule) {
            this.rule = (RuleImpl) rule;
            Object[] state = BaseRuleBuilder.RULE_STATE.getOrDefault(rule, new Object[]{new ArrayList<>(), null});
            this.sources = (List<Function1<CTX, DataSource<?>>>) state[0];
            this.consequence = state[1];
        }

        public RuleImpl getRule()                               { return rule; }
        public List<Function1<CTX, DataSource<?>>> getSources()  { return sources; }
        public Object getConsequence()                          { return consequence; }
    }

    public static class BaseRuleBuilder<END> {
        private END end;
        protected Rule rule;

        // Keyed by RuleImpl identity (==); cleared once descriptor() is called
        @SuppressWarnings("rawtypes")
        static final IdentityHashMap<Rule, Object[]> RULE_STATE = new IdentityHashMap<>();

        public BaseRuleBuilder(END end, Rule rule) {
            this.end = end;
            this.rule = rule;
        }

        public Rule build() {
            return rule;
        }

        public END end() {
            return end;
        }

        @SuppressWarnings({"unchecked", "rawtypes"})
        protected void storePatternSource(Function1 f) {
            Object[] state = RULE_STATE.computeIfAbsent(rule, k -> new Object[]{new ArrayList<>(), null});
            ((List) state[0]).add(f);
        }

        protected void storeConsequence(Object c) {
            Object[] state = RULE_STATE.computeIfAbsent(rule, k -> new Object[]{new ArrayList<>(), null});
            state[1] = c;
        }

        public <CTX> RuleDescriptor<CTX> descriptor() {
            RuleDescriptor<CTX> desc = new RuleDescriptor<>(rule);
            RULE_STATE.remove(rule);
            return desc;
        }

        protected void addPattern(Class<?> cls) {
            GroupElement lhs = ((RuleImpl) rule).getBody();
            lhs.addChild(new Pattern(lhs.getNestedElements().size(), new ClassObjectType(cls)));
        }

        @SuppressWarnings("unchecked")
        protected static <CTX, T> Class<T> extractElementType(Function1<CTX, DataSource<T>> f) {
            try {
                Method writeReplace = f.getClass().getDeclaredMethod("writeReplace");
                writeReplace.setAccessible(true);
                SerializedLambda sl = (SerializedLambda) writeReplace.invoke(f);
                Class<?> declaring = Class.forName(sl.getImplClass().replace('/', '.'));
                Method m = declaring.getMethod(sl.getImplMethodName());
                ParameterizedType returnType = (ParameterizedType) m.getGenericReturnType();
                return (Class<T>) returnType.getActualTypeArguments()[0];
            } catch (Exception e) {
                throw new RuntimeException("from()/join() requires a method reference (e.g. CTX::persons)", e);
            }
        }
    }

    public static class Parameter {
        private final String name;
        private final String type;
        public Parameter(String name, String type) { this.name = name; this.type = type; }
        public String name() { return name; }
        public String type() { return type; }
    }

    public static class ArgList {
        private List<Object> list = new ArrayList<>();

        public Object get(int index) {
            return list.get(index);
        }
    }

    public static class ArgMap {
        private Map<String, Object> map = new HashMap<>();

        public Object get(String index) {
            return map.get(index);
        }
    }

    // -------------------------------------------------------------------------
    // Parameters
    // -------------------------------------------------------------------------

    public static class ParametersFirst<END, CTX> extends BaseRuleBuilder<END> {
        private List<Parameter> listParams;
        private List<Parameter> mapParams;
        private Class params;

        public ParametersFirst(END end, Rule rule) {
            super(end, rule);
        }

        public <T> ParametersSecond<END, CTX, ArgList> param(String name, T... type) {
            return list().param(name, type.getClass().getComponentType().getName());
        }

        public ParametersSecond<END, CTX, ArgList> list() {
            listParams = new ArrayList<>();
            return new ParametersSecond<>(end(), listParams, rule);
        }

        public ParametersSecond<END, CTX, ArgMap> map() {
            mapParams = new ArrayList<>();
            return new ParametersSecond<>(end(), mapParams, rule);
        }

        public <B> From1First<END, CTX, B> params(B... cls) {
            params = cls.getClass().getComponentType();
            return new From1First<>(end(), rule);
        }

        public <T> From1First<END, CTX, T> from(Function1<CTX, DataSource<T>> f) {
            addPattern(extractElementType(f));
            storePatternSource(f);
            return new From1First<>(end(), rule);
        }

        public <T> From1First<Void, CTX, T> from(From1First<?, CTX, T> f) {
            return new From1First<>(null, rule);
        }

        public ParametersFirst<END, CTX> ifn(Runnable fn0) {
            return this;
        }

        public void fn(Consumer1<Context<CTX>> fn1) {
        }

        public <B> From1First<END, CTX, B> extendsRule(RuleExtendsPoint2<CTX, B> extension2) {
            return new From1First<>(end(), rule);
        }

        public <B, C> Join2First<END, CTX, B, C> extendsRule(RuleExtendsPoint3<CTX, B, C> extension3) {
            return new Join2First<>(end(), rule);
        }

        public <B, C, D> Join3First<END, CTX, B, C, D> extendsRule(RuleExtendsPoint4<CTX, B, C, D> extension4) {
            return new Join3First<>(end(), rule);
        }

        public <B, C, D, E> Join4First<END, CTX, B, C, D, E> extendsRule(RuleExtendsPoint5<CTX, B, C, D, E> extension5) {
            return new Join4First<>(end(), rule);
        }
    }

    public static class ParametersSecond<END, CTX, B> extends BaseRuleBuilder<END> {
        private List<Parameter> parameters;

        public ParametersSecond(END end, List<Parameter> list, Rule rule) {
            super(end, rule);
            parameters = list;
        }

        public <T> ParametersSecond<END, CTX, B> param(String name, T... cls) {
            return param(name, cls.getClass().getComponentType().getName());
        }

        public ParametersSecond<END, CTX, B> param(String name, String type) {
            parameters.add(new Parameter(name, type));
            return this;
        }

        public <C> Join2First<Void, CTX, B, C> join(From1First<END, CTX, C> fromC) {
            return new Join2First<>(null, rule);
        }

        public <C> Join2First<Void, CTX, B, C> join(Function1<CTX, DataSource<C>> fromC) {
            return new Join2First<>(null, rule);
        }
    }

    // -------------------------------------------------------------------------
    // From1First
    // -------------------------------------------------------------------------

    public static class From1First<END, CTX, B> extends BaseRuleBuilder<END> {

        public From1First(END end, Rule rule) {
            super(end, rule);
        }

        public RuleExtendsPoint2<CTX, B> extensionPoint() {
            return new RuleExtendsPoint2<>(rule);
        }

        public <T extends B> From1First<END, CTX, T> type(Class<T>... cls) {
            return new From1First<>(end(), rule);
        }

        public From1First<END, CTX, B> filter(Predicate2<Context<CTX>, B> prd2) {
            return this;
        }

        public <C> Join2First<END, CTX, B, C> join(From1First<?, CTX, C> fromC) {
            return new Join2First<>(end(), rule);
        }

        public <C> Join2First<END, CTX, B, C> join(Function1<CTX, DataSource<C>> fromC) {
            addPattern(extractElementType(fromC));
            storePatternSource(fromC);
            return new Join2First<>(end(), rule);
        }

        public <C> Join2First<END, CTX, B, C> not(From1First<Void, CTX, C> fromC) {
            return null;
        }

        public <C> Join2First<END, CTX, B, C> not(Function1<CTX, DataSource<C>> fromC) {
            return null;
        }

        public <C, D> Join3First<END, CTX, B, C, D> join(Join2Second<Void, CTX, C, D> fromCD) {
            return null;
        }

        public <C, D, E> Join4First<END, CTX, B, C, D, E> join(Join3First<Void, CTX, C, D, E> fromCDE) {
            return null;
        }

        public From1First<END, CTX, B> ifn(Consumer2<Context<CTX>, B> fn2) {
            storeConsequence(fn2);
            return this;
        }

        public void fn(Consumer2<Context<CTX>, B> fn2) {
        }

        <PB, PC, PD, PE, PF> Path6<Join2First<END, CTX, B, Tuple6<B, PB, PC, PD, PE, PF>>, Tuple6<B, PB, PC, PD, PE, PF>, B, PB, PC, PD, PE, PF> path6() {
            return new Path6<>(null, null, null);
        }

        <PB, PC, PD, PE> Path4<Join2First<END, CTX, B, Tuple5<B, PB, PC, PD, PE>>, Tuple5<B, PB, PC, PD, PE>, PB, PC, PD, PE> path5(
                Function2<PathContext<Tuple5<B, PB, PC, PD, PE>>, B, ?> fn2,
                Predicate2<PathContext<Tuple5<B, PB, PC, PD, PE>>, PB> flt2) {
            Path5<Join2First<END, CTX, B, Tuple5<B, PB, PC, PD, PE>>, Tuple5<B, PB, PC, PD, PE>, B, PB, PC, PD, PE> path5 = new Path5<>(null, null, null);
            return path5.path(fn2, flt2);
        }

        <PB, PC, PD> Path4<Join2First<END, CTX, B, Tuple4<B, PB, PC, PD>>, Tuple4<B, PB, PC, PD>, B, PB, PC, PD> path4() {
            return new Path4<>(null, null, null);
        }

        <PB, PC> Path3<Join2First<END, CTX, B, Tuple3<B, PB, PC>>, Tuple2<B, PB>, B, PB, PC> path3() {
            return new Path3<>(null, null, null);
        }

        <PB> Path2<Join2First<END, CTX, B, Tuple2<B, PB>>, Tuple1<B>, B, PB> path2() {
            return new Path2<>(null, null, null);
        }
    }

    // -------------------------------------------------------------------------
    // Join2 — templates generating Join3..Join10
    // -------------------------------------------------------------------------

    @Permute(varName = "i", from = 3, to = 10, className = "Join${i}First", inline = true, keepTemplate = true)
    public static class Join2First<END, CTX, B,
            @PermuteTypeParam(varName = "j", from = "3", to = "${i+1}", name = "${alpha(j)}") C>
            extends Join2Second<END, CTX, B, C> {

        public Join2First(END end, Rule rule) {
            super(end, rule);
        }

        @PermuteReturn(className = "Join${i}First", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha')")
        public Join2First<END, CTX, B, C> filter(
                @PermuteDeclr(type = "Predicate2<Context<CTX>, ${alpha(i+1)}>")
                Predicate2<Context<CTX>, C> predicate2) {
            return this;
        }

        // Predicate${i+1} only exists up to Predicate10; omit multi-fact filter for Join10First
        @PermuteReturn(className = "Join${i}First", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha')", when = "i + 1 <= 10")
        public Join2First<END, CTX, B, C> filter(
                @PermuteDeclr(type = "Predicate${i+1}<Context<CTX>, ${typeArgList(2, i+1, 'alpha')}>")
                Predicate3<Context<CTX>, B, C> predicate3) {
            return this;
        }

        @PermuteReturn(className = "Join${i}First", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha')")
        public Join2First<END, CTX, B, C> index() {
            return this;
        }

        @PermuteReturn(className = "Join${i}First", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha')")
        public <V1, V2> Join2First<END, CTX, B, C> filter(Variable<V1> v1, Variable<V2> v2,
                                                          Predicate3<Context<CTX>, V1, V2> predicate3) {
            return this;
        }

        @PermuteReturn(className = "Join${i}First", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha')")
        public <V1, V2, V3> Join2First<END, CTX, B, C> filter(Variable<V1> v1, Variable<V2> v2, Variable<V2> v3,
                                                              Predicate4<Context<CTX>, V1, V2, V3> predicate4) {
            return this;
        }

        @PermuteReturn(className = "Join${i}First", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha')")
        public Join2First<END, CTX, B, C> var(Variable var) {
            return this;
        }
    }

    @Permute(varName = "i", from = 3, to = 10, className = "Join${i}Second", inline = true, keepTemplate = true)
    public static class Join2Second<END, CTX, B,
            @PermuteTypeParam(varName = "j", from = "3", to = "${i+1}", name = "${alpha(j)}") C>
            extends BaseRuleBuilder<END> {

        public Join2Second(END end, Rule rule) {
            super(end, rule);
        }

        @PermuteReturn(className = "RuleExtendsPoint${i+1}", typeArgs = "'CTX, ' + typeArgList(2, i+1, 'alpha')", when = "i + 1 <= 6")
        public RuleExtendsPoint3<CTX, B, C> extensionPoint() {
            return new @PermuteDeclr(type = "RuleExtendsPoint${i+1}") RuleExtendsPoint3<>(rule);
        }

        @PermuteReturn(className = "Join${i}Second", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha')")
        public Join2Second<END, CTX, B, C> not(
                @PermuteDeclr(type = "Function1<CTX, DataSource<${alpha(i+1)}>>", name = "from${alpha(i+1)}")
                Function1<CTX, DataSource<C>> fromC) {
            return this;
        }

        // not() with Not2 — kept on template only; Not2 is arity-2 only
        @PermuteReturn(className = "void", when = "false")
        public Not2<Join2Second<END, CTX, B, C>, CTX, B, C> not() {
            return new Not2<>(this, rule);
        }

        @PermuteReturn(className = "Join${i+1}First", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha') + ', T'", when = "i + 1 <= 10")
        public <T> Join3First<END, CTX, B, C, T> join(From1First<Void, CTX, T> fromT) {
            return new @PermuteDeclr(type = "Join${i+1}First") Join3First<>(end(), rule);
        }

        @PermuteReturn(className = "Join${i+1}First", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha') + ', T'", when = "i + 1 <= 10")
        public <T> Join3First<END, CTX, B, C, T> join(Function1<CTX, DataSource<T>> fromT) {
            addPattern(extractElementType(fromT));
            storePatternSource(fromT);
            return new @PermuteDeclr(type = "Join${i+1}First") Join3First<>(end(), rule);
        }

        // Bilinear join: join a pre-built JoinMFirst; generates overloads for M=2..(10-i).
        // Object placeholders are required so the kept template compiles without T2..Tm declared.
        // @PermuteTypeParam expands <T1> to <T1..Tm> in generated overloads.
        @PermuteMethod(varName = "m", from = 2, to = "${10 - i}")
        @PermuteTypeParam(varName = "j", from = "1", to = "${m}", name = "T${j}")
        @PermuteReturn(className = "Join${i+m}First", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha') + ', ' + typeArgList(1, m, 'T')")
        public <T1> Object join(
                @PermuteDeclr(type = "Join${m}First<?, CTX, ${typeArgList(1, m, 'T')}>")
                Object joinM) {
            return null;
        }

        // Consumer${i+1} only exists up to Consumer10; omit ifn/fn for Join10Second
        @PermuteReturn(className = "Join${i}Second", typeArgs = "'END, CTX, ' + typeArgList(2, i+1, 'alpha')", when = "i + 1 <= 10")
        public Join2Second<END, CTX, B, C> ifn(
                @PermuteDeclr(type = "Consumer${i+1}<Context<CTX>, ${typeArgList(2, i+1, 'alpha')}>",
                        name = "fn${i+1}")
                Consumer3<Context<CTX>, B, C> fn3) {
            storeConsequence(fn3);
            return this;
        }

        // fn() returns BaseRuleBuilder — not in allGeneratedNames, use when to control boundary
        @PermuteReturn(className = "BaseRuleBuilder", typeArgs = "'END'", when = "i + 1 <= 10")
        public BaseRuleBuilder<END> fn(
                @PermuteDeclr(type = "Consumer${i+1}<Context<CTX>, ${typeArgList(2, i+1, 'alpha')}>",
                        name = "fn${i+1}")
                Consumer3<Context<CTX>, B, C> fn3) {
            return this;
        }

        @PermuteReturn(className = "Path2",
                typeArgs = "'Join' + (i+1) + 'First<END, CTX, ' + typeArgList(2, i+1, 'alpha') + ', Tuple2<' + alpha(i+1) + ', PB>>, Tuple2<' + alpha(i+1) + ', PB>, ' + alpha(i+1) + ', PB'",
                when = "i + 1 <= 8")
        <PB> Path2<Join3First<END, CTX, B, C, Tuple2<C, PB>>, Tuple2<C, PB>, C, PB> path2() {
            return new Path2<>(null, null, null);
        }

        @PermuteReturn(className = "Path3",
                typeArgs = "'Join' + (i+1) + 'First<END, CTX, ' + typeArgList(2, i+1, 'alpha') + ', Tuple3<' + alpha(i+1) + ', PB, PC>>, Tuple3<' + alpha(i+1) + ', PB, PC>, ' + alpha(i+1) + ', PB, PC'",
                when = "i + 1 <= 8")
        <PB, PC> Path3<Join3First<END, CTX, B, C, Tuple3<C, PB, PC>>, Tuple3<C, PB, PC>, C, PB, PC> path3() {
            return new Path3<>(null, null, null);
        }

        @PermuteReturn(className = "Path4",
                typeArgs = "'Join' + (i+1) + 'First<END, CTX, ' + typeArgList(2, i+1, 'alpha') + ', Tuple4<' + alpha(i+1) + ', PB, PC, PD>>, Tuple4<' + alpha(i+1) + ', PB, PC, PD>, ' + alpha(i+1) + ', PB, PC, PD'",
                when = "i + 1 <= 8")
        <PB, PC, PD> Path4<Join3First<END, CTX, B, C, Tuple4<C, PB, PC, PD>>, Tuple4<C, PB, PC, PD>, C, PB, PC, PD> path4() {
            return new Path4<>(null, null, null);
        }

        // path5/path6: template-only stubs; @PermuteReturn(when="false") suppresses R1 and removes from generated
        @PermuteReturn(className = "void", when = "false")
        <PB, PC, PD, PE> Path4<Join3First<END, CTX, B, C, Tuple5<C, PB, PC, PD, PE>>, Tuple5<C, PB, PC, PD, PE>, PB, PC, PD, PE> path5(
                Function2<PathContext<Tuple5<C, PB, PC, PD, PE>>, C, ?> fn2,
                Predicate2<PathContext<Tuple5<C, PB, PC, PD, PE>>, PB> flt2) {
            Path5<Join3First<END, CTX, B, C, Tuple5<C, PB, PC, PD, PE>>, Tuple5<C, PB, PC, PD, PE>, C, PB, PC, PD, PE> path5 = new Path5<>(null, null, null);
            return path5.path(fn2, flt2);
        }

        @PermuteReturn(className = "void", when = "false")
        <PB, PC, PD, PE, PF> Path6<Join3First<END, CTX, B, C, Tuple6<C, PB, PC, PD, PE, PF>>, Tuple6<C, PB, PC, PD, PE, PF>, C, PB, PC, PD, PE, PF> path6() {
            return new Path6<>(null, null, null);
        }
    }

    // -------------------------------------------------------------------------
    // Not2 / Group2 — arity-2 only, not templated
    // -------------------------------------------------------------------------

    public static class Not2<END, CTX, B, C> extends Group2<END, CTX, B, C> {
        public Not2(END end, Rule rule) {
            super(end, rule);
        }
    }

    public static class Group2<END, CTX, B, C> extends Join2Second<END, CTX, B, C> {
        public Group2(END end, Rule rule) {
            super(end, rule);
        }
    }
}
