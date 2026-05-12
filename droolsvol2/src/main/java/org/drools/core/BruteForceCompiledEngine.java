package org.drools.core;

import org.drools.api.data.DataSource;
import org.drools.api.data.ObjectHandle;
import org.drools.core.RuleBuilder.RuleDescriptor;
import org.drools.core.RuleBuilder.ScopeDescriptor;
import org.drools.core.function.Consumer2;
import org.drools.core.function.Consumer3;
import org.drools.core.function.Function1;
import org.drools.core.function.Predicate2;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Brute-force compiled engine — explicitly temporary.
 *
 * Wires rules by reading RuleDescriptor sources/filters/head directly rather than
 * traversing the Rete topology. Written to keep tests green while the real
 * incremental Rete engine is built. Will be replaced and discarded.
 *
 * Created by BruteForceEngine.compile().
 */
public class BruteForceCompiledEngine<CTX> implements CompiledEngine<CTX> {

    private final RuleDescriptor<CTX>[] descriptors;
    private final EntryPointNode rete;

    @SuppressWarnings("unchecked")
    BruteForceCompiledEngine(UnitDescriptor<CTX> descriptor, EntryPointNode rete) {
        this.descriptors = descriptor.getRules().toArray(new RuleDescriptor[0]);
        this.rete = rete;
    }

    @Override
    @SuppressWarnings({"unchecked", "rawtypes"})
    public UnitInstance<CTX> createUnit(CTX ctx) {
        UnitInstance<CTX> unit = new UnitInstance<>(ctx);
        Router<CTX> router = new Router<>(countSlots(descriptors));
        router.addContext(unit);

        List<DataSource<?>> wired = new ArrayList<>();
        for (RuleDescriptor<CTX> desc : descriptors) {
            List<Function1<CTX, DataSource<?>>> sources = desc.getSources();
            for (int i = 0; i < sources.size(); i++) {
                DataSource<?> ds = sources.get(i).apply(ctx);
                if (!containsByIdentity(wired, ds)) {
                    wired.add(ds);
                    ((PropagatingDataStore) ds).subscribe(new ContextRouterAdapter<>(i, router));
                }
            }
        }

        for (RuleDescriptor<CTX> desc : descriptors) {
            wireHead(unit, router, desc);
        }

        return unit;
    }

    @Override
    public void disposeUnit(UnitInstance<CTX> unit) {
        // brute-force: DataStore subscriptions not tracked for cleanup
    }

    // --- Wiring ---

    @SuppressWarnings({"unchecked", "rawtypes"})
    private void wireHead(UnitInstance<CTX> unit, Router<CTX> router, RuleDescriptor<CTX> desc) {
        List<Function1<CTX, DataSource<?>>> sources = desc.getSources();
        List<Object> filters = desc.getFilters();
        Object rawHead = desc.getHead();
        boolean immediate = desc.isImmediate();

        if (sources.isEmpty()) {
            throw new UnsupportedOperationException("Rules with no from() not yet supported");
        }

        List<ScopeDescriptor<CTX>> negations = desc.getNegations();
        List<ScopeDescriptor<CTX>> existences = desc.getExistences();

        if (sources.size() == 1) {
            Consumer2<Context<CTX>, Object> consumer = (Consumer2<Context<CTX>, Object>) rawHead;
            UnitProcessor<CTX, Object> action = buildAction(consumer, immediate);
            UnitProcessor<CTX, Object> scoped = scopeGuard(action, negations, existences);
            subscribeWithFilter(router, 0, scoped, filters.isEmpty() ? null : filters.get(0));

        } else if (sources.size() == 2) {
            Consumer3<Context<CTX>, Object, Object> consumer = (Consumer3<Context<CTX>, Object, Object>) rawHead;
            JoinNode joinNode = findJoinNode(desc.getRule(), rete);

            Object filter0 = filters.size() > 0 ? filters.get(0) : null;
            Object filter1 = filters.size() > 1 ? filters.get(1) : null;

            Consumer3<Context<CTX>, Object, Object> scopedConsumer = negations.isEmpty() && existences.isEmpty()
                    ? consumer
                    : (c, leftFact, rightFact) -> {
                        if (scopesAllow2(c, negations, existences, leftFact, rightFact))
                            consumer.accept(c, leftFact, rightFact);
                    };

            Object inletFilter1;
            Consumer3<Context<CTX>, Object, Object> finalConsumer;
            if (filter1 != null && isMultiFactFilter(filter1)) {
                final Object postJoinFilter = filter1;
                finalConsumer = (c, left, right) -> {
                    if (invokePredicate(postJoinFilter, c, new Object[]{left, right}))
                        scopedConsumer.accept(c, left, right);
                };
                inletFilter1 = null;
            } else {
                finalConsumer = scopedConsumer;
                inletFilter1 = filter1;
            }

            subscribeWithFilter(router, 0, new JoinLeftInlet<>(joinNode, finalConsumer, immediate), filter0);
            subscribeWithFilter(router, 1, new JoinRightInlet<>(joinNode, finalConsumer, immediate), inletFilter1);

        } else {
            for (int slot = 0; slot < sources.size(); slot++) {
                final int triggerSlot = slot;
                UnitProcessor<CTX, Object> proc = new UnitProcessor<CTX, Object>() {
                    public void add(UnitInstance<CTX> u, ObjectHandle<Object> h) {
                        evaluateAllCombinations(u.getContext(), sources, filters, rawHead, negations, existences,
                                immediate, u.getAgenda(), triggerSlot, h.getObject());
                    }
                    public void update(UnitInstance<CTX> u, ObjectHandle<Object> h) {
                        evaluateAllCombinations(u.getContext(), sources, filters, rawHead, negations, existences,
                                immediate, u.getAgenda(), triggerSlot, h.getObject());
                    }
                    public void remove(UnitInstance<CTX> u, ObjectHandle<Object> h) {}
                };
                router.subscribe(slot, proc);
            }
        }
    }

    private JoinNode findJoinNode(org.drools.base.definitions.rule.impl.RuleImpl rule, EntryPointNode rete) {
        return findJoinNodeIn(rete, rule);
    }

    private JoinNode findJoinNodeIn(BaseNode node, org.drools.base.definitions.rule.impl.RuleImpl rule) {
        if (node instanceof JoinNode && node.isAssociatedWith(rule)) return (JoinNode) node;
        for (BaseNode out : node.getOutputs()) {
            JoinNode found = findJoinNodeIn(out, rule);
            if (found != null) return found;
        }
        return null;
    }

    @SuppressWarnings("unchecked")
    private void evaluateAllCombinations(Context<CTX> ctx,
            List<Function1<CTX, DataSource<?>>> sources,
            List<Object> filters,
            Object rawConsumer,
            List<ScopeDescriptor<CTX>> negations,
            List<ScopeDescriptor<CTX>> existences,
            boolean immediate,
            Agenda agenda,
            int triggerSlot,
            Object triggerFact) {
        List<Object[]> combinations = new ArrayList<>();
        combinations.add(new Object[0]);

        for (int i = 0; i < sources.size(); i++) {
            List<Object> items;
            if (i == triggerSlot) {
                items = java.util.Collections.singletonList(triggerFact);
            } else {
                @SuppressWarnings("rawtypes")
                List rawList = sources.get(i).apply(ctx.context()).asList();
                items = rawList;
            }
            Object filterPred = i < filters.size() ? filters.get(i) : null;
            List<Object[]> next = new ArrayList<>();
            for (Object item : items) {
                for (Object[] combo : combinations) {
                    Object[] extended = Arrays.copyOf(combo, combo.length + 1);
                    extended[combo.length] = item;
                    if (filterPred == null || invokePredicate(filterPred, ctx, extended)) next.add(extended);
                }
            }
            combinations = next;
            if (combinations.isEmpty()) return;
        }

        Method m = Arrays.stream(rawConsumer.getClass().getMethods())
                .filter(me -> me.getName().equals("accept") && !me.isSynthetic())
                .findFirst().orElseThrow();

        for (Object[] combo : combinations) {
            boolean allowed = true;
            for (ScopeDescriptor<CTX> neg : negations)
                if (scopeHasMatch(neg, ctx, neg.globalEval ? new Object[0] : combo)) { allowed = false; break; }
            if (!allowed) continue;
            for (ScopeDescriptor<CTX> ex : existences)
                if (!scopeHasMatch(ex, ctx, ex.globalEval ? new Object[0] : combo)) { allowed = false; break; }
            if (!allowed) continue;

            Object[] args = new Object[combo.length + 1];
            args[0] = ctx;
            System.arraycopy(combo, 0, args, 1, combo.length);
            final Object[] finalArgs = args;
            try {
                if (immediate) m.invoke(rawConsumer, finalArgs);
                else agenda.enqueue(() -> { try { m.invoke(rawConsumer, finalArgs); } catch (Exception e) { throw new RuntimeException(e); } });
            } catch (Exception e) {
                throw new RuntimeException("Consumer invocation failed", e);
            }
        }
    }

    private boolean scopesAllow2(Context<CTX> c,
            List<ScopeDescriptor<CTX>> negations,
            List<ScopeDescriptor<CTX>> existences,
            Object leftFact, Object rightFact) {
        Object[] outerFacts = new Object[]{ leftFact, rightFact };
        for (ScopeDescriptor<CTX> neg : negations)
            if (scopeHasMatch(neg, c, neg.globalEval ? new Object[0] : outerFacts)) return false;
        for (ScopeDescriptor<CTX> ex : existences)
            if (!scopeHasMatch(ex, c, ex.globalEval ? new Object[0] : outerFacts)) return false;
        return true;
    }

    @SuppressWarnings("unchecked")
    private UnitProcessor<CTX, Object> scopeGuard(
            UnitProcessor<CTX, Object> delegate,
            List<ScopeDescriptor<CTX>> negations,
            List<ScopeDescriptor<CTX>> existences) {
        if (negations.isEmpty() && existences.isEmpty()) return delegate;
        return new UnitProcessor<CTX, Object>() {
            public void add(UnitInstance<CTX> unit, ObjectHandle<Object> h) {
                if (scopesAllow(unit.getContext(), h.getObject())) delegate.add(unit, h);
            }
            public void update(UnitInstance<CTX> unit, ObjectHandle<Object> h) {
                if (scopesAllow(unit.getContext(), h.getObject())) delegate.update(unit, h);
            }
            public void remove(UnitInstance<CTX> unit, ObjectHandle<Object> h) {
                delegate.remove(unit, h);
            }
            private boolean scopesAllow(Context<CTX> c, Object fact) {
                Object[] outerFacts = new Object[]{ fact };
                for (ScopeDescriptor<CTX> neg : negations)
                    if (scopeHasMatch(neg, c, neg.globalEval ? new Object[0] : outerFacts)) return false;
                for (ScopeDescriptor<CTX> ex : existences)
                    if (!scopeHasMatch(ex, c, ex.globalEval ? new Object[0] : outerFacts)) return false;
                return true;
            }
        };
    }

    @SuppressWarnings("unchecked")
    private boolean scopeHasMatch(ScopeDescriptor<CTX> scope, Context<CTX> ctx, Object[] outerFacts) {
        List<Object[]> combinations = new ArrayList<>();
        combinations.add(outerFacts);
        for (int i = 0; i < scope.sources.size(); i++) {
            DataSource<?> ds = scope.sources.get(i).apply(ctx.context());
            Object filterPred = scope.filters.get(i);
            List<Object[]> next = new ArrayList<>();
            for (Object item : ds.asList()) {
                for (Object[] outer : combinations) {
                    Object[] combined = Arrays.copyOf(outer, outer.length + 1);
                    combined[outer.length] = item;
                    if (filterPred == null || invokePredicate(filterPred, ctx, combined)) next.add(combined);
                }
            }
            combinations = next;
            if (combinations.isEmpty()) return false;
        }
        return !combinations.isEmpty();
    }

    private static boolean isMultiFactFilter(Object filter) {
        return Arrays.stream(filter.getClass().getMethods())
                .filter(m -> m.getName().equals("test") && !m.isSynthetic())
                .findFirst()
                .map(m -> m.getParameterCount() > 2)
                .orElse(false);
    }

    private boolean invokePredicate(Object pred, Context<CTX> ctx, Object[] facts) {
        try {
            Method m = Arrays.stream(pred.getClass().getMethods())
                    .filter(me -> me.getName().equals("test") && !me.isSynthetic())
                    .findFirst().orElseThrow();
            Object[] args;
            if (m.getParameterCount() == facts.length + 1) {
                args = new Object[facts.length + 1];
                args[0] = ctx;
                System.arraycopy(facts, 0, args, 1, facts.length);
            } else if (m.getParameterCount() == facts.length) {
                args = facts;
            } else {
                throw new IllegalArgumentException("wrong number of arguments: " +
                        m.getParameterCount() + " expected: " + (facts.length + 1));
            }
            return (Boolean) m.invoke(pred, args);
        } catch (Exception e) {
            throw new RuntimeException("Scope predicate invocation failed", e);
        }
    }

    private UnitProcessor<CTX, Object> buildAction(Consumer2<Context<CTX>, Object> consumer, boolean immediate) {
        if (immediate) return new Action1<>(consumer);
        return new UnitProcessor<CTX, Object>() {
            public void add(UnitInstance<CTX> unit, ObjectHandle<Object> h) {
                unit.getAgenda().enqueue(() -> consumer.accept(unit.getContext(), h.getObject()));
            }
            public void update(UnitInstance<CTX> unit, ObjectHandle<Object> h) {
                unit.getAgenda().enqueue(() -> consumer.accept(unit.getContext(), h.getObject()));
            }
            public void remove(UnitInstance<CTX> unit, ObjectHandle<Object> h) {}
        };
    }

    @SuppressWarnings("unchecked")
    private void subscribeWithFilter(Router<CTX> router, int slot, UnitProcessor<CTX, Object> processor, Object filter) {
        if (filter != null) {
            Predicate2<Context<CTX>, Object> pred = (Predicate2<Context<CTX>, Object>) filter;
            Filter1UnitProcessor<CTX, Object> f1 = new Filter1UnitProcessor<>(pred);
            f1.subscribe(processor);
            router.subscribe(slot, f1);
        } else {
            router.subscribe(slot, processor);
        }
    }

    private static int countSlots(RuleDescriptor<?>[] descriptors) {
        int max = 0;
        for (RuleDescriptor<?> d : descriptors) max = Math.max(max, d.getSources().size());
        return Math.max(max, 1);
    }

    private static boolean containsByIdentity(List<?> list, Object item) {
        for (Object o : list) if (o == item) return true;
        return false;
    }
}
