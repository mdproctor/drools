package org.drools.core;

import org.drools.api.data.DataProcessor;
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
 * Vol2 equivalent of WorkingMemory + Agenda.
 * All rule evaluations for a unit happen within one UnitInstance.
 *
 * Uses NodeMemories (array-backed, keyed by node ID) for beta state.
 * JoinLeftInlet / JoinRightInlet are the named concrete DataProcessors
 * attached to their host JoinNode via the Rete topology.
 */
public class UnitInstance<CTX> {

    private final Router<CTX> router;
    private final ContextPojoDS<CTX> context;
    private final Agenda agenda = new Agenda();
    private final NodeMemories nodeMemories = new SimpleNodeMemories();
    private final EntryPointNode rete;

    @SuppressWarnings({"unchecked", "rawtypes"})
    public UnitInstance(CTX ctx, EntryPointNode rete, RuleDescriptor<CTX>... descriptors) {
        this.rete    = rete;
        this.router  = new Router<>(countSlots(descriptors));
        this.context = new ContextPojoDS<>(ctx);
        this.router.addContext(context);

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
            wireHead(desc);
        }
    }

    // --- Data mutation methods that drain the agenda ---

    @SuppressWarnings("unchecked")
    public <T> ObjectHandle<T> add(PropagatingDataStore<T> store, T obj) {
        ObjectHandle<T> h = store.add(obj);
        agenda.drain();
        return h;
    }

    @SuppressWarnings("unchecked")
    public <T> void update(PropagatingDataStore<T> store, ObjectHandle<T> h, T obj) {
        ((ObjectHandleImpl<T>) h).setObject(obj);
        store.update(h, obj);
        agenda.drain();
    }

    public <T> void remove(PropagatingDataStore<T> store, ObjectHandle<T> h) {
        store.remove(h);
        agenda.drain();
    }

    public NodeMemories getNodeMemories() { return nodeMemories; }

    // --- Internal wiring ---

    @SuppressWarnings({"unchecked", "rawtypes"})
    private void wireHead(RuleDescriptor<CTX> desc) {
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
            DataProcessor<CTX, Object> action = buildAction(consumer, immediate);
            DataProcessor<CTX, Object> scoped = scopeGuard(action, negations, existences);
            subscribeWithFilter(0, scoped, filters.isEmpty() ? null : filters.get(0));

        } else if (sources.size() == 2) {
            Consumer3<Context<CTX>, Object, Object> consumer = (Consumer3<Context<CTX>, Object, Object>) rawHead;
            JoinNode joinNode = findJoinNode(desc.getRule());

            Object filter0 = filters.size() > 0 ? filters.get(0) : null;
            Object filter1 = filters.size() > 1 ? filters.get(1) : null;

            // For 2-source rules, wrap the consumer (not the inlets) so both outer facts
            // are available to scope predicates. The consumer receives (ctx, leftFact, rightFact).
            Consumer3<Context<CTX>, Object, Object> scopedConsumer = negations.isEmpty() && existences.isEmpty()
                    ? consumer
                    : (c, leftFact, rightFact) -> {
                        if (scopesAllow2(c, negations, existences, leftFact, rightFact))
                            consumer.accept(c, leftFact, rightFact);
                    };

            subscribeWithFilter(0, new JoinLeftInlet<>(joinNode, nodeMemories, scopedConsumer, immediate, agenda), filter0);
            subscribeWithFilter(1, new JoinRightInlet<>(joinNode, nodeMemories, scopedConsumer, immediate, agenda), filter1);

        } else {
            // N≥3 sources: delta evaluation — when fact F is added to source K, fire only
            // NEW combinations: (snapshot_0 × ... × {F} × ... × snapshot_N).
            for (int slot = 0; slot < sources.size(); slot++) {
                final int triggerSlot = slot;
                DataProcessor<CTX, Object> proc = new DataProcessor<CTX, Object>() {
                    public void add(Context<CTX> c, ObjectHandle<Object> h) {
                        evaluateAllCombinations(c, sources, filters, rawHead, negations, existences,
                                immediate, agenda, triggerSlot, h.getObject());
                    }
                    public void update(Context<CTX> c, ObjectHandle<Object> h) {
                        evaluateAllCombinations(c, sources, filters, rawHead, negations, existences,
                                immediate, agenda, triggerSlot, h.getObject());
                    }
                    public void remove(Context<CTX> c, ObjectHandle<Object> h) { /* no re-eval on remove for now */ }
                };
                router.subscribe(slot, proc);
            }
        }
    }

    /** Find the JoinNode in the Rete topology associated with this rule. */
    private JoinNode findJoinNode(org.drools.base.definitions.rule.impl.RuleImpl rule) {
        return findJoinNodeIn(rete, rule);
    }

    private JoinNode findJoinNodeIn(BaseNode node, org.drools.base.definitions.rule.impl.RuleImpl rule) {
        if (node instanceof JoinNode && node.isAssociatedWith(rule)) {
            return (JoinNode) node;
        }
        for (BaseNode out : node.getOutputs()) {
            JoinNode found = findJoinNodeIn(out, rule);
            if (found != null) return found;
        }
        return null;
    }

    /**
     * Functional cross-product evaluation for N≥3 source rules.
     * Snapshots all sources via asList(), cross-products, applies filters and scopes,
     * then invokes the action consumer via reflection.
     */
    /**
     * Delta evaluation for N≥3 source rules.
     * When fact {@code triggerFact} is added to source {@code triggerSlot}, fires only
     * the NEW combinations: snapshot[0] × ... × {triggerFact} × ... × snapshot[N-1].
     * Other slots use their full current snapshot, ensuring each combination fires exactly once.
     */
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
            // For the trigger slot: only the new fact. For all others: current snapshot.
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
                    if (filterPred == null || invokePredicate(filterPred, ctx, extended)) {
                        next.add(extended);
                    }
                }
            }
            combinations = next;
            if (combinations.isEmpty()) return;
        }

        Method m = Arrays.stream(rawConsumer.getClass().getMethods())
                .filter(me -> me.getName().equals("accept") && !me.isSynthetic())
                .findFirst().orElseThrow();

        for (Object[] combo : combinations) {
            Object[] outerFacts = combo;
            boolean allowed = true;
            for (ScopeDescriptor<CTX> neg : negations)
                if (scopeHasMatch(neg, ctx, neg.globalEval ? new Object[0] : outerFacts)) { allowed = false; break; }
            if (!allowed) continue;
            for (ScopeDescriptor<CTX> ex : existences)
                if (!scopeHasMatch(ex, ctx, ex.globalEval ? new Object[0] : outerFacts)) { allowed = false; break; }
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

    /** Checks scopes for a 2-fact outer rule where both left and right facts are available. */
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

    /** Wraps a processor to check not()/exists() scopes before delegating. */
    @SuppressWarnings("unchecked")
    private DataProcessor<CTX, Object> scopeGuard(
            DataProcessor<CTX, Object> delegate,
            List<ScopeDescriptor<CTX>> negations,
            List<ScopeDescriptor<CTX>> existences) {
        if (negations.isEmpty() && existences.isEmpty()) return delegate;
        return new DataProcessor<CTX, Object>() {
            public void add(Context<CTX> c, ObjectHandle<Object> h) {
                Object fact = h.getObject();
                if (scopesAllow(c, fact)) delegate.add(c, h);
            }
            public void update(Context<CTX> c, ObjectHandle<Object> h) {
                Object fact = h.getObject();
                if (scopesAllow(c, fact)) delegate.update(c, h);
            }
            public void remove(Context<CTX> c, ObjectHandle<Object> h) {
                delegate.remove(c, h);
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

    /**
     * Evaluates a scope by cross-producting its inner sources with the outer facts,
     * applying each filter, and returning true if any combination passes all filters.
     */
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
                    if (filterPred == null || invokePredicate(filterPred, ctx, combined)) {
                        next.add(combined);
                    }
                }
            }
            combinations = next;
            if (combinations.isEmpty()) return false;
        }
        return !combinations.isEmpty();
    }

    private boolean invokePredicate(Object pred, Context<CTX> ctx, Object[] facts) {
        try {
            Method m = Arrays.stream(pred.getClass().getMethods())
                    .filter(me -> me.getName().equals("test") && !me.isSynthetic())
                    .findFirst()
                    .orElseThrow();
            Object[] args = new Object[facts.length + 1];
            args[0] = ctx;
            System.arraycopy(facts, 0, args, 1, facts.length);
            return (Boolean) m.invoke(pred, args);
        } catch (Exception e) {
            throw new RuntimeException("Scope predicate invocation failed", e);
        }
    }

    private DataProcessor<CTX, Object> buildAction(Consumer2<Context<CTX>, Object> consumer, boolean immediate) {
        if (immediate) return new Action1<>(consumer);
        return new DataProcessor<CTX, Object>() {
            public void add(Context<CTX> c, ObjectHandle<Object> h) { agenda.enqueue(() -> consumer.accept(c, h.getObject())); }
            public void update(Context<CTX> c, ObjectHandle<Object> h) { agenda.enqueue(() -> consumer.accept(c, h.getObject())); }
            public void remove(Context<CTX> c, ObjectHandle<Object> h) { }
        };
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    private void subscribeWithFilter(int slot, DataProcessor<CTX, Object> processor, Object filter) {
        if (filter != null) {
            Predicate2<Context<CTX>, Object> pred = (Predicate2<Context<CTX>, Object>) filter;
            Filter1<CTX, Object> f1 = new Filter1<>(pred);
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

    public Router<CTX> getRouter()         { return router; }
    public ContextPojoDS<CTX> getContext() { return context; }
}
