package org.drools.core;

import org.drools.api.data.DataProcessor;
import org.drools.api.data.DataSource;
import org.drools.api.data.ObjectHandle;
import org.drools.core.RuleBuilder.RuleDescriptor;
import org.drools.core.function.Consumer2;
import org.drools.core.function.Consumer3;
import org.drools.core.function.Function1;
import org.drools.core.function.Predicate2;

import java.util.ArrayList;
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

        if (sources.size() == 1) {
            Consumer2<Context<CTX>, Object> consumer = (Consumer2<Context<CTX>, Object>) rawHead;
            DataProcessor<CTX, Object> action = buildAction(consumer, immediate);
            subscribeWithFilter(0, action, filters.isEmpty() ? null : filters.get(0));

        } else if (sources.size() == 2) {
            Consumer3<Context<CTX>, Object, Object> consumer = (Consumer3<Context<CTX>, Object, Object>) rawHead;
            JoinNode joinNode = findJoinNode(desc.getRule());

            Object filter0 = filters.size() > 0 ? filters.get(0) : null;
            Object filter1 = filters.size() > 1 ? filters.get(1) : null;

            subscribeWithFilter(0, new JoinLeftInlet<>(joinNode, nodeMemories, consumer, immediate, agenda), filter0);
            subscribeWithFilter(1, new JoinRightInlet<>(joinNode, nodeMemories, consumer, immediate, agenda), filter1);

        } else {
            throw new UnsupportedOperationException("Rules with " + sources.size() + " patterns not yet supported");
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
