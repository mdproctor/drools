package org.drools.core;

import org.drools.api.data.DataProcessor;
import org.drools.api.data.DataSource;
import org.drools.api.data.ObjectHandle;
import org.drools.core.RuleBuilder.RuleDescriptor;
import org.drools.core.function.Consumer2;
import org.drools.core.function.Consumer3;
import org.drools.core.function.Function1;

import java.util.ArrayList;
import java.util.List;

/**
 * Vol2 equivalent of WorkingMemory + Agenda.
 * All rule evaluations for a unit happen within one UnitInstance.
 *
 * Wires a RuleDescriptor to a Router: subscribes each DataSource from the CTX
 * record to the appropriate Router slot, then subscribes evaluation handlers
 * (ifn — inline; fn — deferred, TODO) per rule.
 *
 * The network is stateless; UnitInstance holds the per-instance beta memories.
 * Multiple UnitInstances can share the same RuleDescriptor without interference.
 */
public class UnitInstance<CTX> {

    private final Router<CTX> router;
    private final ContextPojoDS<CTX> context;

    @SuppressWarnings({"unchecked", "rawtypes"})
    public UnitInstance(CTX ctx, RuleDescriptor<CTX>... descriptors) {
        int slots = countSlots(descriptors);
        this.router  = new Router<>(slots);
        this.context = new ContextPojoDS<>(ctx);
        this.router.addContext(context);

        // Subscribe one ContextRouterAdapter per source slot (shared across rules).
        // We track which DataSource instances have already been wired by slot index.
        List<DataSource<?>> wiredSources = new ArrayList<>();
        for (RuleDescriptor<CTX> desc : descriptors) {
            List<Function1<CTX, DataSource<?>>> sources = desc.getSources();
            for (int i = 0; i < sources.size(); i++) {
                DataSource<?> ds2 = sources.get(i).apply(ctx);
                if (!containsByIdentity(wiredSources, ds2)) {
                    wiredSources.add(ds2);
                    ((PropagatingDataStore) ds2).subscribe(new ContextRouterAdapter<>(i, router));
                }
            }
        }

        // Wire evaluation handlers for each descriptor
        for (RuleDescriptor<CTX> desc : descriptors) {
            wireHead(desc);
        }
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    private void wireHead(RuleDescriptor<CTX> desc) {
        List<Function1<CTX, DataSource<?>>> sources = desc.getSources();
        Object head = desc.getConsequence();

        if (sources.isEmpty()) {
            // No patterns — not yet supported
            throw new UnsupportedOperationException("Consequence-only rules (no from()) not yet supported via UnitInstance");
        }

        if (sources.size() == 1) {
            // Single-pattern: subscribe ifn directly to slot 0
            Consumer2<Context<CTX>, Object> ifn = (Consumer2<Context<CTX>, Object>) head;
            router.subscribe(0, new Action1<>(ifn));

        } else if (sources.size() == 2) {
            // Two-pattern join: beta memory + left/right handlers
            List<ObjectHandle<?>> leftMem  = new ArrayList<>();
            List<ObjectHandle<?>> rightMem = new ArrayList<>();
            Consumer3<Context<CTX>, Object, Object> ifn = (Consumer3<Context<CTX>, Object, Object>) head;

            router.subscribe(0, new DataProcessor<CTX, Object>() {
                public void add(Context<CTX> c, ObjectHandle<Object> h) {
                    leftMem.add(h);
                    rightMem.forEach(rh -> ifn.accept(c, h.getObject(), rh.getObject()));
                }
                public void update(Context<CTX> c, ObjectHandle<Object> h) { }
                public void remove(Context<CTX> c, ObjectHandle<Object> h) { leftMem.remove(h); }
            });

            router.subscribe(1, new DataProcessor<CTX, Object>() {
                public void add(Context<CTX> c, ObjectHandle<Object> h) {
                    rightMem.add(h);
                    leftMem.forEach(lh -> ifn.accept(c, lh.getObject(), h.getObject()));
                }
                public void update(Context<CTX> c, ObjectHandle<Object> h) { }
                public void remove(Context<CTX> c, ObjectHandle<Object> h) { rightMem.remove(h); }
            });

        } else {
            throw new UnsupportedOperationException("Rules with " + sources.size() + " patterns not yet supported");
        }
    }

    private static int countSlots(RuleDescriptor<?>[] descriptors) {
        int max = 0;
        for (RuleDescriptor<?> d : descriptors) {
            max = Math.max(max, d.getSources().size());
        }
        return Math.max(max, 1);
    }

    private static boolean containsByIdentity(List<?> list, Object item) {
        for (Object o : list) {
            if (o == item) return true;
        }
        return false;
    }

    public Router<CTX> getRouter()           { return router; }
    public ContextPojoDS<CTX> getContext()   { return context; }
}
