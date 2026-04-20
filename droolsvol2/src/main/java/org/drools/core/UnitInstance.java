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
 * Propagation and join logic live entirely here — not on network nodes.
 */
public class UnitInstance<CTX> {

    private final Router<CTX> router;
    private final ContextPojoDS<CTX> context;
    private final Agenda agenda = new Agenda();

    @SuppressWarnings({"unchecked", "rawtypes"})
    public UnitInstance(CTX ctx, RuleDescriptor<CTX>... descriptors) {
        int slots = countSlots(descriptors);
        this.router  = new Router<>(slots);
        this.context = new ContextPojoDS<>(ctx);
        this.router.addContext(context);

        List<DataSource<?>> wiredSources = new ArrayList<>();
        for (RuleDescriptor<CTX> desc : descriptors) {
            List<Function1<CTX, DataSource<?>>> sources = desc.getSources();
            for (int i = 0; i < sources.size(); i++) {
                DataSource<?> ds = sources.get(i).apply(ctx);
                if (!containsByIdentity(wiredSources, ds)) {
                    wiredSources.add(ds);
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

    // --- Internal wiring ---

    @SuppressWarnings({"unchecked", "rawtypes"})
    private void wireHead(RuleDescriptor<CTX> desc) {
        List<Function1<CTX, DataSource<?>>> sources = desc.getSources();
        List<Object> filters = desc.getFilters();
        Object rawHead = desc.getHead();
        boolean immediate = desc.isImmediate();

        if (sources.isEmpty()) {
            throw new UnsupportedOperationException("Rules with no from() not yet supported via UnitInstance");
        }

        if (sources.size() == 1) {
            Consumer2<Context<CTX>, Object> consumer = (Consumer2<Context<CTX>, Object>) rawHead;
            DataProcessor<CTX, Object> action = buildAction(consumer, immediate);
            subscribeWithFilter(0, action, filters.isEmpty() ? null : filters.get(0));

        } else if (sources.size() == 2) {
            Consumer3<Context<CTX>, Object, Object> consumer = (Consumer3<Context<CTX>, Object, Object>) rawHead;
            JoinMemory betaMem = new JoinMemory();
            Object filter0 = filters.size() > 0 ? filters.get(0) : null;
            Object filter1 = filters.size() > 1 ? filters.get(1) : null;

            DataProcessor<CTX, Object> leftProc = new DataProcessor<CTX, Object>() {
                public void add(Context<CTX> c, ObjectHandle<Object> h) {
                    betaMem.addLeft(h);
                    for (ObjectHandle<?> rh : new ArrayList<>(betaMem.getRightHandles())) {
                        fire(c, h.getObject(), rh.getObject(), consumer, immediate);
                    }
                }
                public void update(Context<CTX> c, ObjectHandle<Object> h) {
                    for (ObjectHandle<?> rh : new ArrayList<>(betaMem.getRightHandles())) {
                        fire(c, h.getObject(), rh.getObject(), consumer, immediate);
                    }
                }
                public void remove(Context<CTX> c, ObjectHandle<Object> h) {
                    betaMem.removeLeft(h);
                }
            };

            DataProcessor<CTX, Object> rightProc = new DataProcessor<CTX, Object>() {
                public void add(Context<CTX> c, ObjectHandle<Object> h) {
                    betaMem.addRight(h);
                    for (ObjectHandle<?> lh : new ArrayList<>(betaMem.getLeftHandles())) {
                        fire(c, lh.getObject(), h.getObject(), consumer, immediate);
                    }
                }
                public void update(Context<CTX> c, ObjectHandle<Object> h) {
                    for (ObjectHandle<?> lh : new ArrayList<>(betaMem.getLeftHandles())) {
                        fire(c, lh.getObject(), h.getObject(), consumer, immediate);
                    }
                }
                public void remove(Context<CTX> c, ObjectHandle<Object> h) {
                    betaMem.removeRight(h);
                }
            };

            subscribeWithFilter(0, leftProc,  filter0);
            subscribeWithFilter(1, rightProc, filter1);

        } else {
            throw new UnsupportedOperationException("Rules with " + sources.size() + " patterns not yet supported");
        }
    }

    private void fire(Context<CTX> c, Object left, Object right,
                      Consumer3<Context<CTX>, Object, Object> consumer, boolean immediate) {
        if (immediate) {
            consumer.accept(c, left, right);
        } else {
            agenda.enqueue(() -> consumer.accept(c, left, right));
        }
    }

    @SuppressWarnings("unchecked")
    private DataProcessor<CTX, Object> buildAction(Consumer2<Context<CTX>, Object> consumer, boolean immediate) {
        if (immediate) {
            return new Action1<>(consumer);
        }
        return new DataProcessor<CTX, Object>() {
            public void add(Context<CTX> c, ObjectHandle<Object> h) {
                agenda.enqueue(() -> consumer.accept(c, h.getObject()));
            }
            public void update(Context<CTX> c, ObjectHandle<Object> h) {
                agenda.enqueue(() -> consumer.accept(c, h.getObject()));
            }
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
