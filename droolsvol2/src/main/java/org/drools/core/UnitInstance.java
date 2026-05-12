package org.drools.core;

import org.drools.api.data.ObjectHandle;

/**
 * Per-unit runtime state: memories, agenda, and context.
 *
 * Pure state bag — no wiring logic, no engine knowledge, no Router reference.
 * Created by CompiledEngine.createUnit(); evaluation wiring is the engine's concern.
 * Data mutation methods (add/update/remove) trigger the DataStore propagation chain
 * and drain the agenda — they do not interact with the engine directly.
 */
public class UnitInstance<CTX> {

    private final ContextPojoDS<CTX> context;
    private final Agenda agenda = new Agenda();
    private final NodeMemories nodeMemories = new SimpleNodeMemories();

    UnitInstance(CTX ctx) {
        this.context = new ContextPojoDS<>(ctx);
    }

    // --- Data mutation methods — trigger DataStore → Router chain, then drain agenda ---

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

    public <M extends Memory> M getMemory(MemoryFactory<M> node) {
        return nodeMemories.getNodeMemory(node);
    }

    public Agenda getAgenda() { return agenda; }

    public Context<CTX> getContext() { return context; }
}
