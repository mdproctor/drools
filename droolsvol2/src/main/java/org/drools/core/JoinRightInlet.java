package org.drools.core;

import org.drools.api.data.DataProcessor;
import org.drools.api.data.ObjectHandle;
import org.drools.core.function.Consumer3;

import java.util.ArrayList;

/**
 * Right inlet for a JoinNode.
 * Receives handles from the right DataSource stream, uses the JoinNode's id
 * to look up the combined JoinMemory in UnitMemories (O(1) array access).
 */
public class JoinRightInlet<CTX> implements DataProcessor<CTX, Object> {

    private final JoinNode joinNode;
    private final UnitMemories memories;
    private final Consumer3<Context<CTX>, Object, Object> consumer;
    private final boolean immediate;
    private final Agenda agenda;

    public JoinRightInlet(JoinNode joinNode, UnitMemories memories,
                          Consumer3<Context<CTX>, Object, Object> consumer,
                          boolean immediate, Agenda agenda) {
        this.joinNode  = joinNode;
        this.memories  = memories;
        this.consumer  = consumer;
        this.immediate = immediate;
        this.agenda    = agenda;
    }

    @Override
    public void add(Context<CTX> c, ObjectHandle<Object> h) {
        JoinMemory mem = memories.getOrCreateJoinMemory(joinNode.getId());
        mem.addRight(h);
        for (ObjectHandle<?> lh : new ArrayList<>(mem.getLeftHandles())) {
            fire(c, lh.getObject(), h.getObject());
        }
    }

    @Override
    public void update(Context<CTX> c, ObjectHandle<Object> h) {
        JoinMemory mem = memories.getOrCreateJoinMemory(joinNode.getId());
        for (ObjectHandle<?> lh : new ArrayList<>(mem.getLeftHandles())) {
            fire(c, lh.getObject(), h.getObject());
        }
    }

    @Override
    public void remove(Context<CTX> c, ObjectHandle<Object> h) {
        memories.getOrCreateJoinMemory(joinNode.getId()).removeRight(h);
    }

    private void fire(Context<CTX> c, Object left, Object right) {
        if (immediate) consumer.accept(c, left, right);
        else agenda.enqueue(() -> consumer.accept(c, left, right));
    }
}
