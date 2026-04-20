package org.drools.core;

import org.drools.api.data.DataProcessor;
import org.drools.api.data.ObjectHandle;
import org.drools.core.function.Consumer3;

import java.util.ArrayList;

/**
 * Right inlet for a JoinNode.
 * Receives handles from the right DataSource stream, uses the JoinNode's id
 * to look up the combined JoinMemory in NodeMemories (O(1) array access).
 */
public class JoinRightInlet<CTX> implements DataProcessor<CTX, Object> {

    private final JoinNode joinNode;
    private final NodeMemories memories;
    private final Consumer3<Context<CTX>, Object, Object> consumer;
    private final boolean immediate;
    private final Agenda agenda;

    public JoinRightInlet(JoinNode joinNode, NodeMemories memories,
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
        JoinMemory mem = ((JoinMemory) memories.getNodeMemory(joinNode));
        mem.addRight(h);
        for (ObjectHandle<?> lh : new ArrayList<>(mem.getLeftHandles())) {
            fire(c, lh.getObject(), h.getObject());
        }
    }

    @Override
    public void update(Context<CTX> c, ObjectHandle<Object> h) {
        JoinMemory mem = ((JoinMemory) memories.getNodeMemory(joinNode));
        for (ObjectHandle<?> lh : new ArrayList<>(mem.getLeftHandles())) {
            fire(c, lh.getObject(), h.getObject());
        }
    }

    @Override
    public void remove(Context<CTX> c, ObjectHandle<Object> h) {
        ((JoinMemory) memories.getNodeMemory(joinNode)).removeRight(h);
    }

    private void fire(Context<CTX> c, Object left, Object right) {
        if (immediate) consumer.accept(c, left, right);
        else agenda.enqueue(() -> consumer.accept(c, left, right));
    }
}
