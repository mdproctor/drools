package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.core.function.Consumer3;

import java.util.ArrayList;

/**
 * Left inlet for a JoinNode.
 * Implements UnitProcessor — no runtime state in fields. Beta memory and agenda
 * are accessed through the UnitInstance passed at propagation time.
 */
public class JoinLeftInlet<CTX> implements UnitProcessor<CTX, Object> {

    private final JoinNode joinNode;
    private final Consumer3<Context<CTX>, Object, Object> consumer;
    private final boolean immediate;

    public JoinLeftInlet(JoinNode joinNode,
                         Consumer3<Context<CTX>, Object, Object> consumer,
                         boolean immediate) {
        this.joinNode  = joinNode;
        this.consumer  = consumer;
        this.immediate = immediate;
    }

    @Override
    public void add(UnitInstance<CTX> unit, ObjectHandle<Object> h) {
        JoinMemory mem = unit.getMemory(joinNode);
        mem.addLeft(h);
        for (ObjectHandle<?> rh : new ArrayList<>(mem.getRightHandles())) {
            fire(unit, h.getObject(), rh.getObject());
        }
    }

    @Override
    public void update(UnitInstance<CTX> unit, ObjectHandle<Object> h) {
        JoinMemory mem = unit.getMemory(joinNode);
        for (ObjectHandle<?> rh : new ArrayList<>(mem.getRightHandles())) {
            fire(unit, h.getObject(), rh.getObject());
        }
    }

    @Override
    public void remove(UnitInstance<CTX> unit, ObjectHandle<Object> h) {
        unit.getMemory(joinNode).removeLeft(h);
    }

    private void fire(UnitInstance<CTX> unit, Object left, Object right) {
        if (immediate) consumer.accept(unit.getContext(), left, right);
        else unit.getAgenda().enqueue(() -> consumer.accept(unit.getContext(), left, right));
    }
}
