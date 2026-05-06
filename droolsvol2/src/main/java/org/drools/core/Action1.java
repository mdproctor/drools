package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.core.function.Consumer2;

public class Action1<CTX, T> extends AbstractUnitProcessor<CTX, T> implements UnitProcessor<CTX, T> {
    private final Consumer2<Context<CTX>, T> consumer;

    public Action1(Consumer2<Context<CTX>, T> consumer) {
        this.consumer = consumer;
    }

    @Override
    public void add(UnitInstance<CTX> unit, ObjectHandle<T> handle) {
        consumer.accept(unit.getContext(), handle.get());
        subscribers.forEach(s -> s.add(unit, handle));
    }

    @Override
    public void update(UnitInstance<CTX> unit, ObjectHandle<T> handle) {
        consumer.accept(unit.getContext(), handle.get());
        subscribers.forEach(s -> s.update(unit, handle));
    }

    @Override
    public void remove(UnitInstance<CTX> unit, ObjectHandle<T> handle) {
        consumer.accept(unit.getContext(), handle.get());
        subscribers.forEach(s -> s.remove(unit, handle));
    }
}
