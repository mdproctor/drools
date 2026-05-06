package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.core.function.Predicate2;

/** Unit-evaluation-chain predicate filter — implements UnitProcessor for use after the Router. */
public class Filter1UnitProcessor<CTX, T> extends AbstractUnitProcessor<CTX, T> implements UnitProcessor<CTX, T> {
    private final Predicate2<Context<CTX>, T> predicate;

    public Filter1UnitProcessor(Predicate2<Context<CTX>, T> predicate) {
        this.predicate = predicate;
    }

    @Override
    public void add(UnitInstance<CTX> unit, ObjectHandle<T> handle) {
        if (predicate.test(unit.getContext(), handle.getObject())) {
            subscribers.forEach(s -> s.add(unit, handle));
        }
    }

    @Override
    public void update(UnitInstance<CTX> unit, ObjectHandle<T> handle) {
        if (predicate.test(unit.getContext(), handle.getObject())) {
            subscribers.forEach(s -> s.update(unit, handle));
        } else {
            subscribers.forEach(s -> s.remove(unit, handle));
        }
    }

    @Override
    public void remove(UnitInstance<CTX> unit, ObjectHandle<T> handle) {
        subscribers.forEach(s -> s.remove(unit, handle));
    }
}
