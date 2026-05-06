package org.drools.core;

import java.util.ArrayList;

/** Subscriber management base for unit-evaluation-chain processors. */
public abstract class AbstractUnitProcessor<CTX, T> {
    protected ArrayList<UnitProcessor<CTX, T>> subscribers = new ArrayList<>();

    public void subscribe(UnitProcessor<CTX, T> processor) {
        subscribers.add(processor);
    }

    public void unsubscribe(UnitProcessor<CTX, T> processor) {
        subscribers.remove(processor);
    }
}
