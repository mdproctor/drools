package org.drools.core;

import org.drools.api.data.DataProcessor;

import java.util.ArrayList;

public abstract class AbstractDataProcessor<CTX, T> {
    protected ArrayList<DataProcessor<CTX, T>> subscribers;

    public AbstractDataProcessor() {
        this.subscribers = new ArrayList<DataProcessor<CTX, T>>();
    }

    public void subscribe(DataProcessor<CTX, T> processor) {
        subscribers.add(processor);
    }

    public void unsubscribe(DataProcessor<CTX, T> processor) {
        subscribers.remove(processor);
    }
}
