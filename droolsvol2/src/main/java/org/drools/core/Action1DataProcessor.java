package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.api.data.DataProcessor;
import org.drools.core.function.Consumer2;

/** Alpha-chain consumer — implements DataProcessor for use in the DataSource network. */
public class Action1DataProcessor<CTX, T> extends AbstractDataProcessor<CTX, T> implements DataProcessor<CTX, T> {
    private final Consumer2<Context<CTX>, T> consumer;

    public Action1DataProcessor(Consumer2<Context<CTX>, T> consumer) {
        this.consumer = consumer;
    }

    @Override
    public void add(Context<CTX> ctx, ObjectHandle<T> handle) {
        consumer.accept(ctx, handle.get());
        subscribers.forEach(s -> s.add(ctx, handle));
    }

    @Override
    public void update(Context<CTX> ctx, ObjectHandle<T> handle) {
        consumer.accept(ctx, handle.get());
        subscribers.forEach(s -> s.update(ctx, handle));
    }

    @Override
    public void remove(Context<CTX> ctx, ObjectHandle<T> handle) {
        consumer.accept(ctx, handle.get());
        subscribers.forEach(s -> s.remove(ctx, handle));
    }
}
