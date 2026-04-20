package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.api.data.DataProcessor;
import org.drools.core.function.Consumer2;

public class Action1<CTX, T> extends AbstractDataProcessor<CTX, T> implements DataProcessor<CTX, T> {
    private Consumer2<Context<CTX>, T> consumer;

    public Action1(Consumer2<Context<CTX>, T> consumer) {
        this.consumer = consumer;
    }

    @Override
    public void add(Context<CTX> ctx, ObjectHandle<T> handle) {
        consumer.accept(ctx, handle.get());
        subscribers.forEach( c -> c.add(ctx, handle) );
    }

    @Override
    public void update(Context<CTX> ctx, ObjectHandle<T> handle) {
        consumer.accept(ctx, handle.get());
        subscribers.forEach( c -> c.add(ctx, handle) );
    }

    @Override
    public void remove(Context<CTX> ctx, ObjectHandle<T> handle) {
        consumer.accept(ctx, handle.get());
        subscribers.forEach( c -> c.remove(ctx, handle) );
    }
}
