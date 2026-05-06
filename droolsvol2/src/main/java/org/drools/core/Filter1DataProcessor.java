package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.api.data.DataProcessor;
import org.drools.core.function.Predicate2;

/** Alpha-chain predicate filter — implements DataProcessor for use in the DataSource network. */
public class Filter1DataProcessor<CTX, T> extends AbstractDataProcessor<CTX, T> implements DataProcessor<CTX, T> {
    private final Predicate2<Context<CTX>, T> predicate;

    public Filter1DataProcessor(Predicate2<Context<CTX>, T> predicate) {
        this.predicate = predicate;
    }

    @Override
    public void add(Context<CTX> ctx, ObjectHandle<T> handle) {
        if (predicate.test(ctx, handle.getObject())) {
            subscribers.forEach(c -> c.add(ctx, handle));
        }
    }

    @Override
    public void update(Context<CTX> ctx, ObjectHandle<T> handle) {
        if (predicate.test(ctx, handle.getObject())) {
            subscribers.forEach(c -> c.update(ctx, handle));
        } else {
            subscribers.forEach(c -> c.remove(ctx, handle));
        }
    }

    @Override
    public void remove(Context<CTX> ctx, ObjectHandle<T> handle) {
        subscribers.forEach(c -> c.remove(ctx, handle));
    }
}
