package org.drools.api.data;

import org.drools.core.Context;

public interface DataProcessor<CTX, T> {
    void add(Context<CTX> ctx, ObjectHandle<T> handle);

    void update(Context<CTX> ctx, ObjectHandle<T> handle);

    void remove(Context<CTX> ctx, ObjectHandle<T> handle);

}
