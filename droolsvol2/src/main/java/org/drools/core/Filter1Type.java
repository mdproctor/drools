package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.api.data.DataProcessor;
import org.drools.base.base.ObjectType;

public class Filter1Type<CTX, T> extends AbstractDataProcessor<CTX, T> implements DataProcessor<CTX, T> {

    private ObjectType type;

    public Filter1Type(ObjectType type) {
        super();
        this.type = type;
    }

    @Override
    public void add(Context<CTX> ctx, ObjectHandle<T> handle) {
        if (type.isAssignableFrom(handle.getObject().getClass())) {
            subscribers.forEach(c -> c.add(ctx, handle));
        }
    }

    @Override
    public void update(Context<CTX> ctx, ObjectHandle<T> handle) {
        if (type.isAssignableFrom(handle.getObject().getClass())) {
            subscribers.forEach(c -> c.update(ctx, handle));
        }
    }

    @Override
    public void remove(Context<CTX> ctx, ObjectHandle<T> handle) {
        if (type.isAssignableFrom(handle.getObject().getClass())) {
            subscribers.forEach(c -> c.remove(ctx, handle));
        }
    }
}
