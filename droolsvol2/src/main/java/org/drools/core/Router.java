package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.api.data.DataProcessor;

import java.util.ArrayList;
import java.util.List;

public class Router<CTX> {
    // Each DataProcess can receive a different type, so it can no longer be typed within this class.
    List<List<DataProcessor<CTX, ?>>> processors;

    private List<ContextPojoDS<CTX>> contexts;

    public Router(int size) {
        this.processors = new ArrayList<>(size);
        for (int i = 0; i < size; i++) {
            this.processors.add(new ArrayList<>());
        }

        this.contexts = new ArrayList<>(10);
    }

    public Handle addContext(ContextPojoDS<CTX> context) {
        IndexHandle handle = new IndexHandle(contexts.size());
        contexts.add(context);
        return handle;
    }

    public void removeContext(Handle handle) {
        contexts.remove(((IndexHandle) handle).getIndex());
    }

    public <T> void subscribe(int index, DataProcessor<CTX, T> dataProcessor) {
        processors.get(index).add(dataProcessor);
    }

    public <T> void unsubscribe(int index, DataProcessor<CTX, T> dataProcessor) {
        processors.get(index).add(dataProcessor);
    }

    public <T> void add(int index, ObjectHandle handle) { // lose the Generics, so handle can be used for any type
        contexts.forEach(ctx -> {
            processors.get(index).forEach( dp -> dp.add(ctx, handle));
        });
    }

    public void update(int index, ObjectHandle handle) { // lose the Generics, so handle can be used for any type
        contexts.forEach(ctx -> {
            processors.get(index).forEach( dp -> dp.update(ctx, handle));
        });
    }

    public void remove(int index, ObjectHandle handle) { // lose the Generics, so handle can be used for any type
        contexts.forEach(ctx -> {
            processors.get(index).forEach( dp -> dp.remove(ctx, handle));
        });
    }
}
