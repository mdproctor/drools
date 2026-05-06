package org.drools.core;

import org.drools.api.data.ObjectHandle;

import java.util.ArrayList;
import java.util.List;

public class Router<CTX> {
    List<List<UnitProcessor<CTX, ?>>> processors;
    private List<UnitInstance<CTX>> contexts;

    public Router(int size) {
        this.processors = new ArrayList<>(size);
        for (int i = 0; i < size; i++) {
            this.processors.add(new ArrayList<>());
        }
        this.contexts = new ArrayList<>(10);
    }

    public Handle addContext(UnitInstance<CTX> unit) {
        IndexHandle handle = new IndexHandle(contexts.size());
        contexts.add(unit);
        return handle;
    }

    public void removeContext(Handle handle) {
        contexts.remove(((IndexHandle) handle).getIndex());
    }

    public <T> void subscribe(int index, UnitProcessor<CTX, T> processor) {
        processors.get(index).add(processor);
    }

    public <T> void unsubscribe(int index, UnitProcessor<CTX, T> processor) {
        processors.get(index).remove(processor);
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public void add(int index, ObjectHandle handle) {
        contexts.forEach(unit ->
            processors.get(index).forEach(p -> p.add(unit, handle)));
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public void update(int index, ObjectHandle handle) {
        contexts.forEach(unit ->
            processors.get(index).forEach(p -> p.update(unit, handle)));
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public void remove(int index, ObjectHandle handle) {
        contexts.forEach(unit ->
            processors.get(index).forEach(p -> p.remove(unit, handle)));
    }
}
