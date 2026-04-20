package org.drools.core;

import org.drools.api.data.DataProcessor;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class TypeIndexer<CTX> {
    // Type erasure is necessary here, so it can be cast in the getDataProcessorsByTypeAssignment method.
    private Map<Class, List> map;

    public TypeIndexer() {
        this.map = new HashMap<>();
    }

    public <T> void buildCache(Class cls, List<DataProcessor<CTX, ? extends T>> list) {
        map.put(cls, list);
    }

    public <T, K extends T> List<DataProcessor<CTX, K>> getDataProcessorsByTypeAssignment(Class cls) {
        return map.get(cls);
    }
}
