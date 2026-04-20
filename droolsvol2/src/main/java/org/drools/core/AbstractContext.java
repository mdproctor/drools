package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.api.data.DataProcessor;

import java.util.List;

public abstract class AbstractContext<CTX> implements Context<CTX> {

    // Type erasure is necessary here, so it can be cast in the getDataProcessorsByTypeAssignment method.
    private TypeIndexer<CTX> typeIndexer;

    public AbstractContext() {

    }

    public TypeIndexer<CTX> getTypeIndexer() {
        return typeIndexer;
    }

    public void setTypeIndexer(TypeIndexer<CTX> typeIndexer) {
        this.typeIndexer = typeIndexer;
    }

    @Override
    public <T, K extends T> List<DataProcessor<CTX, K>> getDataProcessorsByTypeAssignment(ObjectHandle<T> handle) {
        return typeIndexer.getDataProcessorsByTypeAssignment(handle.getObject().getClass());
    }

}
