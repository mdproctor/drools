package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.api.data.DataProcessor;

import java.util.List;

public interface Context<CTX> {

    CTX context();

    <T, K extends T> List<DataProcessor<CTX, K>> getDataProcessorsByTypeAssignment(ObjectHandle<T> handle);

    <M> M getMemory(Object object);

}
