package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.api.data.DataProcessor;

import java.util.List;

public class Filter1TypeIndex<CTX, T> extends AbstractDataProcessor<CTX, T> implements DataProcessor<CTX, T> {

    public Filter1TypeIndex() {
        super();
    }

    @Override
    public void add(Context<CTX> ctx, ObjectHandle<T> handle) {
        List<DataProcessor<CTX, T>> list = ctx.getDataProcessorsByTypeAssignment(handle);
        if (list != null) {
            for (int i = 0, size = list.size(); i < size; i++) {
                DataProcessor<CTX, T> processor = list.get(i);
                processor.add(ctx, handle);
            }
        }
    }

    @Override
    public void update(Context<CTX> ctx, ObjectHandle<T> handle) {
        List<DataProcessor<CTX, T>> list = ctx.getDataProcessorsByTypeAssignment(handle);
        if (list != null) {
            for (int i = 0, size = list.size(); i < size; i++) {
                DataProcessor<CTX, T> processor = list.get(i);
                processor.update(ctx, handle);
            }
        }
    }

    @Override
    public void remove(Context<CTX> ctx, ObjectHandle<T> handle) {
        List<DataProcessor<CTX, T>> list = ctx.getDataProcessorsByTypeAssignment(handle);
        if (list != null) {
            for (int i = 0, size = list.size(); i < size; i++) {
                DataProcessor<CTX, T> processor = list.get(i);
                processor.remove(ctx, handle);
            }
        }
    }


}
