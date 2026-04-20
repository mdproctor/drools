package org.drools.core;

import org.drools.api.data.DataSource;

public class SelfContext<CTX extends DataSource> extends AbstractContext<CTX> implements Context<CTX> {
    private CTX dataSource;

    public SelfContext(CTX dataSource) {
        this.dataSource = dataSource;
    }

    public CTX get() {
        return dataSource;
    }

    @Override
    public CTX context() {
        return dataSource;
    }

    @Override
    public <M> M getMemory(Object object) {
        return null;
    }

}
