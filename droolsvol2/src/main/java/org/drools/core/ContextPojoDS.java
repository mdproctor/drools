package org.drools.core;

public class ContextPojoDS<CTX> extends AbstractContext<CTX> implements Context<CTX> {

    private CTX sources;

    public ContextPojoDS(CTX sources) {
        this.sources = sources;
    }

    public CTX context() {
        return sources;
    }

    @Override
    public <M> M getMemory(Object object) {
        return null;
    }

    @Override
    public String toString() {
        return "ContextPojoDS{" +
               "sources=" + sources +
               '}';
    }
}
