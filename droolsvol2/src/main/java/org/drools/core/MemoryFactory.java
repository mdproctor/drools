package org.drools.core;

public interface MemoryFactory<M extends Memory> {
    M createMemory();
}
