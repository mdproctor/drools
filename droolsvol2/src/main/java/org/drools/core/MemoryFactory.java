package org.drools.core;

public interface MemoryFactory<M extends Memory> {
    M createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator);

    default int getMemoryId() {
        return -1; // TODO #6650: implement memory ID assignment
    }
}
