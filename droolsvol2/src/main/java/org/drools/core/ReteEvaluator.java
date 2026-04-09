package org.drools.core;

import org.drools.base.common.NetworkNode;
import org.drools.core.time.TimerService;

/**
 * Vol2 ReteEvaluator — the runtime session evaluator.
 * TODO #6650: implement vol2 ReteEvaluator once evaluation engine is built.
 * Methods are stubs; real implementation will wire to container queue and DataSources.
 */
public class ReteEvaluator {

    public TimerService getTimerService() {
        throw new UnsupportedOperationException("vol2 stub — see #6650");
    }

    public ActivationsManager getActivationsManager() {
        throw new UnsupportedOperationException("vol2 stub — see #6650");
    }

    public RuleSessionConfiguration getRuleSessionConfiguration() {
        throw new UnsupportedOperationException("vol2 stub — see #6650");
    }

    public <T extends Memory> T getNodeMemory(MemoryFactory<T> node) {
        throw new UnsupportedOperationException("vol2 stub — see #6650");
    }

    public void addPropagation(Runnable action) {
        throw new UnsupportedOperationException("vol2 stub — see #6650");
    }
}
