package org.drools.core;

import org.drools.base.base.ValueResolver;
import org.drools.base.rule.accessor.GlobalResolver;
import org.drools.core.time.TimerService;

/**
 * Vol2 ReteEvaluator — the runtime session evaluator.
 * Implements ValueResolver for compatibility with drools-base timer infrastructure.
 * TODO #6650: implement vol2 ReteEvaluator once evaluation engine is built.
 */
public class ReteEvaluator implements ValueResolver {

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

    // ValueResolver implementation
    @Override
    public long getCurrentTime() {
        throw new UnsupportedOperationException("vol2 stub — see #6650");
    }

    @Override
    public GlobalResolver getGlobalResolver() {
        throw new UnsupportedOperationException("vol2 stub — see #6650");
    }

    @Override
    public org.drools.base.RuleBase getRuleBase() {
        throw new UnsupportedOperationException("vol2 stub — see #6650");
    }
}
