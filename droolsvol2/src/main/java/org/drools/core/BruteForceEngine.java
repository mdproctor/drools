package org.drools.core;

/**
 * Stateless factory for BruteForceCompiledEngine.
 * Default EvaluationEngine — used while the real incremental Rete engine is built.
 */
public class BruteForceEngine<CTX> implements EvaluationEngine<CTX> {

    @SuppressWarnings("rawtypes")
    public static final BruteForceEngine INSTANCE = new BruteForceEngine<>();

    @Override
    public CompiledEngine<CTX> compile(UnitDescriptor<CTX> descriptor, EntryPointNode rete) {
        return new BruteForceCompiledEngine<>(descriptor, rete);
    }
}
