package org.drools.core;

/**
 * Pluggable evaluation algorithm for a unit type.
 *
 * compile() is called once per rulebase change — all heavy computation belongs here.
 * The resulting CompiledEngine is shared across all UnitInstances of the same type.
 */
public interface EvaluationEngine<CTX> {
    CompiledEngine<CTX> compile(UnitDescriptor<CTX> descriptor, EntryPointNode rete);
}
