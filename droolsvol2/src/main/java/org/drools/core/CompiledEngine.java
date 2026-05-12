package org.drools.core;

/**
 * An evaluation engine compiled for a specific unit type.
 *
 * createUnit() must be as fast as possible — all heavy computation was done in
 * EvaluationEngine.compile(). Implementations should do nothing here beyond
 * allocating per-unit state and registering the unit for event dispatch.
 */
public interface CompiledEngine<CTX> {
    UnitInstance<CTX> createUnit(CTX ctx);
    void disposeUnit(UnitInstance<CTX> unit);
}
