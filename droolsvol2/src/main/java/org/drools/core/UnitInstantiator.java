package org.drools.core;

/**
 * Decoupled factory for UnitInstance creation.
 * Keeps RuleBase free of any knowledge of how instances are created,
 * allowing different instantiation strategies in future.
 *
 * Usage:
 *   UnitInstantiator.using(ruleBase).createInstance("org.domain.Unit1", ds)
 */
public class UnitInstantiator<DS> {

    private final RuleBase<?> ruleBase;

    private UnitInstantiator(RuleBase<?> ruleBase) {
        this.ruleBase = ruleBase;
    }

    public static <DS> UnitInstantiator<DS> from(RuleBase<?> ruleBase) {
        return new UnitInstantiator<>(ruleBase);
    }

    public UnitInstance<DS> createInstance(String unitFqn, DS ds) {
        UnitDescriptor<DS> descriptor = ruleBase.unitDescriptor(unitFqn);
        if (descriptor == null) {
            throw new IllegalArgumentException("No unit registered as '" + unitFqn + "'");
        }
        return descriptor.createInstance(ds);
    }
}
