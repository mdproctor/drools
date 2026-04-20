package org.drools.core;

/**
 * Decoupled factory for UnitInstance creation.
 * Keeps RuleBase free of any knowledge of how instances are created,
 * allowing different instantiation strategies in future.
 *
 * Usage:
 *   UnitInstantiator.using(ruleBase).createInstance("org.domain.Unit1", ctx)
 */
public class UnitInstantiator<CTX> {

    private final RuleBase<?> ruleBase;

    private UnitInstantiator(RuleBase<?> ruleBase) {
        this.ruleBase = ruleBase;
    }

    public static <CTX> UnitInstantiator<CTX> from(RuleBase<CTX> ruleBase) {
        return new UnitInstantiator<>(ruleBase);
    }

    public UnitInstance<CTX> createInstance(String unitFqn, CTX ctx) {
        UnitDescriptor<CTX> descriptor = ruleBase.unitDescriptor(unitFqn);
        if (descriptor == null) {
            throw new IllegalArgumentException("No unit registered as '" + unitFqn + "'");
        }
        return descriptor.createInstance(ctx, ruleBase.getRete());
    }
}
