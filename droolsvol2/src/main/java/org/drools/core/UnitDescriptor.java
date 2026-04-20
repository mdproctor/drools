package org.drools.core;

import org.drools.core.RuleBuilder.RuleDescriptor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Compiled representation of a named unit within a RuleBase package.
 * Holds all RuleDescriptors for the unit's rules.
 * UnitInstances are created from a UnitDescriptor + a CTX record instance.
 */
public class UnitDescriptor<CTX> {

    private final List<RuleDescriptor<CTX>> rules = new ArrayList<>();

    void addRule(RuleDescriptor<CTX> descriptor) {
        rules.add(descriptor);
    }

    public List<RuleDescriptor<CTX>> getRules() {
        return Collections.unmodifiableList(rules);
    }

    @SuppressWarnings("unchecked")
    public UnitInstance<CTX> createInstance(CTX ctx, EntryPointNode rete) {
        return new UnitInstance<>(ctx, rete, rules.toArray(new RuleDescriptor[0]));
    }
}
