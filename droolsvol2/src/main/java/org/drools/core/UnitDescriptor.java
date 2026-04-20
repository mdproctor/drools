package org.drools.core;

import org.drools.core.RuleBuilder.RuleDescriptor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Compiled representation of a named unit within a RuleBase package.
 * Holds all RuleDescriptors for the unit's rules.
 * UnitInstances are created from a UnitDescriptor + a DS record instance.
 */
public class UnitDescriptor<DS> {

    private final List<RuleDescriptor<DS>> rules = new ArrayList<>();

    void addRule(RuleDescriptor<DS> descriptor) {
        rules.add(descriptor);
    }

    public List<RuleDescriptor<DS>> getRules() {
        return Collections.unmodifiableList(rules);
    }

    @SuppressWarnings("unchecked")
    public UnitInstance<DS> createInstance(DS ds) {
        return new UnitInstance<>(ds, rules.toArray(new RuleDescriptor[0]));
    }
}
