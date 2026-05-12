package org.drools.core;

import org.drools.core.RuleBuilder.RuleDescriptor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Compiled representation of a named unit within a RuleBase package.
 * Holds all RuleDescriptors for the unit's rules and the EvaluationEngine to use.
 *
 * compile() is called once when the descriptor is finalised (lazy, on first createInstance).
 * Subsequent createInstance() calls go directly to CompiledEngine.createUnit().
 */
public class UnitDescriptor<CTX> {

    private final List<RuleDescriptor<CTX>> rules = new ArrayList<>();
    @SuppressWarnings("unchecked")
    private EvaluationEngine<CTX> engine = BruteForceEngine.INSTANCE;
    private CompiledEngine<CTX> compiledEngine;

    void addRule(RuleDescriptor<CTX> descriptor) {
        rules.add(descriptor);
        compiledEngine = null; // invalidate on rule addition
    }

    public List<RuleDescriptor<CTX>> getRules() {
        return Collections.unmodifiableList(rules);
    }

    public void setEngine(EvaluationEngine<CTX> engine) {
        this.engine = engine;
        this.compiledEngine = null;
    }

    public UnitInstance<CTX> createInstance(CTX ctx, EntryPointNode rete) {
        if (compiledEngine == null) {
            compiledEngine = engine.compile(this, rete);
        }
        return compiledEngine.createUnit(ctx);
    }
}
