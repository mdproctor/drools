package org.drools.core;

import org.drools.api.data.DataStore;
import org.drools.core.RuleBuilder.RuleDescriptor;
import org.drools.core.function.Consumer2;
import org.drools.core.function.Consumer3;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the vol2 evaluation engine.
 * All tests go through RuleBaseModifier → UnitInstantiator.
 * Head/join logic lives in evaluation-layer DataProcessors, never on network nodes.
 */
public class RuleProapgationAndExecutionTest {

    record CTX1(DataStore<Person> persons) {}
    record CTX2(DataStore<Person> persons, DataStore<String> names) {}

    // --- DSL descriptor captures sources and head ---

    @Test
    public void testDescriptorStoresSourcesAndHead() {
        RuleDescriptor<CTX1> desc = new RuleBuilder<CTX1>()
                .rule("r1")
                .from(CTX1::persons)
                .ifn((ctx, p) -> {})
                .descriptor();

        assertThat(desc.getSources()).hasSize(1);
        assertThat(desc.getHead()).isInstanceOf(Consumer2.class);
    }

    @Test
    public void testDescriptorJoinStoresSourcesAndHead() {
        RuleDescriptor<CTX2> desc = new RuleBuilder<CTX2>()
                .rule("r1")
                .from(CTX2::persons)
                .join(CTX2::names)
                .ifn((ctx, p, n) -> {})
                .descriptor();

        assertThat(desc.getSources()).hasSize(2);
        assertThat(desc.getHead()).isInstanceOf(Consumer3.class);
    }

    // --- Single-pattern rule: ifn fires on add ---

    @Test
    public void testSinglePatternIfnFires() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        CTX1 unit = new CTX1(persons);

        List<String> fired = new ArrayList<>();
        RuleBase<CTX1> ruleBase = new RuleBase<>();
        RuleBaseModifier.with(ruleBase)
                        .apply(RuleBaseModifier.changeSet()
                                               .selectPackage("org.domain").selectUnit("Unit1")
                                               .add(new RuleBuilder<CTX1>().rule("r1")
                                                                            .from(CTX1::persons)
                                                                            .ifn((ctx, p) -> fired.add(p.name()))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", unit);

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).containsExactly("Darth");

        persons.add(new Person("Yoda", 900, "Dagobah"));
        assertThat(fired).containsExactly("Darth", "Yoda");
    }

    // --- Two-pattern join: ifn fires when both sides have data ---

    @Test
    public void testJoinIfnFires() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 unit = new CTX2(persons, names);

        List<String> fired = new ArrayList<>();
        RuleBase<CTX2> ruleBase = new RuleBase<>();
        RuleBaseModifier.with(ruleBase)
                        .apply(RuleBaseModifier.changeSet()
                                               .selectPackage("org.domain").selectUnit("Unit1")
                                               .add(new RuleBuilder<CTX2>().rule("r1")
                                                                            .from(CTX2::persons)
                                                                            .join(CTX2::names)
                                                                            .ifn((ctx, p, n) -> fired.add(p.name() + ":" + n))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", unit);

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).isEmpty();

        names.add("Vader");
        assertThat(fired).containsExactly("Darth:Vader");
    }

    @Test
    public void testJoinCrossProductFires() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 unit = new CTX2(persons, names);

        List<String> fired = new ArrayList<>();
        RuleBase<CTX2> ruleBase = new RuleBase<>();
        RuleBaseModifier.with(ruleBase)
                        .apply(RuleBaseModifier.changeSet()
                                               .selectPackage("org.domain").selectUnit("Unit1")
                                               .add(new RuleBuilder<CTX2>().rule("r1")
                                                                            .from(CTX2::persons)
                                                                            .join(CTX2::names)
                                                                            .ifn((ctx, p, n) -> fired.add(p.name() + ":" + n))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", unit);

        names.add("Skywalker");
        names.add("Vader");

        persons.add(new Person("Luke", 20, "Tatooine"));
        assertThat(fired).containsExactlyInAnyOrder("Luke:Skywalker", "Luke:Vader");

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).containsExactlyInAnyOrder(
                "Luke:Skywalker", "Luke:Vader", "Darth:Skywalker", "Darth:Vader");
    }

    @Test
    public void testMultipleRulesInUnit() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 unit = new CTX2(persons, names);

        List<String> fired = new ArrayList<>();
        RuleBase<CTX2> ruleBase = new RuleBase<>();
        RuleBuilder<CTX2> builder = new RuleBuilder<>();
        RuleBaseModifier.with(ruleBase)
                        .apply(RuleBaseModifier.changeSet()
                                               .selectPackage("org.domain").selectUnit("Unit1")
                                               .add(builder.rule("r1")
                                                           .from(CTX2::persons)
                                                           .ifn((ctx, p) -> fired.add("r1:" + p.name())))
                                               .add(builder.rule("r2")
                                                           .from(CTX2::persons)
                                                           .join(CTX2::names)
                                                           .ifn((ctx, p, n) -> fired.add("r2:" + p.name() + ":" + n))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", unit);

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).containsExactly("r1:Darth");

        names.add("Vader");
        assertThat(fired).containsExactlyInAnyOrder("r1:Darth", "r2:Darth:Vader");
    }
}
