package org.drools.core;

import org.drools.api.data.DataStore;
import org.drools.api.data.ObjectHandle;
import org.drools.core.RuleBuilder.RuleDescriptor;
import org.drools.core.function.Consumer2;
import org.drools.core.function.Consumer3;
import org.drools.core.function.Predicate2;
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
        CTX1 ctx1 = new CTX1(persons);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX1> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(new RuleBuilder<CTX1>().rule("r1")
                                .from(CTX1::persons)
                                .ifn((ctx, p) -> fired.add(p.name()))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx1);

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).containsExactly("Darth");

        persons.add(new Person("Yoda", 900, "Dagobah"));
        assertThat(fired).containsExactly("Darth", "Yoda");
    }

    // --- Two-pattern join ---

    @Test
    public void testJoinIfnFires() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 ctx2 = new CTX2(persons, names);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX2> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(new RuleBuilder<CTX2>().rule("r1")
                                .from(CTX2::persons)
                                .join(CTX2::names)
                                .ifn((ctx, p, n) -> fired.add(p.name() + ":" + n))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx2);

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).isEmpty();

        names.add("Vader");
        assertThat(fired).containsExactly("Darth:Vader");
    }

    @Test
    public void testJoinCrossProductFires() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 ctx2 = new CTX2(persons, names);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX2> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(new RuleBuilder<CTX2>().rule("r1")
                                .from(CTX2::persons)
                                .join(CTX2::names)
                                .ifn((ctx, p, n) -> fired.add(p.name() + ":" + n))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx2);

        names.add("Skywalker");
        names.add("Vader");
        persons.add(new Person("Luke", 20, "Tatooine"));
        assertThat(fired).containsExactlyInAnyOrder("Luke:Skywalker", "Luke:Vader");

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).containsExactlyInAnyOrder(
                "Luke:Skywalker", "Luke:Vader", "Darth:Skywalker", "Darth:Vader");
    }

    // --- JoinMemory keyed by JoinNode id, NodeMemories array-backed ---

    @Test
    public void testJoinMemoryKeyedByNodeId() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 ctx2 = new CTX2(persons, names);
        RuleBase<CTX2> ruleBase = new RuleBase<>();
        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(new RuleBuilder<CTX2>().rule("r1")
                                .from(CTX2::persons).join(CTX2::names)
                                .ifn((ctx, p, n) -> {})));

        UnitInstance<CTX2> ui = UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx2);

        // JoinMemory in NodeMemories must be keyed by the JoinNode's id from the topology
        int joinNodeId = findJoinNodeId(ruleBase);
        assertThat(joinNodeId).isGreaterThan(0);
        JoinMemory mem = ui.getNodeMemories().getNodeMemory(findJoinNode(ruleBase));
        assertThat(mem.getNodeId()).isEqualTo(joinNodeId);

        persons.add(new Person("Darth", 100, "London"));
        // after add, left side should be in the memory keyed by the join node id
        assertThat(mem.getLeftHandles()).hasSize(1);
    }

    private JoinNode findJoinNode(RuleBase<?> ruleBase) {
        return findJoinNode(ruleBase.getRete());
    }

    private JoinNode findJoinNode(BaseNode node) {
        if (node instanceof JoinNode jn) return jn;
        for (BaseNode out : node.getOutputs()) {
            JoinNode found = findJoinNode(out);
            if (found != null) return found;
        }
        return null;
    }

    private int findJoinNodeId(RuleBase<?> ruleBase) {
        JoinNode jn = findJoinNode(ruleBase);
        return jn != null ? jn.getId() : -1;
    }



    // --- Step 2: update and remove ---

    @Test
    public void testUpdateLeftSideRefires() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 ctx2 = new CTX2(persons, names);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX2> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(new RuleBuilder<CTX2>().rule("r1")
                                .from(CTX2::persons)
                                .join(CTX2::names)
                                .ifn((ctx, p, n) -> fired.add(p.name() + ":" + n))));

        UnitInstance<CTX2> ui = UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx2);

        ObjectHandle<Person> darth = ui.add(persons, new Person("Darth", 100, "London"));
        ui.add(names, "Vader");
        assertThat(fired).containsExactly("Darth:Vader");

        ui.update(persons, darth, new Person("Luke", 20, "Tatooine"));
        assertThat(fired).containsExactly("Darth:Vader", "Luke:Vader");
    }

    @Test
    public void testRemoveLeftStopsMatching() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 ctx2 = new CTX2(persons, names);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX2> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(new RuleBuilder<CTX2>().rule("r1")
                                .from(CTX2::persons)
                                .join(CTX2::names)
                                .ifn((ctx, p, n) -> fired.add(p.name() + ":" + n))));

        UnitInstance<CTX2> ui = UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx2);

        ObjectHandle<Person> darth = ui.add(persons, new Person("Darth", 100, "London"));
        ui.add(names, "Vader");
        assertThat(fired).containsExactly("Darth:Vader");

        ui.remove(persons, darth);
        ui.add(names, "Maul");
        assertThat(fired).containsExactly("Darth:Vader");
    }

    // --- Step 3: filter ---

    @Test
    public void testFilterBlocksNonMatchingSinglePattern() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        CTX1 ctx1 = new CTX1(persons);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX1> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(new RuleBuilder<CTX1>().rule("r1")
                                .from(CTX1::persons)
                                .filter((ctx, p) -> p.age() > 18)
                                .ifn((ctx, p) -> fired.add(p.name()))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx1);

        persons.add(new Person("Child", 10, "London"));
        assertThat(fired).isEmpty();

        persons.add(new Person("Adult", 25, "London"));
        assertThat(fired).containsExactly("Adult");
    }

    @Test
    public void testFilterOnLeftSideOfJoin() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 ctx2 = new CTX2(persons, names);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX2> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(new RuleBuilder<CTX2>().rule("r1")
                                .from(CTX2::persons)
                                .filter((ctx, p) -> p.age() > 18)
                                .join(CTX2::names)
                                .ifn((ctx, p, n) -> fired.add(p.name() + ":" + n))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx2);

        persons.add(new Person("Child", 10, "London"));
        names.add("Vader");
        assertThat(fired).isEmpty();

        persons.add(new Person("Adult", 25, "London"));
        assertThat(fired).containsExactly("Adult:Vader");
    }

    // --- Step 1: fn (deferred head) and Agenda ---

    @Test
    public void testFnFiresDeferredViaUnitAdd() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        CTX1 ctx1 = new CTX1(persons);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX1> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(new RuleBuilder<CTX1>().rule("r1")
                                .from(CTX1::persons)
                                .fn((ctx, p) -> fired.add(p.name()))));

        UnitInstance<CTX1> ui = UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx1);

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).isEmpty();

        ui.add(persons, new Person("Luke", 20, "Tatooine"));
        assertThat(fired).containsExactly("Darth", "Luke"); // both drained: Darth was queued, Luke just added
    }

    @Test
    public void testFnJoinFiresDeferred() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 ctx2 = new CTX2(persons, names);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX2> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(new RuleBuilder<CTX2>().rule("r1")
                                .from(CTX2::persons)
                                .join(CTX2::names)
                                .fn((ctx, p, n) -> fired.add(p.name() + ":" + n))));

        UnitInstance<CTX2> ui = UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx2);

        ui.add(persons, new Person("Darth", 100, "London"));
        assertThat(fired).isEmpty();

        ui.add(names, "Vader");
        assertThat(fired).containsExactly("Darth:Vader");
    }

    @Test
    public void testMultipleRulesInUnit() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX2 ctx2 = new CTX2(persons, names);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX2> ruleBase = new RuleBase<>();
        RuleBuilder<CTX2> builder = new RuleBuilder<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("Unit1")
                        .add(builder.rule("r1")
                                .from(CTX2::persons)
                                .ifn((ctx, p) -> fired.add("r1:" + p.name())))
                        .add(builder.rule("r2")
                                .from(CTX2::persons)
                                .join(CTX2::names)
                                .ifn((ctx, p, n) -> fired.add("r2:" + p.name() + ":" + n))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ctx2);

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).containsExactly("r1:Darth");

        names.add("Vader");
        assertThat(fired).containsExactlyInAnyOrder("r1:Darth", "r2:Darth:Vader");
    }

    // =========================================================================
    // Lambda not()/exists() scopes
    // =========================================================================

    record CTX3(DataStore<Person> persons, DataStore<String> blocklist) {}

    @Test
    public void testLambdaNotScopeBlocksWhenScopeHasMatch() {
        // not(scope): rule fires for each person whose name is NOT on the blocklist.
        // Alice is on the blocklist → blocked. Bob is not → fires.
        PropagatingDataStore<Person> persons   = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> blocklist = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX3 ctx3 = new CTX3(persons, blocklist);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX3> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("U1")
                        .add(new RuleBuilder<CTX3>().rule("notScope")
                                .from(CTX3::persons)
                                .not(scope -> scope
                                        .join(CTX3::blocklist)
                                        .filter((ctx, p, name) -> p.name().equals(name)))
                                .ifn((ctx, p) -> fired.add(p.name()))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.U1", ctx3);

        blocklist.add("Alice");
        persons.add(new Person("Alice", 30, "London"));
        assertThat(fired).isEmpty();  // Alice blocked by not()

        persons.add(new Person("Bob", 25, "Paris"));
        assertThat(fired).containsExactly("Bob");  // Bob not on blocklist → fires
    }

    @Test
    public void testLambdaExistsScopeRequiresMatch() {
        // exists(scope): rule fires for each person whose name IS on the allowlist.
        // Alice is on the allowlist → fires. Bob is not → blocked.
        PropagatingDataStore<Person> persons   = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> allowlist = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX3 ctx3 = new CTX3(persons, allowlist);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX3> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("U2")
                        .add(new RuleBuilder<CTX3>().rule("existsScope")
                                .from(CTX3::persons)
                                .exists(scope -> scope
                                        .join(CTX3::blocklist)
                                        .filter((ctx, p, name) -> p.name().equals(name)))
                                .ifn((ctx, p) -> fired.add(p.name()))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.U2", ctx3);

        allowlist.add("Alice");
        persons.add(new Person("Alice", 30, "London"));
        assertThat(fired).containsExactly("Alice");  // Alice on allowlist → fires

        persons.add(new Person("Bob", 25, "Paris"));
        assertThat(fired).containsExactly("Alice");  // Bob not on allowlist → blocked
    }

    // =========================================================================
    // Lambda not()/exists() — two outer facts (join rule + scope)
    // =========================================================================

    @Test
    public void testLambdaNotScopeTwoOuterFacts() {
        // Rule: from(persons).join(cities) → fires for each (person, city) pair.
        // not(scope): blocks if person's name appears on the blocklist.
        // Both outer facts (p and city) visible in scope filter.
        // Alice on blocklist → all (Alice, *) pairs blocked.
        // Bob not on blocklist → (Bob, *) pairs fire.
        PropagatingDataStore<Person> persons   = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> cities    = new PropagatingDataStore<>(1, new TypeIndexer<>());
        PropagatingDataStore<String> blocklist = new PropagatingDataStore<>(2, new TypeIndexer<>());
        CTX4 ctx4 = new CTX4(persons, cities, blocklist);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX4> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("U3")
                        .add(new RuleBuilder<CTX4>().rule("twoOuterNot")
                                .from(CTX4::persons)
                                .join(CTX4::cities)
                                .not(scope -> scope
                                        .join(CTX4::blocklist)
                                        .filter((ctx, p, city, entry) -> p.name().equals(entry)))
                                .ifn((ctx, p, city) -> fired.add(p.name() + ":" + city))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.U3", ctx4);

        blocklist.add("Alice");
        persons.add(new Person("Alice", 30, "London"));
        cities.add("London");
        assertThat(fired).isEmpty();  // Alice blocked by not (name on blocklist)

        persons.add(new Person("Bob", 25, "Paris"));
        cities.add("Paris");
        // Bob+London and Bob+Paris fire (Bob not on blocklist)
        // Alice+London and Alice+Paris stay blocked
        assertThat(fired).containsExactlyInAnyOrder("Bob:London", "Bob:Paris");
    }

    // =========================================================================
    // Lambda not()/exists() — multiple inner joins in scope
    // =========================================================================

    record CTX4(DataStore<Person> persons, DataStore<String> cities, DataStore<String> blocklist) {}

    @Test
    public void testLambdaNotScopeTwoInnerJoins() {
        // Scope has two inner joins: cities and blocklist.
        // Filter references outer Person + inner city + inner blocklist entry.
        // not(scope): blocks person if scope finds a matching (city, entry) pair where
        //   city == "London" AND entry == p.name().
        // Alice: "London" in cities AND "Alice" in blocklist → scope matches → BLOCKED.
        // Bob: "London" in cities BUT "Bob" not in blocklist → scope empty → PASSES.
        PropagatingDataStore<Person> persons   = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> cities    = new PropagatingDataStore<>(1, new TypeIndexer<>());
        PropagatingDataStore<String> blocklist = new PropagatingDataStore<>(2, new TypeIndexer<>());
        CTX4 ctx4 = new CTX4(persons, cities, blocklist);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX4> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("U3")
                        .add(new RuleBuilder<CTX4>().rule("twoInnerNot")
                                .from(CTX4::persons)
                                .not(scope -> scope
                                        .join(CTX4::cities)
                                        .join(CTX4::blocklist)
                                        .filter((ctx, p, city, entry) ->
                                                city.equals("London") && entry.equals(p.name())))
                                .ifn((ctx, p) -> fired.add(p.name()))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.U3", ctx4);

        cities.add("London");
        blocklist.add("Alice");
        persons.add(new Person("Alice", 30, "London"));
        assertThat(fired).isEmpty();  // Alice blocked: scope matches (London, Alice)

        persons.add(new Person("Bob", 25, "Paris"));
        assertThat(fired).containsExactly("Bob");  // Bob passes: "Bob" not in blocklist
    }

    // =========================================================================
    // Chain-form not()/exists() scopes — global evaluation
    // =========================================================================

    @Test
    public void testChainNotScopeGlobalEval() {
        // Chain form: not().join(source).filter(pred).end()
        // Evaluates globally — if ANY entry on the blocklist triggers the filter,
        // ALL persons are blocked (no per-outer-tuple correlation).
        // Blocklist has "BLOCKED" → global scope matches → all persons blocked.
        PropagatingDataStore<Person> persons   = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> blocklist = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX3 ctx3 = new CTX3(persons, blocklist);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX3> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("U4")
                        .add(new RuleBuilder<CTX3>().rule("chainNot")
                                .from(CTX3::persons)
                                .not()
                                    .join(CTX3::blocklist)
                                    .filter((Object)(Predicate2<Context<CTX3>, String>)(ctx, s) -> s.equals("BLOCKED"))
                                .end()
                                .ifn((ctx, p) -> fired.add(p.name()))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.U4", ctx3);

        persons.add(new Person("Alice", 30, "London"));
        persons.add(new Person("Bob", 25, "Paris"));
        assertThat(fired).containsExactlyInAnyOrder("Alice", "Bob"); // blocklist empty → not() passes

        blocklist.add("BLOCKED");
        // Global: scope now matches → all persons blocked
        assertThat(fired).containsExactlyInAnyOrder("Alice", "Bob"); // already fired, no new firings
    }

    @Test
    public void testChainExistsScopeGlobalEval() {
        // Chain form: exists().join(source).filter(pred).end()
        // Evaluates globally — rule fires only when the exists scope has any match.
        PropagatingDataStore<Person> persons    = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> allowlist  = new PropagatingDataStore<>(1, new TypeIndexer<>());
        CTX3 ctx3 = new CTX3(persons, allowlist);
        List<String> fired = new ArrayList<>();
        RuleBase<CTX3> ruleBase = new RuleBase<>();

        RuleBaseModifier.with(ruleBase).apply(
                RuleBaseModifier.changeSet()
                        .selectPackage("org.domain").selectUnit("U5")
                        .add(new RuleBuilder<CTX3>().rule("chainExists")
                                .from(CTX3::persons)
                                .exists()
                                    .join(CTX3::blocklist)
                                    .filter((Object)(Predicate2<Context<CTX3>, String>)(ctx, s) -> s.equals("OPEN"))
                                .end()
                                .ifn((ctx, p) -> fired.add(p.name()))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.U5", ctx3);

        persons.add(new Person("Alice", 30, "London"));
        assertThat(fired).isEmpty(); // allowlist empty → exists() fails globally → no firing

        allowlist.add("OPEN");
        // exists() now matches globally — but reactive model fires on right-side add,
        // not on left-side retroactively. Alice was added before OPEN.
        // Add Bob after OPEN to verify new persons fire.
        persons.add(new Person("Bob", 25, "Paris"));
        assertThat(fired).containsExactly("Bob");
    }
}
