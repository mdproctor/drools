package org.drools.core;

import org.drools.api.data.DataProcessor;
import org.drools.api.data.DataStore;
import org.drools.api.data.ObjectHandle;
import org.drools.core.RuleBuilder.RuleDescriptor;
import org.drools.core.function.Consumer2;
import org.drools.core.function.Consumer3;
import static org.assertj.core.api.Assertions.assertThatThrownBy;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the vol2 evaluation engine.
 * Join and propagation logic lives in evaluation-layer DataProcessors,
 * never on network nodes (BaseNode or subclasses).
 */
public class RuleProapgationAndExecutionTest {

    record DS1(DataStore<Person> persons) {}
    record DS2(DataStore<Person> persons, DataStore<String> names) {}

    // --- DSL descriptor stores function refs and consequence ---

    @Test
    public void testDescriptorStoresSourcesAndConsequence() {
        List<String> fired = new ArrayList<>();
        RuleDescriptor<DS1> desc = new RuleBuilder<DS1>()
                .rule("r1")
                .from(DS1::persons)
                .ifn((ctx, p) -> fired.add(p.name()))
                .descriptor();

        assertThat(desc.getSources()).hasSize(1);
        assertThat(desc.getConsequence()).isInstanceOf(Consumer2.class);
    }

    @Test
    public void testDescriptorJoinStoresSourcesAndConsequence() {
        List<String> fired = new ArrayList<>();
        RuleDescriptor<DS2> desc = new RuleBuilder<DS2>()
                .rule("r1")
                .from(DS2::persons)
                .join(DS2::names)
                .ifn((ctx, p, n) -> fired.add(p.name() + ":" + n))
                .descriptor();

        assertThat(desc.getSources()).hasSize(2);
        assertThat(desc.getConsequence()).isInstanceOf(Consumer3.class);
    }

    // --- Full flow: RuleBase → UnitDescriptor → UnitInstance ---

    @Test
    public void testRuleBaseJoinViaUnitDescriptor() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        DS2 ds = new DS2(persons, names);

        RuleBase<DS2> ruleBase = new RuleBase<>();
        RuleBuilder<DS2> builder = new RuleBuilder<>();

        List<String> fired = new ArrayList<>();
        RuleBaseModifier.with(ruleBase)
                        .apply(RuleBaseModifier.changeSet()
                                               .selectPackage("org.domain").selectUnit("Unit1")
                                               .add(builder.rule("r1")
                                                           .from(DS2::persons)
                                                           .join(DS2::names)
                                                           .ifn((ctx, p, n) -> fired.add(p.name() + ":" + n))));

        UnitInstantiator.from(ruleBase).createInstance("org.domain.Unit1", ds);

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).isEmpty();

        names.add("Vader");
        assertThat(fired).containsExactly("Darth:Vader");
    }

    // --- UnitInstance end-to-end via DSL ---

    @Test
    public void testUnitInstanceSinglePattern() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        DS1 ds = new DS1(persons);

        List<String> fired = new ArrayList<>();
        RuleDescriptor<DS1> desc = new RuleBuilder<DS1>()
                .rule("r1")
                .from(DS1::persons)
                .ifn((ctx, p) -> fired.add(p.name()))
                .descriptor();

        new UnitInstance<>(ds, desc);

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).containsExactly("Darth");

        persons.add(new Person("Yoda", 900, "Dagobah"));
        assertThat(fired).containsExactly("Darth", "Yoda");
    }

    @Test
    public void testUnitInstanceTwoPatternJoin() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());
        DS2 ds = new DS2(persons, names);

        List<String> fired = new ArrayList<>();
        RuleDescriptor<DS2> desc = new RuleBuilder<DS2>()
                .rule("r1")
                .from(DS2::persons)
                .join(DS2::names)
                .ifn((ctx, p, n) -> fired.add(p.name() + ":" + n))
                .descriptor();

        new UnitInstance<>(ds, desc);

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).isEmpty();

        names.add("Vader");
        assertThat(fired).containsExactly("Darth:Vader");
    }

    // --- Consequence-only rule (no join) ---

    @Test
    public void testConsequenceOnlyFires() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());

        Router<DS1> router = new Router<>(1);
        ContextPojoDS<DS1> ctx = new ContextPojoDS<>(new DS1(persons));
        router.addContext(ctx);

        persons.subscribe(new ContextRouterAdapter<>(0, router));

        List<String> fired = new ArrayList<>();
        router.subscribe(0, new Action1<DS1, Person>((c, p) -> fired.add(p.name())));

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).containsExactly("Darth");

        persons.add(new Person("Yoda", 900, "Dagobah"));
        assertThat(fired).containsExactly("Darth", "Yoda");
    }

    // --- Simple two-pattern join ---

    @Test
    public void testSimpleJoinFires() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());

        Router<DS2> router = new Router<>(2);
        ContextPojoDS<DS2> ctx = new ContextPojoDS<>(new DS2(persons, names));
        router.addContext(ctx);

        persons.subscribe(new ContextRouterAdapter<>(0, router));
        names.subscribe(new ContextRouterAdapter<>(1, router));

        List<String> fired = new ArrayList<>();

        // Beta memory — evaluation-layer state, keyed externally by node ID in a real engine
        List<ObjectHandle<Person>> leftMem  = new ArrayList<>();
        List<ObjectHandle<String>> rightMem = new ArrayList<>();

        // Left handler: store handle, probe right memory, fire on match
        router.subscribe(0, new DataProcessor<DS2, Person>() {
            public void add(Context<DS2> c, ObjectHandle<Person> h) {
                leftMem.add(h);
                rightMem.forEach(rh -> fired.add(h.getObject().name() + ":" + rh.getObject()));
            }
            public void update(Context<DS2> c, ObjectHandle<Person> h) { }
            public void remove(Context<DS2> c, ObjectHandle<Person> h) { leftMem.remove(h); }
        });

        // Right handler: store handle, probe left memory, fire on match
        router.subscribe(1, new DataProcessor<DS2, String>() {
            public void add(Context<DS2> c, ObjectHandle<String> h) {
                rightMem.add(h);
                leftMem.forEach(lh -> fired.add(lh.getObject().name() + ":" + h.getObject()));
            }
            public void update(Context<DS2> c, ObjectHandle<String> h) { }
            public void remove(Context<DS2> c, ObjectHandle<String> h) { rightMem.remove(h); }
        });

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).isEmpty();  // no names yet

        names.add("Vader");
        assertThat(fired).containsExactly("Darth:Vader");
    }

    @Test
    public void testJoinWithMultipleFactsFires() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore<>(0, new TypeIndexer<>());
        PropagatingDataStore<String> names   = new PropagatingDataStore<>(1, new TypeIndexer<>());

        Router<DS2> router = new Router<>(2);
        router.addContext(new ContextPojoDS<>(new DS2(persons, names)));

        persons.subscribe(new ContextRouterAdapter<>(0, router));
        names.subscribe(new ContextRouterAdapter<>(1, router));

        List<String> fired = new ArrayList<>();
        List<ObjectHandle<Person>> leftMem  = new ArrayList<>();
        List<ObjectHandle<String>> rightMem = new ArrayList<>();

        router.subscribe(0, new DataProcessor<DS2, Person>() {
            public void add(Context<DS2> c, ObjectHandle<Person> h) {
                leftMem.add(h);
                rightMem.forEach(rh -> fired.add(h.getObject().name() + ":" + rh.getObject()));
            }
            public void update(Context<DS2> c, ObjectHandle<Person> h) { }
            public void remove(Context<DS2> c, ObjectHandle<Person> h) { leftMem.remove(h); }
        });

        router.subscribe(1, new DataProcessor<DS2, String>() {
            public void add(Context<DS2> c, ObjectHandle<String> h) {
                rightMem.add(h);
                leftMem.forEach(lh -> fired.add(lh.getObject().name() + ":" + h.getObject()));
            }
            public void update(Context<DS2> c, ObjectHandle<String> h) { }
            public void remove(Context<DS2> c, ObjectHandle<String> h) { rightMem.remove(h); }
        });

        names.add("Skywalker");
        names.add("Vader");

        persons.add(new Person("Luke", 20, "Tatooine"));
        assertThat(fired).containsExactlyInAnyOrder("Luke:Skywalker", "Luke:Vader");

        persons.add(new Person("Darth", 100, "London"));
        assertThat(fired).containsExactlyInAnyOrder(
                "Luke:Skywalker", "Luke:Vader", "Darth:Skywalker", "Darth:Vader");
    }
}
