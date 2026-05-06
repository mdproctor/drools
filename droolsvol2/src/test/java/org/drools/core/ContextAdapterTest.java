package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.api.data.DataStore;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;

public class ContextAdapterTest {

    @Test
    public void testPropagation() {
        PropagatingDataStore<Person> persons = new PropagatingDataStore(0, new TypeIndexer<>());
        PropagatingDataStore<City> cities   = new PropagatingDataStore(1, new TypeIndexer<>());

        record CTX1(DataStore<Person> persons, DataStore<City> cities) {}

        Router<CTX1> router = new Router<>(2);

        UnitInstance<CTX1> unit = new UnitInstance<>(new CTX1(persons, cities));
        router.addContext(unit);

        ContextRouterAdapter<DataStore<Person>, CTX1, Person> ctxAdapter0 = new ContextRouterAdapter<>(0, router);
        ContextRouterAdapter<DataStore<City>,   CTX1, City>   ctxAdapter1 = new ContextRouterAdapter<>(1, router);
        persons.subscribe(ctxAdapter0);
        cities.subscribe(ctxAdapter1);

        RecordingUnitProcessor<CTX1, Object> recorder0 = new RecordingUnitProcessor<>(0);
        RecordingUnitProcessor<CTX1, Object> recorder1 = new RecordingUnitProcessor<>(1);
        router.subscribe(0, recorder0);
        router.subscribe(1, recorder1);

        List<LogEntry> list0 = recorder0.getLog();
        List<LogEntry> list1 = recorder1.getLog();

        ObjectHandle<Person> h1 = persons.add(new Person("Darth", 100, "London"));
        assertThat(list0).hasSize(1);
        assertThat(list0.get(0).action()).isEqualTo("add");
        assertThat(list0.get(0).object()).isSameAs(h1.getObject());

        persons.update(h1, new Person("Darth", 210, "New York"));
        assertThat(list0).hasSize(2);
        assertThat(list0.get(1).action()).isEqualTo("update");
        assertThat(list0.get(1).object()).isSameAs(h1.getObject());

        persons.remove(h1);
        assertThat(list0).hasSize(3);
        assertThat(list0.get(2).action()).isEqualTo("remove");
        assertThat(list0.get(2).object()).isSameAs(h1.getObject());

        ObjectHandle<City> c1 = cities.add(new City("London"));
        assertThat(list1).hasSize(1);
        assertThat(list1.get(0).action()).isEqualTo("add");
        assertThat(list1.get(0).object()).isSameAs(c1.getObject());

        cities.update(c1, new City("New York"));
        assertThat(list1).hasSize(2);
        assertThat(list1.get(1).action()).isEqualTo("update");
        assertThat(list1.get(1).object()).isSameAs(c1.getObject());

        cities.remove(c1);
        assertThat(list1).hasSize(3);
        assertThat(list1.get(2).action()).isEqualTo("remove");
        assertThat(list1.get(2).object()).isSameAs(c1.getObject());

        assertThat(list0).hasSize(3);
    }

    @Test
    public void testAddRemoveMultipleContexts() {
        PropagatingDataStore<Person> persons1 = new PropagatingDataStore(0, new TypeIndexer<>());
        PropagatingDataStore<Person> persons2 = new PropagatingDataStore(1, new TypeIndexer<>());
        PropagatingDataStore<City>   cities   = new PropagatingDataStore(2, new TypeIndexer<>());
        List<String> list1 = new ArrayList<>();
        List<String> list2 = new ArrayList<>();

        record CTX1(String name, DataStore<Person> persons, DataStore<City> cities, List<String> list) {}

        Router<CTX1> router = new Router<>(2);

        UnitInstance<CTX1> unit1 = new UnitInstance<>(new CTX1("ctx1", persons1, cities, list1));
        UnitInstance<CTX1> unit2 = new UnitInstance<>(new CTX1("ctx2", persons2, cities, list2));
        Handle unit1H = router.addContext(unit1);
        Handle unit2H = router.addContext(unit2);

        ContextRouterAdapter<DataStore<Person>, CTX1, Person> ctxAdapter0 = new ContextRouterAdapter<>(0, router);
        ContextRouterAdapter<DataStore<City>,   CTX1, City>   ctxAdapter1 = new ContextRouterAdapter<>(1, router);
        persons1.subscribe(ctxAdapter0);
        cities.subscribe(ctxAdapter1);

        Action1<CTX1, Person> pfn = new Action1<>((ctx, o) -> ctx.context().list().add(ctx.context().name() + ":" + o.name()));
        Action1<CTX1, City>   cfn = new Action1<>((ctx, o) -> ctx.context().list().add(ctx.context().name() + ":" + o.name()));
        router.subscribe(0, pfn);
        router.subscribe(1, cfn);

        persons1.add(new Person("Darth", 100, "London"));
        assertThat(unit1.getContext().context().list()).containsExactly("ctx1:Darth");
        assertThat(unit2.getContext().context().list()).containsExactly("ctx2:Darth");

        router.removeContext(unit1H);
        persons1.add(new Person("Yoda", 300, "Paris"));
        assertThat(unit1.getContext().context().list()).containsExactly("ctx1:Darth");
        assertThat(unit2.getContext().context().list()).containsExactly("ctx2:Darth", "ctx2:Yoda");

        unit1H = router.addContext(unit1);
        persons1.add(new Person("Luke", 30, "Barcelona"));
        assertThat(unit1.getContext().context().list()).containsExactly("ctx1:Darth", "ctx1:Luke");
        assertThat(unit2.getContext().context().list()).containsExactly("ctx2:Darth", "ctx2:Yoda", "ctx2:Luke");
    }
}
