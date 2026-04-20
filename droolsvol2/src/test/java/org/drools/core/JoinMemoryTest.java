package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.api.data.DataStore;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/** Unit tests for JoinMemory — the per-join-node left/right handle store. */
public class JoinMemoryTest {

    private ObjectHandle<Person> handle(String name) {
        PropagatingDataStore<Person> store = new PropagatingDataStore<>(0, new TypeIndexer<>());
        return store.add(new Person(name, 30, "London"));
    }

    @Test
    public void testStartsEmpty() {
        JoinMemory mem = new JoinMemory();
        assertThat(mem.getLeftHandles()).isEmpty();
        assertThat(mem.getRightHandles()).isEmpty();
    }

    @Test
    public void testAddLeft() {
        JoinMemory mem = new JoinMemory();
        ObjectHandle<Person> h = handle("Darth");
        mem.addLeft(h);
        assertThat(mem.getLeftHandles()).containsExactly(h);
        assertThat(mem.getRightHandles()).isEmpty();
    }

    @Test
    public void testAddRight() {
        JoinMemory mem = new JoinMemory();
        ObjectHandle<Person> h = handle("Darth");
        mem.addRight(h);
        assertThat(mem.getRightHandles()).containsExactly(h);
        assertThat(mem.getLeftHandles()).isEmpty();
    }

    @Test
    public void testRemoveLeft() {
        JoinMemory mem = new JoinMemory();
        ObjectHandle<Person> h1 = handle("Darth");
        ObjectHandle<Person> h2 = handle("Luke");
        mem.addLeft(h1);
        mem.addLeft(h2);
        mem.removeLeft(h1);
        assertThat(mem.getLeftHandles()).containsExactly(h2);
    }

    @Test
    public void testRemoveRight() {
        JoinMemory mem = new JoinMemory();
        ObjectHandle<Person> h1 = handle("Darth");
        ObjectHandle<Person> h2 = handle("Luke");
        mem.addRight(h1);
        mem.addRight(h2);
        mem.removeRight(h2);
        assertThat(mem.getRightHandles()).containsExactly(h1);
    }
}
