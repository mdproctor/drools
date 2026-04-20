package org.drools.core;

import java.util.Arrays;

/**
 * Vol2 non-concurrent implementation of NodeMemories.
 * Array-backed: memories[node.getMemoryId()] — O(1) get-or-create.
 * Single-threaded (vol2 core is not thread-safe by design).
 */
public class SimpleNodeMemories implements NodeMemories {

    private Memory[] memories;

    public SimpleNodeMemories() {
        this.memories = new Memory[16];
    }

    @Override
    @SuppressWarnings("unchecked")
    public <T extends Memory> T getNodeMemory(MemoryFactory<T> node) {
        int id = node.getMemoryId();
        ensureCapacity(id);
        if (memories[id] == null) {
            memories[id] = node.createMemory(null, null);
        }
        return (T) memories[id];
    }

    @Override
    public void clearNodeMemory(MemoryFactory node) {
        int id = node.getMemoryId();
        if (id < memories.length) memories[id] = null;
    }

    @Override
    public void clear() {
        memories = new Memory[16];
    }

    @Override
    public Memory peekNodeMemory(int memoryId) {
        return memoryId < memories.length ? memories[memoryId] : null;
    }

    @Override
    public int length() {
        return memories.length;
    }

    @Override
    public void resetAllMemories() {
        for (Memory m : memories) {
            if (m != null) m.reset();
        }
    }

    private void ensureCapacity(int id) {
        if (id >= memories.length) {
            memories = Arrays.copyOf(memories, Math.max(id + 1, memories.length * 2));
        }
    }
}
