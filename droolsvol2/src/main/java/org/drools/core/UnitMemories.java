package org.drools.core;

import java.util.Arrays;

/**
 * Array-backed node memory store for one UnitInstance.
 * Indexed by node ID — O(1) get-or-create, no Map overhead.
 * IDs are compact and sequential from the IdGenerator; array grows on demand.
 */
public class UnitMemories {

    private Object[] memories = new Object[16];

    @SuppressWarnings("unchecked")
    public JoinMemory getOrCreateJoinMemory(int nodeId) {
        ensureCapacity(nodeId);
        if (memories[nodeId] == null) {
            memories[nodeId] = new JoinMemory(nodeId);
        }
        return (JoinMemory) memories[nodeId];
    }

    private void ensureCapacity(int nodeId) {
        if (nodeId >= memories.length) {
            memories = Arrays.copyOf(memories, Math.max(nodeId + 1, memories.length * 2));
        }
    }
}
