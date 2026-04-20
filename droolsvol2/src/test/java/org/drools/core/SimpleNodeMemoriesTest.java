package org.drools.core;

import org.junit.jupiter.api.Test;
import static org.assertj.core.api.Assertions.assertThat;

/** Unit tests for SimpleNodeMemories — array-backed, O(1) get-or-create by node ID. */
public class SimpleNodeMemoriesTest {

    private MemoryFactory<JoinMemory> nodeFactory(int memoryId) {
        return new MemoryFactory<JoinMemory>() {
            public JoinMemory createMemory(RuleBaseConfiguration c, ReteEvaluator r) {
                return new JoinMemory(memoryId);
            }
            public int getMemoryId() { return memoryId; }
        };
    }

    @Test
    public void testGetOrCreateReturnsNewInstanceOnFirstAccess() {
        SimpleNodeMemories mem = new SimpleNodeMemories();
        JoinMemory jm = mem.getNodeMemory(nodeFactory(5));
        assertThat(jm).isNotNull();
        assertThat(jm.getNodeId()).isEqualTo(5);
    }

    @Test
    public void testGetOrCreateReturnsSameInstanceOnSubsequentAccess() {
        SimpleNodeMemories mem = new SimpleNodeMemories();
        JoinMemory jm1 = mem.getNodeMemory(nodeFactory(3));
        JoinMemory jm2 = mem.getNodeMemory(nodeFactory(3));
        assertThat(jm1).isSameAs(jm2);
    }

    @Test
    public void testIndependentSlotsDoNotInterfere() {
        SimpleNodeMemories mem = new SimpleNodeMemories();
        JoinMemory jm1 = mem.getNodeMemory(nodeFactory(2));
        JoinMemory jm2 = mem.getNodeMemory(nodeFactory(7));
        assertThat(jm1).isNotSameAs(jm2);
        assertThat(jm1.getNodeId()).isEqualTo(2);
        assertThat(jm2.getNodeId()).isEqualTo(7);
    }

    @Test
    public void testGrowsBeyondInitialCapacity() {
        SimpleNodeMemories mem = new SimpleNodeMemories();
        // IDs are compact — force array growth
        JoinMemory jm = mem.getNodeMemory(nodeFactory(100));
        assertThat(jm.getNodeId()).isEqualTo(100);
        assertThat(mem.getNodeMemory(nodeFactory(100))).isSameAs(jm);
    }
}
