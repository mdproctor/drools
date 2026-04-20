package org.drools.core;

import org.junit.jupiter.api.Test;
import static org.assertj.core.api.Assertions.assertThat;

/** Unit tests for NodeMemories — array-backed, O(1) get-or-create by node ID. */
public class UnitMemoriesTest {

    @Test
    public void testGetOrCreateReturnsNewInstanceOnFirstAccess() {
        UnitMemories mem = new UnitMemories();
        JoinMemory jm = mem.getOrCreateJoinMemory(5);
        assertThat(jm).isNotNull();
        assertThat(jm.getNodeId()).isEqualTo(5);
    }

    @Test
    public void testGetOrCreateReturnsSameInstanceOnSubsequentAccess() {
        UnitMemories mem = new UnitMemories();
        JoinMemory jm1 = mem.getOrCreateJoinMemory(3);
        JoinMemory jm2 = mem.getOrCreateJoinMemory(3);
        assertThat(jm1).isSameAs(jm2);
    }

    @Test
    public void testIndependentSlotsDoNotInterfere() {
        UnitMemories mem = new UnitMemories();
        JoinMemory jm1 = mem.getOrCreateJoinMemory(2);
        JoinMemory jm2 = mem.getOrCreateJoinMemory(7);
        assertThat(jm1).isNotSameAs(jm2);
        assertThat(jm1.getNodeId()).isEqualTo(2);
        assertThat(jm2.getNodeId()).isEqualTo(7);
    }

    @Test
    public void testGrowsBeyondInitialCapacity() {
        UnitMemories mem = new UnitMemories();
        // IDs are compact — force array growth
        JoinMemory jm = mem.getOrCreateJoinMemory(100);
        assertThat(jm.getNodeId()).isEqualTo(100);
        assertThat(mem.getOrCreateJoinMemory(100)).isSameAs(jm);
    }
}
