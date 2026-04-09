package org.drools.core;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Ported from vol1 org.drools.core.reteoo.BetaNodeTest.
 *
 * Vol1 used MockTupleSource, MockObjectSource, RightInputAdapterNode —
 * all vol1-specific. Vol2 uses AlphaNode and LeftInputAdapterNode directly
 * as shared input nodes.
 */
public class BetaNodeTest {

    @Test
    public void testEqualsObject() {
        // Shared inputs — same node instances used for multiple beta nodes
        AlphaNode           sharedLeft  = new AlphaNode(1, 0, 0);
        ObjectTypeNode      sharedRight = new ObjectTypeNode(2, 0, 0);

        JoinNode j1 = new JoinNode(10, 1, 1);
        j1.setLeftInput(sharedLeft);
        j1.setRightInput(sharedRight);

        JoinNode j2 = new JoinNode(20, 1, 1);  // different ID, same inputs
        j2.setLeftInput(sharedLeft);
        j2.setRightInput(sharedRight);

        NotNode n1 = new NotNode(30, 1, 1);
        n1.setLeftInput(sharedLeft);
        n1.setRightInput(sharedRight);

        NotNode n2 = new NotNode(40, 1, 1);    // different ID, same inputs
        n2.setLeftInput(sharedLeft);
        n2.setRightInput(sharedRight);

        // Same type + same inputs → equal
        assertThat(j1).isEqualTo(j1);
        assertThat(j2).isEqualTo(j2);
        assertThat(j1).isEqualTo(j2);
        assertThat(n1).isEqualTo(n1);
        assertThat(n2).isEqualTo(n2);
        assertThat(n1).isEqualTo(n2);

        // Different type → not equal (even with same inputs)
        assertThat(j1).isNotEqualTo(n1);
        assertThat(j1).isNotEqualTo(n2);
        assertThat(n1).isNotEqualTo(j1);
        assertThat(n1).isNotEqualTo(j2);
    }

    @Test
    public void testDifferentInputsNotEqual() {
        AlphaNode left1 = new AlphaNode(1, 0, 0);
        AlphaNode left2 = new AlphaNode(2, 0, 0);  // different ID
        ObjectTypeNode right = new ObjectTypeNode(3, 0, 0);

        JoinNode j1 = new JoinNode(10, 1, 1);
        j1.setLeftInput(left1);
        j1.setRightInput(right);

        JoinNode j2 = new JoinNode(20, 1, 1);
        j2.setLeftInput(left2);  // different left input
        j2.setRightInput(right);

        assertThat(j1).isNotEqualTo(j2);
    }

    @Test
    public void testHashCodeConsistentWithEquals() {
        AlphaNode      sharedLeft  = new AlphaNode(1, 0, 0);
        ObjectTypeNode sharedRight = new ObjectTypeNode(2, 0, 0);

        JoinNode j1 = new JoinNode(10, 1, 1);
        j1.setLeftInput(sharedLeft);
        j1.setRightInput(sharedRight);

        JoinNode j2 = new JoinNode(20, 1, 1);
        j2.setLeftInput(sharedLeft);
        j2.setRightInput(sharedRight);

        assertThat(j1).isEqualTo(j2);
        assertThat(j1.hashCode()).isEqualTo(j2.hashCode());
    }
}
