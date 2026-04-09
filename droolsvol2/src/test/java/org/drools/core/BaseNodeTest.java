package org.drools.core;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Ported from vol1 org.drools.core.reteoo.BaseNodeTest — adapted for vol2 constructors.
 * Vol1 used BaseNode(id, RuleBasePartitionId); vol2 uses BaseNode(id, pathIndex, objectIndex).
 */
public class BaseNodeTest {

    @Test
    public void testBaseNodeStoresId() {
        AlphaNode node = new AlphaNode(10, 0, 0);
        assertThat(node.getId()).isEqualTo(10);

        node = new AlphaNode(155, 0, 0);
        assertThat(node.getId()).isEqualTo(155);
    }

    @Test
    public void testBaseNodeStoresPathAndObjectIndex() {
        AlphaNode node = new AlphaNode(1, 3, 2);
        assertThat(node.getPathIndex()).isEqualTo(3);
        assertThat(node.getObjectIndex()).isEqualTo(2);
    }

    @Test
    public void testObjectTypeNodeStoresObjectType() {
        ObjectTypeNode otn = new ObjectTypeNode(5, 0, 0);
        org.drools.base.base.ClassObjectType objectType =
                new org.drools.base.base.ClassObjectType(String.class);
        otn.setObjectType(objectType);

        assertThat(otn.getId()).isEqualTo(5);
        assertThat(otn.getObjectType()).isEqualTo(objectType);
    }
}
