/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
package org.drools.core;

import org.drools.core.util.AbstractDoubleLinkedNode;

/**
 * Vol2 from-node — outer class is a stub pending vol2 data source integration.
 * TODO #6650: implement vol2 FromNode (DataSource-aware, no BetaConstraints dependency)
 * Inner FromMemory is needed by SegmentMemory prototype machinery.
 */
public class FromNode<T extends FromNode.FromMemory> extends BaseNode implements MemoryFactory<T> {

    public FromNode() { }

    public FromNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    @Override
    @SuppressWarnings("unchecked")
    public T createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) {
        return (T) new FromMemory();
    }

    public static class FromMemory extends AbstractDoubleLinkedNode<Memory> implements SegmentNodeMemory {

        private SegmentMemory memory;
        private long          nodePosMaskBit;

        @Override
        public int getNodeType() { return 0; }

        @Override
        public SegmentMemory getSegmentMemory() { return memory; }

        @Override
        public void setSegmentMemory(SegmentMemory smem) { this.memory = smem; }

        @Override
        public long getNodePosMaskBit() { return nodePosMaskBit; }

        @Override
        public void setNodePosMaskBit(long segmentPos) { this.nodePosMaskBit = segmentPos; }

        @Override
        public void setNodeDirtyWithoutNotify() {
            if (memory != null) memory.updateDirtyNodeMask(nodePosMaskBit);
        }

        @Override
        public void setNodeCleanWithoutNotify() {
            if (memory != null) memory.updateCleanNodeMask(nodePosMaskBit);
        }

        @Override
        public void reset() { }
    }
}
