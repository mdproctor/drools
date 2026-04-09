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

import org.drools.base.reteoo.NodeTypeEnums;
import org.drools.core.util.AbstractDoubleLinkedNode;
import org.drools.core.util.index.TupleList;

/**
 * Vol2 timer node — outer class is a stub pending vol2 timer/async infrastructure.
 * TODO #6650: implement vol2 timer node (replaces vol1 TimerNode + timer-via-container-queue design)
 * The inner TimerNodeMemory is needed by SegmentMemory prototype machinery.
 */
public class TimerNode extends BaseNode implements MemoryFactory<TimerNode.TimerNodeMemory> {

    public TimerNode() { }

    public TimerNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    @Override
    public TimerNodeMemory createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) {
        return new TimerNodeMemory();
    }

    public static class TimerNodeMemory extends AbstractDoubleLinkedNode<Memory> implements SegmentNodeMemory {

        private TupleList     insertOrUpdateLeftTuples;
        private TupleList     deleteLeftTuples;
        private SegmentMemory memory;
        private long          nodePosMaskBit;

        public TimerNodeMemory() {
            this.insertOrUpdateLeftTuples = new TupleList();
            this.deleteLeftTuples = new TupleList();
        }

        public TupleList getInsertOrUpdateLeftTuples() { return this.insertOrUpdateLeftTuples; }
        public TupleList getDeleteLeftTuples() { return this.deleteLeftTuples; }

        @Override
        public int getNodeType() { return NodeTypeEnums.TimerConditionNode; }

        @Override
        public SegmentMemory getSegmentMemory() { return this.memory; }

        @Override
        public void setSegmentMemory(SegmentMemory smem) { this.memory = smem; }

        @Override
        public long getNodePosMaskBit() { return nodePosMaskBit; }

        @Override
        public void setNodePosMaskBit(long segmentPos) { this.nodePosMaskBit = segmentPos; }

        @Override
        public void setNodeDirtyWithoutNotify() { memory.updateDirtyNodeMask(nodePosMaskBit); }

        @Override
        public void setNodeCleanWithoutNotify() { memory.updateCleanNodeMask(nodePosMaskBit); }

        @Override
        public void reset() {
            insertOrUpdateLeftTuples.clear();
            deleteLeftTuples.clear();
        }
    }
}
