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

import java.util.ArrayList;
import java.util.List;

/**
 * Vol2 async receive node — outer class is a stub pending vol2 async/container-queue infrastructure.
 * TODO #6650: implement vol2 async receive node (messages arrive via container queue, not AsyncMessagesCoordinator)
 * The inner AsyncReceiveMemory is needed by SegmentMemory prototype machinery.
 */
public class AsyncReceiveNode extends BaseNode implements MemoryFactory<AsyncReceiveNode.AsyncReceiveMemory> {

    public AsyncReceiveNode() { }

    public AsyncReceiveNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    @Override
    public AsyncReceiveMemory createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) {
        return new AsyncReceiveMemory();
    }

    public static class AsyncReceiveMemory extends AbstractDoubleLinkedNode<Memory> implements SegmentNodeMemory {

        private final TupleList insertOrUpdateLeftTuples = new TupleList();
        private final List<Object> messages = new ArrayList<>();
        private SegmentMemory memory;
        private long          nodePosMaskBit;

        public TupleList getInsertOrUpdateLeftTuples() { return insertOrUpdateLeftTuples; }
        public List<Object> getMessages() { return messages; }

        public void addMessage(Object message) { messages.add(message); }

        @Override
        public int getNodeType() { return NodeTypeEnums.AsyncReceiveNode; }

        @Override
        public SegmentMemory getSegmentMemory() { return this.memory; }

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
        public void reset() { messages.clear(); }
    }
}
