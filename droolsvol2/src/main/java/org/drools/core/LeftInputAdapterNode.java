package org.drools.core;

import org.drools.base.reteoo.NodeTypeEnums;
import org.drools.core.util.AbstractDoubleLinkedNode;

public class LeftInputAdapterNode extends BaseNode implements MemoryFactory<LeftInputAdapterNode.LiaNodeMemory> {

    public LeftInputAdapterNode() {
        super(0, 0, 0);
    }

    @Override
    public LiaNodeMemory createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) {
        return new LiaNodeMemory();
    }

    public static class LiaNodeMemory extends AbstractDoubleLinkedNode<Memory> implements SegmentNodeMemory {
        private int           counter;
        private SegmentMemory segmentMemory;
        private long          nodePosMaskBit;

        public LiaNodeMemory() { }

        public int getCounter() { return counter; }
        public int getAndIncreaseCounter() { return this.counter++; }
        public int getAndDecreaseCounter() { return this.counter--; }
        public void setCounter(int counter) { this.counter = counter; }

        public SegmentMemory getSegmentMemory() { return segmentMemory; }
        public void setSegmentMemory(SegmentMemory sm) { this.segmentMemory = sm; }

        public long getNodePosMaskBit() { return nodePosMaskBit; }
        public void setNodePosMaskBit(long nodePosMask) { nodePosMaskBit = nodePosMask; }

        public void setNodeDirtyWithoutNotify() { }
        public void setNodeCleanWithoutNotify() { }

        public void linkNodeWithoutRuleNotify() { segmentMemory.linkNodeWithoutRuleNotify(nodePosMaskBit); }
        public void linkNode() { segmentMemory.linkNode(nodePosMaskBit); }
        public boolean unlinkNode() { return segmentMemory.unlinkNode(nodePosMaskBit); }
        public void unlinkNodeWithoutRuleNotify() { segmentMemory.unlinkNodeWithoutRuleNotify(nodePosMaskBit); }

        public int getNodeType() { return NodeTypeEnums.LeftInputAdapterNode; }
        public void setNodeDirty() { segmentMemory.notifyRuleLinkSegment(nodePosMaskBit); }
        public void reset() { counter = 0; }
    }
}
