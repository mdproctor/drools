package org.drools.core;

import org.drools.base.reteoo.NodeTypeEnums;
import org.drools.core.util.AbstractDoubleLinkedNode;

/**
 * TODO #6650: Temporary stub — queries are unified with rules in vol2,
 * so this node type may be simplified or removed.
 */
public class QueryElementNode extends BaseNode implements MemoryFactory<QueryElementNode.QueryElementNodeMemory> {

    private org.drools.base.rule.QueryElement queryElement;

    public QueryElementNode() {
        super(0, 0, 0);
    }

    public org.drools.base.rule.QueryElement getQueryElement() { return queryElement; }
    public void setQueryElement(org.drools.base.rule.QueryElement qe) { this.queryElement = qe; }

    public QueryElementNodeMemory createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) {
        return new QueryElementNodeMemory(this);
    }

    /**
     * TODO #6650: Simplified stub — full implementation TBD once queries/rules are fully unified.
     */
    public static class QueryElementNodeMemory extends AbstractDoubleLinkedNode<Memory> implements SegmentNodeMemory {
        private final QueryElementNode node;
        private SegmentMemory          smem;
        private SegmentMemory          querySegmentMemory;
        private long                   nodePosMaskBit;

        public QueryElementNodeMemory(QueryElementNode node) {
            this.node = node;
        }

        public QueryElementNode getNode() { return node; }

        @Override
        public int getNodeType() { return NodeTypeEnums.QueryElementNode; }

        @Override
        public void setSegmentMemory(SegmentMemory smem) { this.smem = smem; }

        @Override
        public SegmentMemory getSegmentMemory() { return smem; }

        public SegmentMemory getQuerySegmentMemory() { return querySegmentMemory; }
        public void setQuerySegmentMemory(SegmentMemory qsm) { this.querySegmentMemory = qsm; }

        @Override
        public long getNodePosMaskBit() { return nodePosMaskBit; }

        @Override
        public void setNodePosMaskBit(long nodePosMaskBit) { this.nodePosMaskBit = nodePosMaskBit; }

        @Override
        public void setNodeDirtyWithoutNotify() { }

        @Override
        public void setNodeCleanWithoutNotify() { }

        @Override
        public void reset() { }
    }
}
