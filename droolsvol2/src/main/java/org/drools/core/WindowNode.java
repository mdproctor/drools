package org.drools.core;
import java.util.List;
/** TODO #6650: Temporary stub — vol2 window node (sliding window filter) not yet implemented. */
public class WindowNode extends BaseNode implements MemoryFactory<WindowNode.WindowMemory> {
    public WindowNode() { }
    @Override
    public WindowMemory createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) {
        return new WindowMemory();
    }
    public static class WindowMemory implements Memory {
        private WindowFilterContext[] filterContext;
        private SegmentMemory segmentMemory;
        public WindowFilterContext[] getFilterContext() { return filterContext; }
        public void setFilterContext(WindowFilterContext[] ctx) { this.filterContext = ctx; }
        @Override public int getNodeType() { return 0; }
        @Override public void reset() { }
        @Override public void setSegmentMemory(SegmentMemory sm) { this.segmentMemory = sm; }
        @Override public SegmentMemory getSegmentMemory() { return segmentMemory; }
    }
}
