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

import org.drools.base.base.ObjectType;
import org.drools.base.common.NetworkNode;
import org.drools.base.common.RuleBasePartitionId;
import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.base.reteoo.NodeTypeEnums;
import org.drools.base.rule.Declaration;
import org.drools.base.rule.GroupElement;
import org.drools.base.rule.Pattern;
import org.drools.core.rete.builder.BuildContext;
import org.drools.util.bitmask.AllSetBitMask;
import org.drools.util.bitmask.BitMask;
import org.drools.util.bitmask.EmptyBitMask;

import java.util.List;
import java.util.Map;

import static org.drools.base.reteoo.PropertySpecificUtil.isPropertyReactive;

public class TerminalNode extends BaseNode implements PathEndNode {

    /** The rule to invoke upon match. */
    private RuleImpl rule;

    /**
     * the subrule reference is needed to resolve declarations
     * because declarations may have different offsets in each subrule
     */
    private GroupElement subrule;
    private int          subruleIndex;
    private Declaration[] allDeclarations;
    protected Declaration[] requiredDeclarations;

    // leftInput is inherited from BaseNode — do not redeclare
    private BaseNode startLeftInput;

    private BitMask declaredMask = EmptyBitMask.get();
    private BitMask inferredMask = EmptyBitMask.get();
    private BitMask negativeMask = EmptyBitMask.get();

    // LeftTupleNode[] pathNodes — commented out until LeftTupleNode is defined in vol2

    private transient PathEndNode[] pathEndNodes;

    private SegmentMemory.SegmentPrototype[] segmentPrototypes;
    private SegmentMemory.SegmentPrototype[] eagerSegmentPrototypes;

    // PathMemSpec pathMemSpec — commented out until PathMemSpec is defined in vol2

    private int objectCount;

    public TerminalNode() { }

    public TerminalNode(int id, BaseNode leftInput,
                        BuildContext context,
                        RuleImpl rule, GroupElement subrule, int subruleIndex) {
        super(id, leftInput.getPathIndex() + 1, leftInput.getObjectIndex());
        setLeftInput(leftInput);
        this.rule = rule;
        this.subrule = subrule;
        this.subruleIndex = subruleIndex;
        this.setObjectCount(getLeftInput().getObjectCount()); // terminal nodes do not increase the count
        context.addPathEndNode(this);
        initMemoryId(context);
        initDeclaredMask(context);
        initInferredMask();

        Map<String, Declaration> decls = this.subrule.getOuterDeclarations();
        this.allDeclarations = decls.values().toArray(new Declaration[decls.size()]);
        // vol2 has no field bindings — requiredDeclarations not needed
        this.requiredDeclarations = new Declaration[0];

        BaseNode current = getLeftInput();
        while (current.getLeftInput() != null) {
            current = current.getLeftInput();
        }
        startLeftInput = current;
    }

    @Override
    public BaseNode getParent() {
        return leftInput;
    }

    // PathMemSpec methods commented out until PathMemSpec is defined in vol2
    //
    // public PathMemSpec getPathMemSpec() { ... }
    // public void setPathMemSpec(PathMemSpec pathMemSpec) { ... }
    // public PathMemSpec getPathMemSpec(TerminalNode removingTN) { ... }
    // public void resetPathMemSpec(TerminalNode removingTN) { ... }
    // public void nullPathMemSpec() { ... }

    public RuleImpl getRule() {
        return this.rule;
    }

    public GroupElement getSubRule() {
        return this.subrule;
    }

    public int getSubruleIndex() {
        return subruleIndex;
    }

    public Declaration[] getAllDeclarations() {
        return this.allDeclarations;
    }

    public Declaration[] getRequiredDeclarations() {
        return this.requiredDeclarations;
    }

    public BaseNode getStartLeftInput() {
        return startLeftInput;
    }

    @Override
    public void setPathEndNodes(PathEndNode[] pathEndNodes) {
        this.pathEndNodes = pathEndNodes;
    }

    @Override
    public PathEndNode[] getPathEndNodes() {
        return pathEndNodes;
    }

    @Override
    public void setSegmentPrototypes(SegmentMemory.SegmentPrototype[] smems) {
        this.segmentPrototypes = smems;
    }

    @Override
    public SegmentMemory.SegmentPrototype[] getSegmentPrototypes() {
        return segmentPrototypes;
    }

    public SegmentMemory.SegmentPrototype[] getEagerSegmentPrototypes() {
        return eagerSegmentPrototypes;
    }

    public void setEagerSegmentPrototypes(SegmentMemory.SegmentPrototype[] eagerSegmentPrototypes) {
        this.eagerSegmentPrototypes = eagerSegmentPrototypes;
    }

    public int getPathIndex() {
        return leftInput.getPathIndex() + 1;
    }

    public int getObjectCount() {
        return objectCount;
    }

    public void setObjectCount(int count) {
        objectCount = count;
    }

    protected void initDeclaredMask(BuildContext context) {
        if (!(NodeTypeEnums.isLeftInputAdapterNode(unwrapLeftInput()))) {
            // terminal nodes not after LIANode are not relevant for property specific
            declaredMask = AllSetBitMask.get();
            return;
        }

        Pattern pattern = context.getLastBuiltPatterns()[0];
        ObjectType objectType = pattern.getObjectType();

        if (isPropertyReactive(context.getRuleBase(), objectType)) {
            List<String> accessibleProperties = pattern.getAccessibleProperties(context.getRuleBase());
            declaredMask = pattern.getPositiveWatchMask(accessibleProperties);
            negativeMask = pattern.getNegativeWatchMask(accessibleProperties);
        } else {
            declaredMask = AllSetBitMask.get();
        }
    }

    public void initInferredMask() {
        BaseNode unwrapped = unwrapLeftInput();
        if (NodeTypeEnums.isLeftInputAdapterNode(unwrapped) &&
                ((LeftInputAdapterNode) unwrapped).getParentObjectSource().getType() == NodeTypeEnums.AlphaNode) {
            AlphaNode alphaNode = (AlphaNode) ((LeftInputAdapterNode) unwrapped).getParentObjectSource();
            inferredMask = alphaNode.updateMask(getDeclaredMask());
        } else {
            inferredMask = getDeclaredMask();
        }

        inferredMask = getInferredMask().resetAll(getNegativeMask());
        if (getNegativeMask().isAllSet() && !getDeclaredMask().isAllSet()) {
            inferredMask = getInferredMask().setAll(getDeclaredMask());
        }
    }

    public BaseNode unwrapLeftInput() {
        return leftInput.getType() == NodeTypeEnums.FromNode ? leftInput.getLeftInput() : leftInput;
    }

    // createMemory commented out until RuleBaseConfiguration is defined in vol2
    // public PathMemory createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) { ... }

    // initPathMemory commented out until PathMemSpec is defined in vol2
    // public static PathMemory initPathMemory(PathEndNode pathEndNode, PathMemory pmem) { ... }

    // doRemove commented out until ReteBuilder reference and removeTupleSink/removeOutput are resolved
    // protected boolean doRemove(final RuleRemovalContext context, final ReteBuilder builder) { ... }

    public BitMask getDeclaredMask() {
        return declaredMask;
    }

    public BitMask getInferredMask() {
        return inferredMask;
    }

    public BitMask getNegativeMask() {
        return negativeMask;
    }

    // networkUpdated commented out until UpdateContext is defined in vol2
    // public void networkUpdated(UpdateContext updateContext) { ... }

    public boolean isInUse() {
        return false;
    }

    public boolean isLeftTupleMemoryEnabled() {
        return false;
    }

    // getPathNodes / hasPathNode / visitLeftTupleNodes commented out until LeftTupleNode is defined in vol2
    // public static BaseNode[] getPathNodes(PathEndNode endNode) { ... }
    // public BaseNode[] getPathNodes() { ... }
    // public boolean hasPathNode(BaseNode node) { ... }
    // public void visitLeftTupleNodes(Consumer<BaseNode> func) { ... }

    @Override
    public final void setPartitionIdWithSinks(RuleBasePartitionId partitionId) {
        this.partitionId = partitionId;
    }

    @Override
    public ObjectTypeNode getObjectTypeNode() {
        return getLeftInput().getObjectTypeNode();
    }

    protected int calculateHashCode() {
        return (31 * (31 + this.rule.hashCode())) + subruleIndex;
    }

    @Override
    public boolean equals(final Object object) {
        if (this == object) {
            return true;
        }
        if (!(object instanceof TerminalNode) || this.hashCode() != object.hashCode()) {
            return false;
        }
        final TerminalNode other = (TerminalNode) object;
        return getRule().equals(other.getRule()) && getSubruleIndex() == other.getSubruleIndex();
    }
}
