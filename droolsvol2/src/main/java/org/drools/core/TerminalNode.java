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

import org.drools.base.common.RuleBasePartitionId;
import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.base.reteoo.BaseTerminalNode;
import org.drools.base.reteoo.NodeTypeEnums;
import org.drools.base.rule.Declaration;
import org.drools.base.rule.GroupElement;
import org.drools.core.rete.builder.BuildContext;
import org.drools.util.bitmask.BitMask;
import org.drools.util.bitmask.EmptyBitMask;

import java.util.Map;

public class TerminalNode extends BaseNode implements PathEndNode, BaseTerminalNode {

    private RuleImpl rule;
    private GroupElement subrule;
    private int          subruleIndex;
    private Declaration[] allDeclarations;
    protected Declaration[] requiredDeclarations;

    private BaseNode startLeftInput;

    private BitMask declaredMask = EmptyBitMask.get();
    private BitMask inferredMask = EmptyBitMask.get();
    private BitMask negativeMask = EmptyBitMask.get();

    private transient PathEndNode[] pathEndNodes;

    private SegmentMemory.SegmentPrototype[] segmentPrototypes;
    private SegmentMemory.SegmentPrototype[] eagerSegmentPrototypes;

    private int objectCount;

    @Override public int getType() { return Vol2NodeTypeEnums.TerminalNode; }

    public TerminalNode() { }

    public TerminalNode(int id, BaseNode leftInput,
                        BuildContext context,
                        RuleImpl rule, GroupElement subrule, int subruleIndex) {
        super(id, leftInput.getPathIndex() + 1, leftInput.getObjectIndex());
        setLeftInput(leftInput);
        this.rule = rule;
        this.subrule = subrule;
        this.subruleIndex = subruleIndex;
        this.objectCount = getLeftInput().getObjectCount();
        context.addPathEndNode(this);
        initMemoryId(context);

        Map<String, Declaration> decls = this.subrule.getOuterDeclarations();
        this.allDeclarations = decls.values().toArray(new Declaration[decls.size()]);
        this.requiredDeclarations = new Declaration[0]; // vol2 has no field bindings

        BaseNode current = getLeftInput();
        while (current.getLeftInput() != null) {
            current = current.getLeftInput();
        }
        startLeftInput = current;
    }

    // PathMemSpec methods commented out until PathMemSpec is defined in vol2
    // public PathMemSpec getPathMemSpec() { ... }
    // public void setPathMemSpec(PathMemSpec pathMemSpec) { ... }
    // public PathMemSpec getPathMemSpec(TerminalNode removingTN) { ... }
    // public void resetPathMemSpec(TerminalNode removingTN) { ... }
    // public void nullPathMemSpec() { ... }

    @Override
    public RuleImpl getRule() {
        return this.rule;
    }

    @Override
    public GroupElement getSubRule() {
        return this.subrule;
    }

    @Override
    public int getSubruleIndex() {
        return subruleIndex;
    }

    @Override
    public Declaration[] getAllDeclarations() {
        return this.allDeclarations;
    }

    @Override
    public Declaration[] getRequiredDeclarations() {
        return this.requiredDeclarations;
    }

    @Override
    public Declaration[] getSalienceDeclarations() {
        return new Declaration[0]; // vol2 — TBD
    }

    @Override
    public boolean isFireDirect() {
        return false; // vol2 — TBD
    }

    @Override
    public void initInferredMask() {
        // vol2 TODO: mask initialisation depends on property reactivity model
        inferredMask = declaredMask;
    }

    @Override
    public BitMask getNegativeMask() {
        return negativeMask;
    }

    public BitMask getDeclaredMask() {
        return declaredMask;
    }

    public BitMask getInferredMask() {
        return inferredMask;
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

    @Override
    public SegmentMemory.SegmentPrototype[] getEagerSegmentPrototypes() {
        return eagerSegmentPrototypes;
    }

    @Override
    public void setEagerSegmentPrototypes(SegmentMemory.SegmentPrototype[] eagerSegmentPrototypes) {
        this.eagerSegmentPrototypes = eagerSegmentPrototypes;
    }

    public int getObjectCount() {
        return objectCount;
    }

    public void setObjectCount(int count) {
        objectCount = count;
    }

    @Override
    public PathMemory createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) {
        // TODO #6650: wire path memory creation once vol2 evaluation engine is built
        return new PathMemory(this, reteEvaluator);
    }

    public boolean isInUse() {
        return false;
    }

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
