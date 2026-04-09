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

import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.base.reteoo.NodeTypeEnums;

/**
 * Vol2 tuple-to-object node — outer class is a stub pending vol2 bi-linear network infrastructure.
 * In vol1 this was RightInputAdapterNode; in vol2 bi-linear networks replace that concept.
 * TODO #6650: implement vol2 equivalent (input adapter for bi-linear joins, path-end for right sub-networks)
 * The inner SubnetworkPathMemory is needed by SegmentMemory/BetaMemory prototype machinery.
 */
public class TupleToObjectNode extends BaseNode implements PathEndNode, MemoryFactory<PathMemory> {

    private PathEndNode[] pathEndNodes;
    private SegmentMemory.SegmentPrototype[] segmentPrototypes;
    private SegmentMemory.SegmentPrototype[] eagerSegmentPrototypes;
    private BaseNode startLeftInput;

    public TupleToObjectNode() { }

    public TupleToObjectNode(int id, int pathIndex, int objectIndex) {
        super(id, pathIndex, objectIndex);
    }

    @Override
    public PathMemory createMemory(RuleBaseConfiguration config, ReteEvaluator reteEvaluator) {
        return new SubnetworkPathMemory(this, reteEvaluator);
    }

    @Override
    public void setPathEndNodes(PathEndNode[] pathEndNodes) { this.pathEndNodes = pathEndNodes; }

    @Override
    public PathEndNode[] getPathEndNodes() { return pathEndNodes; }

    @Override
    public void setSegmentPrototypes(SegmentMemory.SegmentPrototype[] smems) { this.segmentPrototypes = smems; }

    @Override
    public SegmentMemory.SegmentPrototype[] getSegmentPrototypes() { return segmentPrototypes; }

    @Override
    public SegmentMemory.SegmentPrototype[] getEagerSegmentPrototypes() { return eagerSegmentPrototypes; }

    @Override
    public void setEagerSegmentPrototypes(SegmentMemory.SegmentPrototype[] eagerSegmentPrototypes) {
        this.eagerSegmentPrototypes = eagerSegmentPrototypes;
    }

    @Override
    public BaseNode getStartLeftInput() { return startLeftInput; }

    /** TODO #6650: PathMemSpec not yet implemented in vol2. */
    public PathMemSpec getPathMemSpec() { return null; }

    /**
     * Subnetwork path memory — holds the PathMemory for a right sub-network in a bi-linear join.
     * TODO #6650: wire doLinkRule/doUnlinkRule once vol2 subnetwork propagation is built.
     */
    public static class SubnetworkPathMemory extends PathMemory implements Memory {

        public SubnetworkPathMemory(PathEndNode pathEndNode, ReteEvaluator reteEvaluator) {
            super(pathEndNode, reteEvaluator);
        }

        @Override
        protected boolean initDataDriven(ReteEvaluator reteEvaluator) {
            for (PathEndNode pnode : getPathEndNode().getPathEndNodes()) {
                if (NodeTypeEnums.isTerminalNode(pnode)) {
                    RuleImpl rule = ((TerminalNode) pnode).getRule();
                    if (isRuleDataDriven(reteEvaluator, rule)) {
                        return true;
                    }
                }
            }
            return false;
        }

        public TupleToObjectNode getTupleToObjectNode() {
            return (TupleToObjectNode) getPathEndNode();
        }

        @Override
        public void doLinkRule() {
            // TODO #6650: vol2 subnetwork link propagation not yet implemented
        }

        @Override
        public void doUnlinkRule() {
            // TODO #6650: vol2 subnetwork unlink propagation not yet implemented
        }

        @Override
        public int getNodeType() {
            return NodeTypeEnums.TupleToObjectNode;
        }

        @Override
        public String toString() {
            return "SubnetworkPathMemory(tton=" + getTupleToObjectNode().getId() + ")";
        }
    }
}
