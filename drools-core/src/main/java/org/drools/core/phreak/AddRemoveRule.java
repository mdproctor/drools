/*
 * Copyright 2015 Red Hat, Inc. and/or its affiliates.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
*/

package org.drools.core.phreak;


import org.drools.core.common.EventFactHandle;
import org.drools.core.common.InternalFactHandle;
import org.drools.core.common.InternalWorkingMemory;
import org.drools.core.common.Memory;
import org.drools.core.common.MemoryFactory;
import org.drools.core.common.PropagationContextFactory;
import org.drools.core.common.TupleSets;
import org.drools.core.common.TupleSetsImpl;
import org.drools.core.definitions.rule.impl.RuleImpl;
import org.drools.core.impl.InternalKnowledgeBase;
import org.drools.core.reteoo.AbstractTerminalNode;
import org.drools.core.reteoo.AccumulateNode;
import org.drools.core.reteoo.AccumulateNode.AccumulateContext;
import org.drools.core.reteoo.AccumulateNode.AccumulateMemory;
import org.drools.core.reteoo.BetaMemory;
import org.drools.core.reteoo.BetaNode;
import org.drools.core.reteoo.FromNode.FromMemory;
import org.drools.core.reteoo.LeftInputAdapterNode;
import org.drools.core.reteoo.LeftInputAdapterNode.RightTupleSinkAdapter;
import org.drools.core.reteoo.LeftTuple;
import org.drools.core.reteoo.LeftTupleNode;
import org.drools.core.reteoo.LeftTupleSink;
import org.drools.core.reteoo.LeftTupleSinkNode;
import org.drools.core.reteoo.LeftTupleSource;
import org.drools.core.reteoo.NodeTypeEnums;
import org.drools.core.reteoo.ObjectSource;
import org.drools.core.reteoo.ObjectTypeNode;
import org.drools.core.reteoo.ObjectTypeNode.ObjectTypeNodeMemory;
import org.drools.core.reteoo.PathEndNode;
import org.drools.core.reteoo.PathMemory;
import org.drools.core.reteoo.QueryElementNode;
import org.drools.core.reteoo.RightInputAdapterNode;
import org.drools.core.reteoo.RightInputAdapterNode.RiaNodeMemory;
import org.drools.core.reteoo.RightTuple;
import org.drools.core.reteoo.SegmentMemory;
import org.drools.core.reteoo.TerminalNode;
import org.drools.core.reteoo.TupleMemory;
import org.drools.core.reteoo.WindowNode;
import org.drools.core.spi.PropagationContext;
import org.drools.core.spi.Tuple;
import org.drools.core.util.FastIterator;
import org.drools.core.util.LinkedList;
import org.kie.api.definition.rule.Rule;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

public class AddRemoveRule {

    private static final Logger log = LoggerFactory.getLogger(AddRemoveRule.class);

    /**
     * This method is called after the rule nodes have been added to the network
     * For add tuples are processed after the segments and pmems have been adjusted
     *
     * @param tn
     * @param wms
     * @param kBase
     */
    public static void addRule(TerminalNode tn, InternalWorkingMemory[] wms, InternalKnowledgeBase kBase) {
        if (log.isTraceEnabled()) {
            log.trace("Adding Rule {}", tn.getRule().getName());
        }

        boolean hasProtos = kBase.hasSegmentPrototypes();
        boolean hasWms = wms.length > 0;

        if (!hasProtos && !hasWms) {
            return;
        }

        RuleImpl rule = tn.getRule();
        LeftTupleNode firstSplit = getNetworkSplitPoint(tn, rule);
        PathEndNodes pathEndNodes = getPathEndNodes(kBase, firstSplit, tn, rule, hasProtos, hasWms);

        // Insert the facts for the new paths. This will iterate each new path from EndNode to the splitStart - but will not process the splitStart itself (as tha already exist).
        // It does not matter that the prior segments have not yet been processed for splitting, as this will only apply for branches of paths that did not exist before


        for (InternalWorkingMemory wm : wms) {
            wm.flushPropagations();

            if (NodeTypeEnums.LeftInputAdapterNode == firstSplit.getType() && firstSplit.getAssociatedRuleSize() == 1) {
                // rule added with no sharing
                insertLiaFacts(firstSplit, wm);
            } else {
                PathEndNodeMemories tnms = getPathEndMemories(wm, pathEndNodes, false);

                if (tnms.subjectPmem == null) {
                    // If the existing PathMemories are not yet initialized there are no Segments or tuples to process
                    continue;
                }

                Map<PathMemory, SegmentMemory[]> prevSmemsLookup = reInitPathMemories(wm, tnms.otherPmems, null);

                // must collect all visited SegmentMemories, for link notification
                Set<SegmentMemory> smemsToNotify = addExistingPaths(rule, prevSmemsLookup, tnms.otherPmems, kBase, wm);

                addNewPaths(wm, smemsToNotify, tnms.subjectPmems);

                processLeftTuples(firstSplit, wm, true, rule);

                notifySegments(smemsToNotify, wm);
            }
        }

        insertFacts(pathEndNodes, wms);
    }


    private static Set<SegmentMemory> addExistingPaths(RuleImpl rule, Map<PathMemory, SegmentMemory[]> prevSmemsLookup,
                                                       List<PathMemory> pmems, InternalKnowledgeBase kBase, InternalWorkingMemory wm) {
        Set<SegmentMemory>                smemsToNotify    = new HashSet<SegmentMemory>();
        Set<SegmentMemory>                visitedSegments  = new HashSet<SegmentMemory>();
        Map<LeftTupleNode, SegmentMemory> nodeToSegmentMap = new HashMap<LeftTupleNode, SegmentMemory>();

        for (PathMemory pmem : pmems) {
            LeftTupleNode[] nodes = pmem.getPathEndNode().getPathNodes();

            SegmentMemory[] prevSmems = prevSmemsLookup.get(pmem);
            SegmentMemory[] smems     = pmem.getSegmentMemories();

            LeftTupleNode node                  = null;
            int           prevSmemIndex         = 0;
            int           smemIndex             = 0;
            int           smemSplitAdjustAmount = 0;
            int           nodeIndex             = 0;
            // excluding the rule just added iterate while not split (i.e. find the next split, prior to this rule being added)
            // note it's checking for when the parent is the split, and thus node is the next root root.

            smems[smemIndex] = prevSmems[prevSmemIndex];
            do {
                node       = nodes[nodeIndex++];
                LeftTupleNode parentNode = node.getLeftTupleSource();
                if (isSplit(parentNode)) {
                    smemIndex++;
                    if (isSplit(parentNode, rule)) {
                        prevSmemIndex++;
                        smems[smemIndex] = prevSmems[prevSmemIndex];
                        if ( smems[smemIndex] != null && smemSplitAdjustAmount > 0 && visitedSegments.add(smems[smemIndex])) {
                            smemsToNotify.add(smems[smemIndex]);
                            smems[smemIndex].unlinkSegment(wm);
                            correctSegmentMemoryAfterSplitOnAdd(smems[smemIndex], smemSplitAdjustAmount);
                        }
                    } else {
                        if (smems[smemIndex - 1] != null) {
                            SegmentMemory sm2 = nodeToSegmentMap.get(node);
                            if (sm2 == null) {
                                SegmentMemory sm1 = smems[smemIndex - 1];
                                correctMemoryOnSplitsChanged(parentNode, null, wm);
                                sm2 = splitSegment(sm1, parentNode);
                                nodeToSegmentMap.put(node, sm2);
                                smemsToNotify.add(sm1);
                                smemsToNotify.add(sm2);
                            }

                            smems[smemIndex] = sm2;
                        }
                        smemSplitAdjustAmount++;
                    }
                }
            } while (!NodeTypeEnums.isEndNode(node));

        }
        return smemsToNotify;
    }

    private static void addNewPaths(InternalWorkingMemory wm, Set<SegmentMemory> smemsToNotify, List<PathMemory> pmems) {
        for (PathMemory pmem : pmems) {
            LeftTupleSink tipNode = (LeftTupleSink) pmem.getPathEndNode();

            LeftTupleNode child  = tipNode;
            LeftTupleNode parent = tipNode.getLeftTupleSource();

            SegmentMemory[] smems = pmem.getSegmentMemories();
            while (true) {
                if (parent != null && parent.getAssociatedRuleSize() != 1 && child.getAssociatedRuleSize() == 1) {
                    // This is the split point that the new path enters an existing path.
                    // If the parent has other child SegmentMemorys then it must create a new child SegmentMemory
                    // If the parent is a query node, then it's internal data structure needs changing
                    // all right input data must be propagated
                    Memory mem = wm.getNodeMemories().peekNodeMemory(parent.getId());
                    if (mem != null && mem.getSegmentMemory() != null) {
                        SegmentMemory sm = mem.getSegmentMemory();
                        if (sm.getFirst() != null) {
                            SegmentMemory childSmem = SegmentUtilities.createChildSegment(wm, child);
                            sm.add(childSmem);
                            smems[childSmem.getPos()] = childSmem;
                            smemsToNotify.add(childSmem);
                        }
                        correctMemoryOnSplitsChanged(parent, null, wm);
                    }
                } else {
                    Memory mem = wm.getNodeMemories().peekNodeMemory(child.getId());
                    // The root of each segment
                    if (mem != null) {
                        SegmentMemory sm = mem.getSegmentMemory();
                        if (sm != null && !sm.getPathMemories().contains( pmem )) {
                            sm.addPathMemory( pmem );
                            pmem.setSegmentMemory( sm.getPos(), sm );
                            sm.notifyRuleLinkSegment( wm, pmem );
                        }
                    }
                }

                if (parent == null) {
                    break;
                }

                child = parent;
                parent = parent.getLeftTupleSource();
            }
        }
    }

    /**
     * This method is called before the rule nodes are removed from the network.
     * For remove tuples are processed before the segments and pmems have been adjusted
     *
     * @param tn
     * @param wms
     * @param kBase
     */
    public static void removeRule(TerminalNode tn, InternalWorkingMemory[] wms, InternalKnowledgeBase kBase) {
        if (log.isTraceEnabled()) {
            log.trace("Removing Rule {}", tn.getRule().getName());
        }

        boolean hasProtos = kBase.hasSegmentPrototypes();
        boolean hasWms = wms.length > 0;

        if (!hasProtos && !hasWms) {
            return;
        }

        RuleImpl      rule       = tn.getRule();
        LeftTupleNode firstSplit = getNetworkSplitPoint(tn, rule);
        PathEndNodes pathEndNodes = getPathEndNodes(kBase, firstSplit, tn, rule, hasProtos, hasWms);

        for (InternalWorkingMemory wm : wms) {
            wm.flushPropagations();

            processLeftTuples(firstSplit, wm, false, tn.getRule());


            PathEndNodeMemories tnms = getPathEndMemories(wm, pathEndNodes, true);

            if (NodeTypeEnums.LeftInputAdapterNode == firstSplit.getType() && firstSplit.getAssociatedRuleSize() == 1) {
                if ( tnms.subjectPmem != null ) {
                    flushStagedTuples(firstSplit, tnms.subjectPmem, wm);
                }
            } else {

                for (PathMemory pmem : tnms.pmemsToBeFlushed) {
                    flushStagedTuples(firstSplit, pmem, wm);
                }

                Map<PathMemory, SegmentMemory[]> prevSmemsLookup = reInitPathMemories(wm, tnms.otherPmems, rule);

                // must collect all visited SegmentMemories, for link notification
                Set<SegmentMemory> smemsToNotify = removeExistingPaths(rule, prevSmemsLookup, tnms.otherPmems, wm);

                removeNewPaths(wm, tnms.subjectPmems);

                notifySegments(smemsToNotify, wm);
            }

            if (tnms.subjectPmem != null && tnms.subjectPmem.getRuleAgendaItem() != null && tnms.subjectPmem.getRuleAgendaItem().isQueued()) {
                // SubjectPmem can be null, if it was never initialized
                tnms.subjectPmem.getRuleAgendaItem().dequeue();
            }
        }
    }

    private static Set<SegmentMemory> removeExistingPaths(RuleImpl rule, Map<PathMemory, SegmentMemory[]> prevSmemsLookup,
                                                          List<PathMemory> pmems, InternalWorkingMemory wm) {
        Set<SegmentMemory> visitedSegments = new HashSet<SegmentMemory>();
        Set<LeftTupleNode> alreadyMerged = new HashSet<LeftTupleNode>();
        Set<SegmentMemory> smemsToNotify   = new HashSet<SegmentMemory>();
        for (PathMemory pmem : pmems) {
            LeftTupleNode[] nodes = pmem.getPathEndNode().getPathNodes();

            SegmentMemory[] prevSmems = prevSmemsLookup.get(pmem);
            SegmentMemory[] smems     = pmem.getSegmentMemories();

            LeftTupleNode node                  = null;
            int           prevSmemIndex         = 0;
            int           smemIndex             = 0;
            int           smemSplitAdjustAmount = 0;
            int           nodeIndex             = 0;
            // excluding the rule just added iterate while not split (i.e. find the next split, prior to this rule being added)
            // note it's checking for when the parent is the split, and thus node is the next root root.

            smems[smemIndex] = prevSmems[prevSmemIndex];
            do {
                node       = nodes[nodeIndex++];
                LeftTupleNode parentNode = node.getLeftTupleSource();
                if (isSplit(parentNode)) {
                    prevSmemIndex++;
                    if (isSplit(parentNode, rule)) {
                        smemIndex++;
                        smems[smemIndex] = prevSmems[prevSmemIndex];
                        if (smems[smemIndex] != null && smemSplitAdjustAmount > 0 && visitedSegments.add(smems[smemIndex])) {
                            correctSegmentMemoryAfterSplitOnRemove(smems[smemIndex], smemSplitAdjustAmount);
                        }

                    } else {
                        if (alreadyMerged.add(node)) {
                            correctMemoryOnSplitsChanged(parentNode, rule, wm);

                            SegmentMemory sm1 = smems[smemIndex];
                            SegmentMemory sm2 = prevSmems[prevSmemIndex];
                            if (sm1 != null && sm2 == null) {
                                sm2 = SegmentUtilities.createChildSegment(wm,node);
                                sm1.add(sm2);
                            } else if (sm1 == null && sm2 != null) {
                                sm1 = SegmentUtilities.createChildSegment(wm, parentNode);
                                sm1.add(sm2);
                            }

                            if (sm1 != null && sm2 != null) {
                                mergeSegment(sm1, sm2);
                                smemsToNotify.add(sm1);
                                sm1.unlinkSegment(wm);
                                sm2.unlinkSegment(wm);
                            }
                        }
                        smemSplitAdjustAmount++;
                    }
                }
            } while (!NodeTypeEnums.isEndNode(node));
        }
        return smemsToNotify;
    }

    private static void removeNewPaths(InternalWorkingMemory wm, List<PathMemory> pmems) {
        for (PathMemory pmem : pmems) {
            LeftTupleSink tipNode = (LeftTupleSink) pmem.getPathEndNode();

            LeftTupleNode node = tipNode;

            while (node != null) {
                if (node.getAssociatedRuleSize() == 1 && NodeTypeEnums.isBetaNode(node)) {
                    // If this is a beta node, it'll delete all the right input data
                    deleteRightInputData((LeftTupleSink) node, wm);
                }

                Memory mem = wm.getNodeMemories().peekNodeMemory(node.getId());
                // The root of each segment
                if (mem != null && mem.getSegmentMemory() != null) {
                    mem.getSegmentMemory().removePathMemory(pmem);
                }

                node = node.getLeftTupleSource();
            }
        }
    }

    private static boolean isSplit(LeftTupleNode node) {
        return isSplit(node, null);
    }

    private static boolean isSplit(LeftTupleNode node, Rule excludingRule) {
        return node != null && SegmentUtilities.isTipNode( node, excludingRule );

    }

    private static void flushStagedTuples(LeftTupleNode splitStartNode, PathMemory pmem, InternalWorkingMemory wm) {
        int             smemIndex = getSegmentPos(splitStartNode, null); // index before the segments are merged
        SegmentMemory[] smems     = pmem.getSegmentMemories();

        SegmentMemory   sm;
        LeftTupleSink   sink;
        Memory          mem;
        long            bit       = 1;
        if (splitStartNode.getAssociatedRuleSize() == 1 && (smems[0] == null || smems[0].getTipNode().getType() != NodeTypeEnums.LeftInputAdapterNode)) {
            // there is no sharing
            sm = smems[0];
            if (sm == null || sm.getStagedLeftTuples().isEmpty()) {
                return; // segment has not yet been initialized
            }
            sink = sm.getRootNode().getSinkPropagator().getFirstLeftTupleSink();
            mem = sm.getNodeMemories().get(1);
            bit = 2; // adjust bit to point to next node
        } else {
            sm = smems[++smemIndex]; // segment after the split being removed.
            if (sm == null || sm.getStagedLeftTuples().isEmpty()) {
                return; // segment has not yet been initialized
            }
            sink = (LeftTupleSink) sm.getRootNode();
            mem = sm.getNodeMemories().get(0);
        }

        new RuleNetworkEvaluator().outerEval((LeftInputAdapterNode) smems[0].getRootNode(),
                                             pmem, sink, bit, mem, smems, smemIndex,
                                             sm.getStagedLeftTuples().takeAll(), wm, new LinkedList<StackEntry>(), true, pmem.getRuleAgendaItem().getRuleExecutor());
    }

    public static boolean flushLeftTupleIfNecessary(InternalWorkingMemory wm, SegmentMemory sm, LeftTuple leftTuple, boolean streamMode) {
        PathMemory pmem = streamMode ?
                          sm.getPathMemories().get(0) :
                          sm.getFirstDataDrivenPathMemory();
        return pmem != null && forceFlushLeftTuple(pmem, sm, wm, leftTuple);
    }

    private static boolean forceFlushLeftTuple(PathMemory pmem, SegmentMemory sm, InternalWorkingMemory wm, LeftTuple leftTuple) {
        SegmentMemory[] smems = pmem.getSegmentMemories();
        if (smems[0] == null) {
            return false; // segment has not yet been initialized
        }

        LeftTupleSink sink;
        Memory        mem;
        long          bit = 1;
        if (sm.getRootNode() instanceof LeftInputAdapterNode) {
            sink = ((LeftInputAdapterNode) sm.getRootNode()).getSinkPropagator().getFirstLeftTupleSink();
            mem = sm.getNodeMemories().get(1);
            bit = 2; // adjust bit to point to next node
        } else {
            sink = (LeftTupleSink) sm.getRootNode();
            mem = sm.getNodeMemories().get(0);
        }

        TupleSets<LeftTuple> leftTupleSets = new TupleSetsImpl<LeftTuple>();
        if (leftTuple != null) {
            leftTupleSets.addInsert(leftTuple);
        }

        new RuleNetworkEvaluator().outerEval((LeftInputAdapterNode) smems[0].getRootNode(),
                                             pmem, sink, bit, mem, smems, sm.getPos(), leftTupleSets, wm,
                                             new LinkedList<StackEntry>(),
                                             true, pmem.getOrCreateRuleAgendaItem(wm).getRuleExecutor());
        return true;
    }


    private static Map<PathMemory, SegmentMemory[]> reInitPathMemories(InternalWorkingMemory wm, List<PathMemory> pathMems, Rule removingRule) {
        Map<PathMemory, SegmentMemory[]> previousSmems = new HashMap<PathMemory, SegmentMemory[]>();
        for (PathMemory pmem : pathMems) {
            // Re initialise all the PathMemories
            previousSmems.put(pmem, pmem.getSegmentMemories());
            LeftTupleSource startRianLts = null;
            if (!NodeTypeEnums.isTerminalNode(pmem.getPathEndNode())) {
                RightInputAdapterNode rian = (RightInputAdapterNode) pmem.getPathEndNode();
                startRianLts = rian.getStartTupleSource();
            }
            AbstractTerminalNode.initPathMemory(pmem, pmem.getPathEndNode(), startRianLts, wm, removingRule); // re-initialise the PathMemory
        }
        return previousSmems;
    }

    public static void notifySegments(Set<SegmentMemory> smems, InternalWorkingMemory wm) {
        for (SegmentMemory sm : smems) {
            sm.notifyRuleLinkSegment(wm);
        }
    }

    private static void correctMemoryOnSplitsChanged(LeftTupleNode splitStart, Rule removingRule, InternalWorkingMemory wm) {
        if (splitStart.getType() == NodeTypeEnums.UnificationNode) {
            QueryElementNode.QueryElementNodeMemory mem = (QueryElementNode.QueryElementNodeMemory) wm.getNodeMemories().peekNodeMemory(splitStart.getId());
            if (mem != null) {
                mem.correctMemoryOnSinksChanged(removingRule);
            }
        }
    }


    public static void correctSegmentMemoryAfterSplitOnAdd(SegmentMemory sm) {
        correctSegmentMemoryAfterSplitOnAdd(sm, 1);
    }

    public static void correctSegmentMemoryAfterSplitOnAdd(SegmentMemory sm, int i) {
        sm.setPos(sm.getPos() + i);
        sm.setSegmentPosMaskBit(sm.getSegmentPosMaskBit() << i);
    }

    public static void correctSegmentMemoryAfterSplitOnRemove(SegmentMemory sm, int i) {
        sm.setPos(sm.getPos() - i);
        sm.setSegmentPosMaskBit(sm.getSegmentPosMaskBit() >> i);
    }

    public static int getSegmentPos(LeftTupleNode lts, Rule removingRule) {
        int counter = 0;
        while (lts.getType() != NodeTypeEnums.LeftInputAdapterNode) {
            lts = lts.getLeftTupleSource();
            if (SegmentUtilities.isTipNode(lts, removingRule)) {
                counter++;
            }
        }
        return counter;
    }

    private static void insertLiaFacts(LeftTupleNode startNode, InternalWorkingMemory wm) {
        // rule added with no sharing
        PropagationContextFactory pctxFactory = wm.getKnowledgeBase().getConfiguration().getComponentFactory().getPropagationContextFactory();
        final PropagationContext  pctx        = pctxFactory.createPropagationContext(wm.getNextPropagationIdCounter(), PropagationContext.RULE_ADDITION, null, null, null);
        LeftInputAdapterNode      lian        = (LeftInputAdapterNode) startNode;
        RightTupleSinkAdapter     liaAdapter  = new RightTupleSinkAdapter(lian);
        lian.getObjectSource().updateSink(liaAdapter, pctx, wm);
    }

    private static void insertFacts(PathEndNodes endNodes, InternalWorkingMemory[] wms) {
        int index = 0;
        if ( endNodes.subjectSplit != null ) {
            index = endNodes.subjectSplit.getPositionInPath() + 1; // must be +1 otherwise it will propagate existing data, as subjectSplit is the split node in the existing network
        }
        Set<LeftTupleNode> visited = new HashSet<LeftTupleNode>();

        for ( PathEndNode endNode : endNodes.subjectEndNodes ) {
            LeftTupleNode[]  nodes = endNode.getPathNodes();
            for ( int i = nodes.length-1; i >= index; i-- ) {
                LeftTupleNode node = nodes[i];
                if  ( NodeTypeEnums.isBetaNode(node)  ) {
                    if (!visited.add( node )) {
                        continue;// this is to avoid rentering a path, and processing nodes twice. This can happen for nested subnetworks.
                    }
                    BetaNode bn = (BetaNode) node;

                    if (!bn.isRightInputIsRiaNode()) {
                        for ( int j = 0; j < wms.length; j++ ) {
                            PropagationContextFactory pctxFactory = wms[j].getKnowledgeBase().getConfiguration().getComponentFactory().getPropagationContextFactory();
                            final PropagationContext pctx = pctxFactory.createPropagationContext(wms[j].getNextPropagationIdCounter(), PropagationContext.RULE_ADDITION, null, null, null);
                            bn.getRightInput().updateSink(bn,
                                                          pctx,
                                                          wms[j]);
                        }
                    }
                }
            }
        }
    }

    private static void deleteRightInputData(LeftTupleSink node, InternalWorkingMemory wm) {
        if (wm.getNodeMemories().peekNodeMemory(node.getId()) != null) {
            BetaNode   bn = (BetaNode) node;
            BetaMemory bm;
            if (bn.getType() == NodeTypeEnums.AccumulateNode) {
                bm = ((AccumulateMemory) wm.getNodeMemory(bn)).getBetaMemory();
            } else {
                bm = (BetaMemory) wm.getNodeMemory(bn);
            }

            TupleMemory  rtm = bm.getRightTupleMemory();
            FastIterator it  = rtm.fullFastIterator();
            for (Tuple rightTuple = BetaNode.getFirstTuple(rtm, it); rightTuple != null; ) {
                Tuple next = (Tuple) it.next(rightTuple);
                rtm.remove(rightTuple);
                rightTuple.unlinkFromRightParent();
                rightTuple = next;
            }

            if (!bm.getStagedRightTuples().isEmpty()) {
                bm.setNodeDirtyWithoutNotify();
            }
            TupleSets<RightTuple> srcRightTuples = bm.getStagedRightTuples().takeAll();

            unlinkRightTuples(srcRightTuples.getInsertFirst());
            unlinkRightTuples(srcRightTuples.getUpdateFirst());
            unlinkRightTuples(srcRightTuples.getDeleteFirst());

            deleteFactsFromRightInput(bn, wm);
        }
    }

    private static void deleteFactsFromRightInput(BetaNode bn, InternalWorkingMemory wm) {
        ObjectSource source = bn.getRightInput();
        if (source instanceof WindowNode) {
            WindowNode.WindowMemory memory = (WindowNode.WindowMemory) wm.getNodeMemory(((WindowNode) source));
            for (EventFactHandle factHandle : memory.getFactHandles()) {
                for (RightTuple rightTuple = factHandle.getFirstRightTuple(); rightTuple != null; ) {
                    RightTuple nextRightTuple = rightTuple.getHandleNext();
                    if (source.equals(rightTuple.getTupleSink())) {
                        rightTuple.unlinkFromRightParent();
                    }
                    rightTuple = nextRightTuple;
                }
            }
        }
    }

    private static void unlinkRightTuples(RightTuple rightTuple) {
        for (RightTuple rt = rightTuple; rt != null; ) {
            RightTuple next = rt.getStagedNext();
            // this RightTuple could have been already unlinked by the former cycle
            if (rt.getFactHandle() != null) {
                rt.unlinkFromRightParent();
            }
            rt = next;
        }
    }

    /**
     * Populates the SegmentMemory with staged LeftTuples. If the parent is not a Beta or From node, it iterates up to find the first node with memory. If necessary
     * It traverses to the LiaNode's ObjectTypeNode. It then iterates the LeftTuple chains, where an existing LeftTuple is staged
     * as delete. Or a new LeftTuple is created and staged as an insert.
     */
    private static void processLeftTuples(LeftTupleNode node, InternalWorkingMemory wm, boolean insert, Rule rule) {
        // *** if you make a fix here, it most likely needs to be in PhreakActivationIteratorToo ***

        // Must iterate up until a node with memory is found, this can be followed to find the LeftTuples
        // which provide the potential peer of the tuple being added or removed

        Memory memory = wm.getNodeMemories().peekNodeMemory(node.getId());
        if (memory == null || memory.getSegmentMemory() == null) {
            // segment has never been initialized, which means the rule(s) have never been linked and thus no Tuples to fix
            return;
        }
        SegmentMemory sm = memory.getSegmentMemory();

        while (NodeTypeEnums.LeftInputAdapterNode != node.getType()) {

            if (NodeTypeEnums.isBetaNode(node)) {
                BetaMemory    bm;
                SegmentMemory childSmem = sm; // if there is no split the child smem is same as current node

                if (sm.getTipNode() == node) {
                    // There is a network split, so must use the next sm
                    childSmem = sm.getFirst();
                }
                if (NodeTypeEnums.AccumulateNode == node.getType()) {
                    AccumulateMemory am = (AccumulateMemory) memory;
                    bm = am.getBetaMemory();
                    FastIterator it = bm.getLeftTupleMemory().fullFastIterator();
                    Tuple        lt = BetaNode.getFirstTuple(bm.getLeftTupleMemory(), it);
                    for (; lt != null; lt = (LeftTuple) it.next(lt)) {
                        AccumulateContext accctx = (AccumulateContext) lt.getContextObject();
                        visitChild(accctx.getResultLeftTuple(), childSmem, insert, wm, rule);
                    }
                } else if (NodeTypeEnums.ExistsNode == node.getType()) {
                    bm = (BetaMemory) wm.getNodeMemory((MemoryFactory) node);
                    FastIterator it = bm.getRightTupleMemory().fullFastIterator(); // done off the RightTupleMemory, as exists only have unblocked tuples on the left side
                    RightTuple   rt = (RightTuple) BetaNode.getFirstTuple(bm.getRightTupleMemory(), it);
                    for (; rt != null; rt = (RightTuple) it.next(rt)) {
                        for (LeftTuple lt = rt.getBlocked(); lt != null; lt = lt.getBlockedNext()) {
                            visitChild(lt.getFirstChild(), childSmem, insert, wm, rule);
                        }
                    }
                } else {
                    bm = (BetaMemory) wm.getNodeMemory((MemoryFactory) node);
                    FastIterator it = bm.getLeftTupleMemory().fullFastIterator();
                    Tuple        lt = BetaNode.getFirstTuple(bm.getLeftTupleMemory(), it);
                    for (; lt != null; lt = (LeftTuple) it.next(lt)) {
                        visitChild(lt.getFirstChild(), childSmem, insert, wm, rule);
                    }
                }
                return;
            } else if (NodeTypeEnums.FromNode == node.getType()) {
                FromMemory   fm  = (FromMemory) wm.getNodeMemory((MemoryFactory) node);
                TupleMemory  ltm = fm.getBetaMemory().getLeftTupleMemory();
                FastIterator it  = ltm.fullFastIterator();
                for (LeftTuple lt = (LeftTuple) ltm.getFirst(null); lt != null; lt = (LeftTuple) it.next(lt)) {
                    visitChild(lt, sm, insert, wm, rule);
                }
                return;
            }
            if (sm.getRootNode() == node) {
                sm = wm.getNodeMemory((MemoryFactory<Memory>) node.getLeftTupleSource()).getSegmentMemory();
            }
            node = node.getLeftTupleSource();
        }

        // No beta or from nodes, so must retrieve LeftTuples from the LiaNode.
        // This is done by scanning all the LeftTuples referenced from the FactHandles in the ObjectTypeNode
        LeftInputAdapterNode lian = (LeftInputAdapterNode) node;

        ObjectSource os = lian.getObjectSource();
        while (os.getType() != NodeTypeEnums.ObjectTypeNode) {
            os = os.getParentObjectSource();
        }
        ObjectTypeNode             otn  = (ObjectTypeNode) os;
        final ObjectTypeNodeMemory omem = wm.getNodeMemory(otn);
        if (omem == null) {
            // no OTN memory yet, i.e. no inserted matching objects, so no Tuples to process
            return;
        }

        Iterator<InternalFactHandle> it = omem.iterator();
        while (it.hasNext()) {
            InternalFactHandle fh = it.next();
            for (LeftTuple lt = fh.getFirstLeftTuple(); lt != null; lt = lt.getHandleNext()) {
                // Each lt is for a different lian, skip any lian not associated with the rule. Need to use lt parent (souce) not child to check the lian.
                if (lt.getTupleSource().isAssociatedWith(rule)) {
                    SegmentMemory childSmem = sm;
                    if (sm.getFirst() != null && sm.getFirst().getRootNode() == lt.getTupleSink()) {
                        // child lt sink is root of next segment, so assign. This happens when the Lian is in a segment of it's own
                        childSmem = sm.getFirst();
                    }
                    visitChild(lt, childSmem, insert, wm, rule);
                }
            }
        }
    }

    private static void visitChild(LeftTuple lt, SegmentMemory smem, boolean insert, InternalWorkingMemory wm, Rule rule) {
        LeftTuple prevLt = null;
        for (; lt != null; lt = lt.getPeer()) {
            boolean ltWasDeleted = false;

            if (lt.getTupleSink().isAssociatedWith(rule)) {
                if (lt.getTupleSink().getAssociatedRuleSize() > 1) {

                    if (lt.getFirstChild() != null) {
                        SegmentMemory childSmem = smem; // if there is no split the child smem is same as current node

                        if (lt.getFirstChild().getPeer() != null) {
                            // There is a network split, so must use child smem
                            childSmem = smem.getFirst();
                        }

                        visitChild(lt.getFirstChild(), childSmem, insert, wm, rule);
                    }

                } else if (!insert) {
                    // this sink is not shared and is associated with the rule being removed delete it's children
                    deletePeerLeftTuple(lt, prevLt, smem);
                    ltWasDeleted = true;
                }
            } else if (insert) {
                // There are more sinks after this peer LT, but there is no additional peer, so create it
                if ((lt.getPeer() == null && ((LeftTupleSinkNode) lt.getTupleSink()).getNextLeftTupleSinkNode() != null)) {
                    insertPeerLeftTuple(lt, ((LeftTupleSinkNode) lt.getTupleSink()).getNextLeftTupleSinkNode(), wm);
                    return; // must return as as just added a peer to lt, and it'll end up processing the newly added peer, which is not needed
                }
            }


            if (smem != null) {
                // will go null when it reaches an LT for a newly added sink, as these need to be initialised
                smem = smem.getNext();
            }
            if (!ltWasDeleted) {
                // if the lt was deleted, the prevLt is still the prevLt
                prevLt = lt;
            }
        }
    }


    /**
     * Create all missing peers
     */
    private static void insertPeerLeftTuple(LeftTuple lt, LeftTupleSinkNode node, InternalWorkingMemory wm) {
        LeftInputAdapterNode.LiaNodeMemory liaMem = null;
        if ( node.getLeftTupleSource().getType() == NodeTypeEnums.LeftInputAdapterNode ) {
            liaMem = wm.getNodeMemory(((LeftInputAdapterNode) node.getLeftTupleSource()));
        }
        for (; node != null; node = node.getNextLeftTupleSinkNode()) {
            lt = node.createPeer(lt);
            Memory memory = wm.getNodeMemories().peekNodeMemory(node.getId());
            if (memory == null || memory.getSegmentMemory() == null) {
                throw new IllegalStateException("Defensive Programming: this should not be possilbe, as the addRule code should init child segments if they are needed ");
            }


            if ( liaMem == null) {
                memory.getSegmentMemory().getStagedLeftTuples().addInsert(lt);
            } else {
                // If parent is Lian, then this must be called, so that any linking or unlinking can be done.
                LeftInputAdapterNode.doInsertSegmentMemory(wm, true, liaMem, memory.getSegmentMemory(), lt, node.getLeftTupleSource().isStreamMode());
            }
        }
    }

    private static void deletePeerLeftTuple(LeftTuple lt, LeftTuple prevLt, SegmentMemory smem) {
        switch (lt.getStagedType()) {
            case LeftTuple.INSERT: {
                // insert was never propagated, thus has no children, does not need to be staged.
                smem.getStagedLeftTuples().removeInsert(lt);
                break;
            }
            case LeftTuple.UPDATE: {
                smem.getStagedLeftTuples().removeUpdate(lt);
                // don't break, so that this falls through and calls addDelete
            }
            case LeftTuple.NONE: {
                smem.getStagedLeftTuples().addDelete(lt);
            }
            case LeftTuple.DELETE: {
                // do nothing, leave it staged for delete, added for documention help
            }
        }

        if (prevLt == null) {
            // the first sink is being removed, which is the first peer. The next peer must be set as the first peer.
            if (lt.getPeer() != null) {
                deleteLeftTuple(lt);

            } else {
                // no peers to support this, so remove completely.
                lt.unlinkFromLeftParent();
                lt.unlinkFromRightParent();
            }
        } else {
            // mid or end LeftTuple peer is being removed
            prevLt.setPeer(lt.getPeer());
        }
    }

    private static void deleteLeftTuple(LeftTuple oldLt) {
        LeftTuple newLt    = oldLt.getPeer();
        boolean   isHandle = oldLt.getLeftParent() == null;

        LeftTuple leftPrevious = oldLt.getHandlePrevious();
        LeftTuple leftNext     = oldLt.getHandleNext();

        LeftTuple rightPrevious = oldLt.getRightParentPrevious();
        LeftTuple rightNext     = oldLt.getRightParentNext();


        InternalFactHandle fh          = oldLt.getFactHandle();
        LeftTuple          leftParent  = oldLt.getLeftParent();
        RightTuple         rightParent = oldLt.getRightParent();

        newLt.setLeftParent(oldLt.getLeftParent());
        newLt.setRightParent(oldLt.getRightParent());

        // replace left
        if (leftPrevious == null && leftNext == null) {
            // no other tuples, simply replace
            if (isHandle) {
                fh.removeLeftTuple(oldLt);
                fh.addFirstLeftTuple(newLt);
            } else {
                oldLt.unlinkFromLeftParent();
                leftParent.setFirstChild(newLt);
                leftParent.setLastChild(newLt);
            }
        } else if (leftNext != null) {
            // replacing first
            newLt.setHandleNext(leftNext);
            leftNext.setHandlePrevious(newLt);
            if (isHandle) {
                fh.setFirstLeftTuple(newLt);
            } else {
                leftParent.setFirstChild(newLt);
            }
        } else {
            // replacing last
            newLt.setHandlePrevious(leftPrevious);
            leftPrevious.setHandleNext(newLt);
            if (isHandle) {
                fh.setLastLeftTuple(newLt);
            } else {
                leftParent.setLastChild(newLt);
            }
        }

        // replace right
        if (rightParent != null) {
            // LiaNode LeftTuples have no right parents
            if (rightPrevious == null && rightNext == null) {
                // no other tuples, simply replace
                oldLt.unlinkFromRightParent();
                rightParent.setFirstChild(newLt);
                rightParent.setLastChild(newLt);
            } else if (rightNext != null) {
                // replacing first
                newLt.setRightParentNext(rightNext);
                rightNext.setRightParentPrevious(newLt);
                rightParent.setFirstChild(newLt);
            } else {
                // replacing last
                newLt.setRightParentPrevious(rightPrevious);
                rightPrevious.setRightParentNext(newLt);
                rightParent.setLastChild(newLt);
            }
        }
    }

    private static LeftTupleNode getNetworkSplitPoint(LeftTupleNode node, Rule rule) {
        while (node.getType() != NodeTypeEnums.LeftInputAdapterNode && node.getAssociatedRuleSize() == 1) {
            node = node.getLeftTupleSource();
        }

        return node;
    }

    public static SegmentMemory splitSegment(SegmentMemory sm1, LeftTupleNode splitNode) {
        // create new segment, starting after split
        SegmentMemory sm2 = new SegmentMemory(splitNode.getSinkPropagator().getFirstLeftTupleSink()); // we know there is only one sink

        // Move the children of sm1 to sm2
        if (sm1.getFirst() != null) {
            for (SegmentMemory sm = sm1.getFirst(); sm != null; ) {
                SegmentMemory next = sm.getNext();
                sm1.remove(sm);
                sm2.add(sm);
                sm = next;
            }
        }

        sm1.add(sm2);

        sm2.setPos(sm1.getPos());  // clone for now, it's corrected later
        sm2.setSegmentPosMaskBit(sm1.getSegmentPosMaskBit()); // clone for now, it's corrected later
        sm2.setLinkedNodeMask(sm1.getLinkedNodeMask());  // clone for now, it's corrected later

        sm2.mergePathMemories(sm1);

        // re-assigned tip nodes
        sm2.setTipNode(sm1.getTipNode());
        sm1.setTipNode(splitNode); // splitNode is now tip of original segment

        if (sm1.getTipNode().getType() == NodeTypeEnums.LeftInputAdapterNode) {
            if (!sm1.getStagedLeftTuples().isEmpty()) {
                // Segments with only LiaNode's cannot have staged LeftTuples, so move them down to the new Segment
                sm2.getStagedLeftTuples().addAll(sm1.getStagedLeftTuples());
            }
        }

        // find the pos of the node in the segment
        int pos = nodeSegmentPosition(sm1, splitNode);

        splitNodeMemories(sm1, sm2, pos);

        splitBitMasks(sm1, sm2, pos);

        correctSegmentMemoryAfterSplitOnAdd(sm2);

        return sm2;
    }

    private static void mergeSegment(SegmentMemory sm1, SegmentMemory sm2) {
        if (sm1.getTipNode().getType() == NodeTypeEnums.LeftInputAdapterNode && !sm2.getStagedLeftTuples().isEmpty()) {
            // If a rule has not been linked, lia can still have child segments with staged tuples that did not get flushed
            // these are safe to just move to the parent SegmentMemory
            sm1.getStagedLeftTuples().addAll(sm2.getStagedLeftTuples());
        }

        // sm1 may not be linked yet to sm2 because sm2 has been just created
        if (sm1.contains(sm2)) {
            sm1.remove(sm2);
        }

        if (sm2.getFirst() != null) {
            for (SegmentMemory sm = sm2.getFirst(); sm != null; ) {
                SegmentMemory next = sm.getNext();
                sm2.remove(sm);
                sm1.add(sm);
                sm = next;
            }
        }
        // re-assigned tip nodes
        sm1.setTipNode(sm2.getTipNode());

        mergeNodeMemories(sm1, sm2);

        mergeBitMasks(sm1, sm2);
    }

    private static void splitBitMasks(SegmentMemory sm1, SegmentMemory sm2, int pos) {
        int  splitPos                 = pos + 1; // +1 as zero based
        long currentAllLinkedMaskTest = sm1.getAllLinkedMaskTest();
        long currentLinkedNodeMask    = sm1.getLinkedNodeMask();
        long mask                     = (1L << splitPos) - 1;

        sm1.setAllLinkedMaskTest(mask & currentAllLinkedMaskTest);
        sm1.setLinkedNodeMask(sm1.getLinkedNodeMask() & sm1.getAllLinkedMaskTest());

        mask = currentAllLinkedMaskTest >> splitPos;
        sm2.setAllLinkedMaskTest(mask);
        sm2.setLinkedNodeMask(mask & (currentLinkedNodeMask >> splitPos));
    }

    private static void mergeBitMasks(SegmentMemory sm1, SegmentMemory sm2) {
        LinkedList<Memory> smNodeMemories2 = sm2.getNodeMemories();

        long mask = sm2.getAllLinkedMaskTest() << smNodeMemories2.size();
        sm1.setAllLinkedMaskTest(mask & sm1.getAllLinkedMaskTest());

        mask = sm2.getAllLinkedMaskTest() << smNodeMemories2.size();
        sm1.setLinkedNodeMask(mask & sm1.getLinkedNodeMask());
    }

    private static void splitNodeMemories(SegmentMemory sm1, SegmentMemory sm2, int pos) {
        LinkedList<Memory> smNodeMemories1 = sm1.getNodeMemories();
        LinkedList<Memory> smNodeMemories2 = sm2.getNodeMemories();

        Memory mem         = smNodeMemories1.getFirst();
        int    nodePosMask = 1;
        for (int i = 0, length = smNodeMemories1.size(); i < length; i++) {
            Memory next = mem.getNext();
            if (i > pos) {
                smNodeMemories1.remove(mem);
                smNodeMemories2.add(mem);
                mem.setSegmentMemory(sm2);

                // correct the NodePosMaskBit
                BetaMemory bm = null;
                if (mem instanceof AccumulateNode.AccumulateMemory) {
                    bm = ((AccumulateNode.AccumulateMemory) mem).getBetaMemory();
                } else if (mem instanceof BetaMemory) {
                    bm = (BetaMemory) mem;
                }
                if (bm != null) {  // node may not be a beta
                    bm.setNodePosMaskBit(nodePosMask);
                }
                nodePosMask = nodePosMask << 1;
            }
            mem = next;
        }
    }

    private static void mergeNodeMemories(SegmentMemory sm1, SegmentMemory sm2) {
        LinkedList<Memory> smNodeMemories1 = sm1.getNodeMemories();
        LinkedList<Memory> smNodeMemories2 = sm2.getNodeMemories();


        int nodePosMask = 1;
        for (int i = 0, length = smNodeMemories1.size(); i < length; i++) {
            nodePosMask = nodePosMask >> 1;
        }

        for (Memory mem = smNodeMemories2.getFirst(); mem != null; ) {
            Memory next = mem.getNext();
            smNodeMemories2.remove(mem);
            smNodeMemories1.add(mem);
            mem.setSegmentMemory(sm1);

            // correct the NodePosMaskBit
            BetaMemory bm = null;
            if (mem instanceof AccumulateNode.AccumulateMemory) {
                bm = ((AccumulateNode.AccumulateMemory) mem).getBetaMemory();
            } else if (mem instanceof BetaMemory) {
                bm = (BetaMemory) mem;
            }
            if (bm != null) {  // node may not be a beta
                bm.setNodePosMaskBit(nodePosMask);
            }
            nodePosMask = nodePosMask >> 1;
            mem = next;
        }
    }

    private static int nodeSegmentPosition(SegmentMemory sm1, LeftTupleNode splitNode) {
        LeftTupleNode lt = splitNode;
        int nodePos = 0;
        while (lt != sm1.getRootNode()) {
            lt = lt.getLeftTupleSource();
            nodePos++;
        }
        return nodePos;
    }


    private static boolean isUnsharedSinkForRule(Rule rule, LeftTupleNode sink) {
        return sink.getAssociatedRuleSize() == 1 && sink.isAssociatedWith(rule);
    }

    private static PathEndNodeMemories getPathEndMemories(InternalWorkingMemory wm,
                                                          PathEndNodes pathEndNodes,
                                                          boolean isRemoving) {
        PathEndNodeMemories tnMems = new PathEndNodeMemories();

        if (isRemoving) {
            List<LeftTupleNode> nodes = new ArrayList<LeftTupleNode>();
            nodes.addAll(pathEndNodes.subjectSplits);
            nodes.addAll(pathEndNodes.otherSplits);

            for (LeftTupleNode splitNode : nodes) {
                findPmemToBeFlushed( tnMems, wm.getNodeMemories().peekNodeMemory(splitNode.getId()) );
                for (LeftTupleSink sink : splitNode.getSinkPropagator().getSinks()) {
                    findPmemToBeFlushed( tnMems, wm.getNodeMemories().peekNodeMemory(sink.getId()) );
                }
            }
        }

        for (LeftTupleNode node : pathEndNodes.otherEndNodes) {
            if (node.getType() == NodeTypeEnums.RightInputAdaterNode) {
                RiaNodeMemory riaMem = (RiaNodeMemory) wm.getNodeMemories().peekNodeMemory(node.getId());
                if (riaMem != null) {
                    tnMems.otherPmems.add(riaMem.getRiaPathMemory());
                }
            } else {
                PathMemory pmem = (PathMemory) wm.getNodeMemories().peekNodeMemory(node.getId());
                if (pmem != null) {
                    tnMems.otherPmems.add(pmem);
                }
            }
        }

        tnMems.subjectPmem = (PathMemory) wm.getNodeMemories().peekNodeMemory(pathEndNodes.subjectEndNode.getId());
        if (tnMems.subjectPmem == null && !tnMems.otherPmems.isEmpty()) {
            // If "other pmem's are initialized, then the subject needs to be initialized too.
            tnMems.subjectPmem = (PathMemory) wm.getNodeMemory((MemoryFactory<Memory>) pathEndNodes.subjectEndNode);
        }

        for (LeftTupleNode node : pathEndNodes.subjectEndNodes) {
            if (node.getType() == NodeTypeEnums.RightInputAdaterNode) {
                RiaNodeMemory riaMem = (RiaNodeMemory) wm.getNodeMemories().peekNodeMemory(node.getId());
                if (riaMem != null) {
                    tnMems.subjectPmems.add(riaMem.getRiaPathMemory());
                }
            } else {
                PathMemory pmem = (PathMemory) wm.getNodeMemories().peekNodeMemory(node.getId());
                if (pmem != null) {
                    tnMems.subjectPmems.add(pmem);
                }
            }
        }

        return tnMems;
    }

    private static void findPmemToBeFlushed( PathEndNodeMemories tnMems, Memory mem ) {
        if (mem != null) {
            SegmentMemory smem = mem.getSegmentMemory();
            if (smem != null && !smem.getStagedLeftTuples().isEmpty()) {
                for (PathMemory pmem : smem.getPathMemories()) {
                    if (pmem.getRuleAgendaItem() != null) {
                        tnMems.pmemsToBeFlushed.add( pmem );
                        break;
                    }
                }
            }
        }
    }

    private static class PathEndNodeMemories {
        PathMemory subjectPmem;
        List<PathMemory> subjectPmems = new ArrayList<PathMemory>();
        List<PathMemory> otherPmems = new ArrayList<PathMemory>();
        Set<PathMemory> pmemsToBeFlushed = new HashSet<PathMemory>();
    }

    private static PathEndNodes getPathEndNodes(InternalKnowledgeBase kBase,
                                                LeftTupleNode lt,
                                                TerminalNode tn,
                                                Rule processedRule,
                                                boolean hasProtos,
                                                boolean hasWms) {
        PathEndNodes endNodes = new PathEndNodes();
        endNodes.subjectEndNode = (PathEndNode) tn;
        endNodes.subjectEndNodes.add((PathEndNode) tn);
        if (hasWms && SegmentUtilities.isTipNode(lt, null)) {
            endNodes.subjectSplit = lt;
            endNodes.subjectSplits.add(lt);
        }

        if (hasProtos) {
            invalidateRootNode( kBase, lt );
        }

        collectPathEndNodes(kBase, lt, endNodes, tn, processedRule, hasProtos, hasWms, hasProtos && isSplit(lt, processedRule));

        return endNodes;
    }

    private static void collectPathEndNodes(InternalKnowledgeBase kBase,
                                            LeftTupleNode lt,
                                            PathEndNodes endNodes,
                                            TerminalNode tn,
                                            Rule processedRule,
                                            boolean hasProtos,
                                            boolean hasWms,
                                            boolean isBelowNewSplit) {
        for (LeftTupleSink sink : lt.getSinkPropagator().getSinks()) {
            if (sink == tn) {
                continue;
            }
            if (hasProtos) {
                if (isBelowNewSplit) {
                    if (SegmentUtilities.isRootNode(sink, null)) {
                        kBase.invalidateSegmentPrototype( sink );
                    }
                } else {
                    isBelowNewSplit = isSplit(sink, processedRule);
                    if (isBelowNewSplit) {
                        invalidateRootNode( kBase, sink );
                    }
                }
            }
            if (NodeTypeEnums.isLeftTupleSource(sink)) {
                if (hasWms && SegmentUtilities.isTipNode(sink, null)) {
                    if (isUnsharedSinkForRule(tn.getRule(), sink)) {
                        endNodes.subjectSplits.add(sink);
                    } else {
                        endNodes.otherSplits.add(sink);
                    }
                }

                collectPathEndNodes(kBase, sink, endNodes, tn, processedRule, hasProtos, hasWms, isBelowNewSplit);
            } else if (NodeTypeEnums.isTerminalNode(sink)) {
                endNodes.otherEndNodes.add((PathEndNode) sink);
            } else if (NodeTypeEnums.RightInputAdaterNode == sink.getType()) {
                if (isUnsharedSinkForRule(tn.getRule(), sink)) {
                    endNodes.subjectEndNodes.add((PathEndNode) sink);
                } else {
                    endNodes.otherEndNodes.add((PathEndNode) sink);
                }

            } else {
                throw new RuntimeException("Error: Unknown Node. Defensive programming test..");
            }
        }
    }

    private static void invalidateRootNode( InternalKnowledgeBase kBase, LeftTupleNode lt ) {
        while (!SegmentUtilities.isRootNode( lt, null )) {
            lt = lt.getLeftTupleSource();
        }
        kBase.invalidateSegmentPrototype( lt );
    }

    private static class PathEndNodes {
        PathEndNode   subjectEndNode;
        LeftTupleNode subjectSplit;
        List<PathEndNode>   subjectEndNodes = new ArrayList<PathEndNode>();
        List<LeftTupleNode> subjectSplits   = new ArrayList<LeftTupleNode>();
        List<PathEndNode>   otherEndNodes   = new ArrayList<PathEndNode>();
        List<LeftTupleNode> otherSplits     = new ArrayList<LeftTupleNode>();
    }

}
