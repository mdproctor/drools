/*
 * Copyright 2005 Red Hat, Inc. and/or its affiliates.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.drools.core.reteoo;

import org.drools.core.common.BaseNode;
import org.drools.core.common.DroolsObjectInputStream;
import org.drools.core.common.DroolsObjectOutputStream;
import org.drools.core.common.InternalWorkingMemory;
import org.drools.core.common.MemoryFactory;
import org.drools.core.definitions.rule.impl.RuleImpl;
import org.drools.core.impl.InternalKnowledgeBase;
import org.drools.core.phreak.AddRemoveRule;
import org.drools.core.reteoo.builder.ReteooRuleBuilder;
import org.drools.core.rule.InvalidPatternException;
import org.drools.core.rule.WindowDeclaration;
import org.kie.api.definition.rule.Query;
import org.kie.api.definition.rule.Rule;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.Externalizable;
import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.*;

/**
 * Builds the Rete-OO network for a <code>Package</code>.
 *
 */
public class ReteooBuilder
        implements
        Externalizable {
    // ------------------------------------------------------------
    // Instance members
    // ------------------------------------------------------------

    private static final long           serialVersionUID = 510l;

    /** The RuleBase */
    private transient InternalKnowledgeBase kBase;

    private Map<String, PathEndNode[]>      rules;
    private Map<String, PathEndNode[]>      queries;

    private Map<String, WindowNode>         namedWindows;

    private transient RuleBuilder        ruleBuilder;

    private IdGenerator                  idGenerator;

    Set<Rule> removingRules;
    Set<Rule> addingRules;


    // ------------------------------------------------------------
    // Constructors
    // ------------------------------------------------------------

    public ReteooBuilder() {
    }

    /**
     * Construct a <code>Builder</code> against an existing <code>Rete</code>
     * network.
     */
    public ReteooBuilder( final InternalKnowledgeBase  kBase ) {
        this.kBase = kBase;
        this.rules = new HashMap<String, PathEndNode[]>();
        this.queries = new HashMap<String, PathEndNode[]>();
        this.namedWindows = new HashMap<String, WindowNode>();
        initTransient();

        //Set to 1 as Rete node is set to 0
        this.idGenerator = new IdGenerator( 1 );
        this.ruleBuilder = kBase.getConfiguration().getComponentFactory().getRuleBuilderFactory().newRuleBuilder();
    }

    private void initTransient() {
        Set<Rule> removingRules = new HashSet<Rule>();
        Set<Rule> addingRules = new HashSet<Rule>();

    }


    public void writeExternal(ObjectOutput out) throws IOException {
        boolean isDrools = out instanceof DroolsObjectOutputStream;
        DroolsObjectOutputStream droolsStream;
        ByteArrayOutputStream bytes;

        if ( isDrools ) {
            bytes = null;
            droolsStream = (DroolsObjectOutputStream) out;
        } else {
            bytes = new ByteArrayOutputStream();
            droolsStream = new DroolsObjectOutputStream( bytes );
        }
        droolsStream.writeObject( rules );
        droolsStream.writeObject( queries );
        droolsStream.writeObject( namedWindows );
        droolsStream.writeObject( idGenerator );
        if ( !isDrools ) {
            droolsStream.flush();
            droolsStream.close();
            bytes.close();
            out.writeInt( bytes.size() );
            out.writeObject( bytes.toByteArray() );
        }
    }

    public void readExternal(ObjectInput in) throws IOException,
            ClassNotFoundException {
        boolean isDrools = in instanceof DroolsObjectInputStream;
        DroolsObjectInputStream droolsStream;
        ByteArrayInputStream bytes;

        if ( isDrools ) {
            bytes = null;
            droolsStream = (DroolsObjectInputStream) in;
        } else {
            bytes = new ByteArrayInputStream( (byte[]) in.readObject() );
            droolsStream = new DroolsObjectInputStream( bytes );
        }

        this.rules = (Map<String, PathEndNode[]>) droolsStream.readObject();
        this.queries = (Map<String, PathEndNode[]>) droolsStream.readObject();
        this.namedWindows = (Map<String, WindowNode>) droolsStream.readObject();
        this.idGenerator = (IdGenerator) droolsStream.readObject();
        if ( !isDrools ) {
            droolsStream.close();
            bytes.close();
        }

        initTransient();

    }

    // ------------------------------------------------------------
    // Instance methods
    // ------------------------------------------------------------



    /**
     * Add a <code>Rule</code> to the network.
     *
     * @param rule
     *            The rule to add.
     * @throws InvalidPatternException
     */
    public synchronized void addRule(final RuleImpl rule) throws InvalidPatternException {
        final List<TerminalNode> terminals = this.ruleBuilder.addRule( rule,
                                                                       kBase,
                                                                       idGenerator );

        PathEndNode[] nodes = terminals.toArray( new PathEndNode[terminals.size()] );
        this.rules.put( rule.getFullyQualifiedName(), nodes );
        if (rule.isQuery()) {
            this.queries.put( rule.getName(), nodes );
        }
    }

    public void initRules() {
        List<LeftTupleNode> subjectSplits = new ArrayList<LeftTupleNode>();

        Map<Integer, LeftTupleNode> convergencePoints = new HashMap<Integer, LeftTupleNode>();
        Map<Integer, LeftTupleNode> convergencePaths = new HashMap<Integer, LeftTupleNode>();
        if (kBase.getConfiguration().isPhreakEnabled()) {
            for ( Rule rule : addingRules ) {
                for (PathEndNode tn : rules.get(((RuleImpl)rule).getFullyQualifiedName())) {
                    AddRemoveRule.getConvergence(tn, convergencePaths, convergencePoints);
                }
            }
        }


        for ( LeftTupleNode convergencePoint :  convergencePoints.values() ) {
            Collection<Rule> rules = convergencePoint.getAssociatedRules();
            for ( Rule rule : rules ) {
                //initPaths(rule, convergencePoint, null, addingRules, subjectSplits);
            }
        }


        //PathEndNode[] pnodes = rtn.getPathEndNodes();
//                LeftTupleNode ltn = pnodes[0];
//                while( ltn != null ) {
//                    ltn = ltn.getLeftTupleSource();
//                }

        //AddRemoveRule.addRule(rtn,  kBase.getWorkingMemories(), kBase);


//
//        Set<Rule> stillToAdd = new HashSet<Rule>();
//        stillToAdd.addAll(addedRules);
//
//
//        Set<PathEndNode> visited = new HashSet<PathEndNode>();
//        for ( LeftTupleNode splitNode : addedSplits ) {
//            for ( Rule rule : splitNode.getAssociatedRules() ) {
//                if ( removedRules.contains(rule)) {
//                    // don't update the paths of rules being removed
//                    continue;
//                }
//                addedRules.remove(rule); // we don't want to process this twice
//
//                initPaths((RuleImpl)rule, splitNode,visited);
//            }
//        }
//
//        for ( LeftTupleNode splitNode : removedSplits ) {
//            for ( Rule rule : splitNode.getAssociatedRules() ) {
//                if ( removedRules.contains(rule)) {
//                    // don't update the paths of rules being removed
//                    continue;
//                }
//                addedRules.remove(rule); // we don't want to process this twice
//
//                initPaths((RuleImpl)rule, splitNode,visited);
//            }
//        }
//
//        for ( Rule rule : stillToAdd ) {
//            initPaths((RuleImpl)rule, visited);
//        }

    }
//
//    public static class SplitIndexEntry {
//        List<LeftTupleNode> list = new ArrayList<LeftTupleNode>();
//
//    }
//
//    private Map<Integer, Integer> splitIndex = new HashMap<Integer, Integer>();
//
//    private void buildSplitIndex() {
//        for ( LeftTupleNode splitNode : addedSplits ) {
//            for ( LeftTupleNode parent = splitNode.getLeftTupleSource(); parent != null; parent = parent.getLeftTupleSource() ) {
//                splitIndex.put(parent.getId(), null);
//            }
//        }
//    }
//
//    private void initPaths(RuleImpl rule, Set<PathEndNode> visited) {
//        initPaths(rule, null, visited);
//    }
//
    private void initPaths(Rule rule, LeftTupleNode convergenceNode, Set<Rule> removingRules, Set<Rule> addingRules, List<LeftTupleNode> subjectSplits, List<PathEndNode> pathEnds) {
        PathEndNode[] rtnNodes = rules.get(((RuleImpl)rule).getFullyQualifiedName());
        initPaths(rtnNodes, convergenceNode, removingRules, addingRules, subjectSplits, pathEnds);
    }

    public static void initPaths( PathEndNode[] rtnNodes, LeftTupleNode convergenceNode, Set<Rule> removingRules, Set<Rule> addingRules, List<LeftTupleNode> subjectSplits, List<PathEndNode> pathEnds) {
        for ( PathEndNode rtnNode : rtnNodes ) {
            PathEndNode[] endNodes = rtnNode.getPathEndNodes();
            for ( int i = endNodes.length-1; i >= 0; i--) {
                // must initialize from the outer most subnetwork first, going inwards only. i.e. from the graph visual of right to left
                PathEndNode   endNode = endNodes[i];

                // Ensure only descendant PathEndNodes are processed, i.e. those impacted by the convergenceNode.
                // If their descendant splits, this work subsumes those, and they need to be skipped
                if ( convergenceNode.getPositionInPath() < endNode.getPathNodes().length && endNode.getPathNodes()[convergenceNode.getPositionInPath()] == convergenceNode ) {
                    LeftTupleNode startLeftTupleNode = null;
                    if (endNode.getType() == NodeTypeEnums.RightInputAdaterNode) {
                        startLeftTupleNode = ((RightInputAdapterNode) endNode).getStartTupleSource();
                    }
                    pathEnds.add( endNode );
                    ReteooRuleBuilder.initPath(endNode, startLeftTupleNode, removingRules, addingRules, subjectSplits);
                }
            }
        }
    }

    public void addEntryPoint( String id ) {
        this.ruleBuilder.addEntryPoint( id,
                                        this.kBase,
                                        this.idGenerator );
    }

    public synchronized void addNamedWindow( WindowDeclaration window ) {
        final WindowNode wnode = this.ruleBuilder.addWindowNode( window,
                                                                 this.kBase,
                                                                 this.idGenerator );

        this.namedWindows.put( window.getName(),
                               wnode );
    }

    public WindowNode getWindowNode( String name ) {
        return this.namedWindows.get( name );
    }

    public IdGenerator getIdGenerator() {
        return this.idGenerator;
    }
    public synchronized PathEndNode[] getTerminalNodes(final String fullyQualifiedName) {
        return this.rules.get( fullyQualifiedName );
    }

    public synchronized PathEndNode[] getTerminalNodesForQuery(final String ruleName) {
        PathEndNode[] nodes = this.queries.get( ruleName );
        if ( nodes == null || nodes.length == 0 ) {
            throw new  IllegalStateException("Defensive Programming: removed some logic that shouldn't happen, so added defensive check, until we are sure it can be removed (mdp)");
        }
        return nodes;
    }

    public synchronized Map<String, PathEndNode[]> getTerminalNodes() {
        return this.rules;
    }

    public synchronized void removeRule(final RuleImpl rule) {
        // reset working memories for potential propagation
        InternalWorkingMemory[] workingMemories = this.kBase.getWorkingMemories();

        final RuleRemovalContext context = new RuleRemovalContext( kBase, rule );
        context.setKnowledgeBase(kBase);

        for (PathEndNode node : rules.remove( rule.getFullyQualifiedName() )) {
            removeTerminalNode(context, (TerminalNode) node, workingMemories);
        }

        if (rule.isQuery()) {
            this.queries.remove( rule.getName() );
        }
    }

    public void removeTerminalNode(RuleRemovalContext context, TerminalNode tn, InternalWorkingMemory[] workingMemories)  {
        if ( this.kBase.getConfiguration().isPhreakEnabled() ) {
            AddRemoveRule.removeRule( tn, workingMemories, kBase );
        }

        RuleRemovalContext.CleanupAdapter adapter = null;
        if ( !this.kBase.getConfiguration().isPhreakEnabled() ) {
            if ( tn instanceof RuleTerminalNode) {
                adapter = new RuleTerminalNode.RTNCleanupAdapter( (RuleTerminalNode) tn );
            }
            context.setCleanupAdapter( adapter );
        }

        BaseNode node = (BaseNode) tn;
        removeNodeAssociation(node, context.getRule());

        resetMasks(removeNodes((AbstractTerminalNode)tn, workingMemories, context));
    }

    private Collection<BaseNode> removeNodes(AbstractTerminalNode terminalNode, InternalWorkingMemory[] wms, RuleRemovalContext context) {
        Map<Integer, BaseNode> stillInUse = new HashMap<Integer, BaseNode>();
        Collection<ObjectSource> alphas = new HashSet<ObjectSource>();

        removePath(wms, context, stillInUse, alphas, terminalNode);

        Set<Integer> removedNodes = new HashSet<Integer>();
        for (ObjectSource alpha : alphas) {
            removeObjectSource( wms, stillInUse, removedNodes, alpha, context );
        }

        return stillInUse.values();
    }

    /**
     * Path's must be removed starting from the outer most path, iterating towards the inner most path.
     * Each time it reaches a subnetwork beta node, the current path evaluation ends, and instead the subnetwork
     * path continues.
     */
    private void removePath( InternalWorkingMemory[] wms, RuleRemovalContext context, Map<Integer, BaseNode> stillInUse, Collection<ObjectSource> alphas, PathEndNode endNode ) {
        LeftTupleNode[] nodes = endNode.getPathNodes();
        for (int i = endNode.getPositionInPath(); i >= 0; i--) {
            BaseNode node = (BaseNode) nodes[i];

            boolean removed = false;
            if ( NodeTypeEnums.isLeftTupleNode( node ) ) {
                removed = removeLeftTupleNode(wms, context, stillInUse, node);
            }

            if ( removed || !kBase.getConfiguration().isPhreakEnabled() ) {
                // reteoo requires to call remove on the OTN for tuples cleanup
                if (NodeTypeEnums.isBetaNode(node) && !((BetaNode) node).isRightInputIsRiaNode()) {
                    alphas.add(((BetaNode) node).getRightInput());
                } else if (node.getType() == NodeTypeEnums.LeftInputAdapterNode) {
                    alphas.add(((LeftInputAdapterNode) node).getObjectSource());
                }
            }

            if (NodeTypeEnums.isBetaNode(node) && ((BetaNode) node).isRightInputIsRiaNode()) {
                endNode = (PathEndNode) ((BetaNode) node).getRightInput();
                removePath(wms, context, stillInUse, alphas, endNode);
                return;
            }
        }
    }

    private boolean removeLeftTupleNode(InternalWorkingMemory[] wms, RuleRemovalContext context, Map<Integer, BaseNode> stillInUse, BaseNode node) {
        boolean removed;
        removed = node.remove(context, this, wms);

        if (removed) {
            stillInUse.remove( node.getId() );
            if (kBase.getConfiguration().isPhreakEnabled()) {
                // phreak must clear node memories, although this should ideally be pushed into AddRemoveRule
                for (InternalWorkingMemory workingMemory : wms) {
                    workingMemory.clearNodeMemory((MemoryFactory) node);
                }
            }
        } else {
            stillInUse.put( node.getId(), node );
        }

        return removed;
    }

    private void removeObjectSource(InternalWorkingMemory[] wms, Map<Integer, BaseNode> stillInUse, Set<Integer> removedNodes, ObjectSource node, RuleRemovalContext context ) {
        if (removedNodes.contains( node.getId() )) {
            return;
        }
        ObjectSource parent = node.getParentObjectSource();

        boolean removed = node.remove( context, this, wms );

        if ( !removed ) {
            stillInUse.put( node.getId(), node );
            if (!kBase.getConfiguration().isPhreakEnabled()) {
                // reteoo requires to call remove on the OTN for tuples cleanup
                if (parent != null && parent.getType() != NodeTypeEnums.EntryPointNode) {
                    removeObjectSource(wms, stillInUse, removedNodes, parent, context);
                }
            }
        } else {
            stillInUse.remove(node.getId());
            removedNodes.add(node.getId());

            if ( node.getType() != NodeTypeEnums.ObjectTypeNode &&
                 node.getType() != NodeTypeEnums.AlphaNode &&
                 kBase.getConfiguration().isPhreakEnabled() ) {
                // phreak must clear node memories, although this should ideally be pushed into AddRemoveRule
                for (InternalWorkingMemory workingMemory : wms) {
                    workingMemory.clearNodeMemory( (MemoryFactory) node);
                }
            }

            if (parent != null && parent.getType() != NodeTypeEnums.EntryPointNode) {
                removeObjectSource(wms, stillInUse, removedNodes, parent, context);
            }
        }
    }

    private void removeNodeAssociation(BaseNode node, Rule rule) {
        if (node == null || !node.removeAssociation( rule )) {
            return;
        }
        if (node instanceof LeftTupleNode) {
            removeNodeAssociation( ((LeftTupleNode)node).getLeftTupleSource(), rule );
        }
        if ( NodeTypeEnums.isBetaNode( node ) ) {
            removeNodeAssociation( ((BetaNode) node).getRightInput(), rule );
        } else if ( node.getType() == NodeTypeEnums.LeftInputAdapterNode ) {
            removeNodeAssociation( ((LeftInputAdapterNode) node).getObjectSource(), rule );
        } else if ( node.getType() == NodeTypeEnums.AlphaNode ) {
            removeNodeAssociation( ((AlphaNode) node).getParentObjectSource(), rule );
        }
    }

    private void resetMasks(Collection<BaseNode> nodes) {
        NodeSet leafSet = new NodeSet();

        for ( BaseNode node : nodes ) {
            if ( node.getType() == NodeTypeEnums.AlphaNode ) {
                ObjectSource source = (AlphaNode) node;
                while ( true ) {
                    source.resetInferredMask();
                    BaseNode parent = source.getParentObjectSource();
                    if (parent.getType() != NodeTypeEnums.AlphaNode) {
                        break;
                    }
                    source = (ObjectSource)parent;
                }
                updateLeafSet(source, leafSet );
            } else if( NodeTypeEnums.isBetaNode( node ) ) {
                BetaNode betaNode = ( BetaNode ) node;
                if ( betaNode.isInUse() ) {
                    leafSet.add( betaNode );
                }
            } else if ( NodeTypeEnums.isTerminalNode( node )  ) {
                RuleTerminalNode rtNode = ( RuleTerminalNode ) node;
                if ( rtNode.isInUse() ) {
                    leafSet.add( rtNode );
                }
            }
        }

        for ( BaseNode node : leafSet ) {
            if ( NodeTypeEnums.isTerminalNode( node ) ) {
                ((TerminalNode)node).initInferredMask();
            } else { // else node instanceof BetaNode
                ((BetaNode)node).initInferredMask();
            }
        }
    }

    private void updateLeafSet(BaseNode baseNode, NodeSet leafSet) {
        if ( baseNode.getType() == NodeTypeEnums.AlphaNode ) {
            for ( ObjectSink sink : ((AlphaNode) baseNode).getObjectSinkPropagator().getSinks() ) {
                if ( ((BaseNode)sink).isInUse() ) {
                    updateLeafSet( ( BaseNode ) sink, leafSet );
                }
            }
        } else  if ( baseNode.getType() ==  NodeTypeEnums.LeftInputAdapterNode ) {
            for ( LeftTupleSink sink : ((LeftInputAdapterNode) baseNode).getSinkPropagator().getSinks() ) {
                if ( sink.getType() ==  NodeTypeEnums.RuleTerminalNode ) {
                    leafSet.add( (BaseNode) sink );
                } else if ( ((BaseNode)sink).isInUse() ) {
                    updateLeafSet( ( BaseNode ) sink, leafSet );
                }
            }
        } else if ( baseNode.getType() == NodeTypeEnums.EvalConditionNode ) {
            for ( LeftTupleSink sink : ((EvalConditionNode) baseNode).getSinkPropagator().getSinks() ) {
                if ( ((BaseNode)sink).isInUse() ) {
                    updateLeafSet( ( BaseNode ) sink, leafSet );
                }
            }
        } else if ( NodeTypeEnums.isBetaNode( baseNode ) ) {
            if ( baseNode.isInUse() ) {
                leafSet.add( baseNode );
            }
        }
    }

    public static class IdGenerator
            implements
            Externalizable {

        private static final long serialVersionUID = 510l;

        private Queue<Integer>    recycledIds;
        private int               nextId;

        public IdGenerator() {
        }

        public IdGenerator(final int firstId) {
            this.nextId = firstId;
            this.recycledIds = new LinkedList<Integer>();
        }

        @SuppressWarnings("unchecked")
        public void readExternal(ObjectInput in) throws IOException,
                                                        ClassNotFoundException {
            recycledIds = (Queue<Integer>) in.readObject();
            nextId = in.readInt();
        }

        public void writeExternal(ObjectOutput out) throws IOException {
            out.writeObject( recycledIds );
            out.writeInt( nextId );
        }

        public synchronized int getNextId() {
            Integer id = this.recycledIds.poll();
            return ( id == null ) ? this.nextId++ : id;
        }

        public synchronized void releaseId(int id) {
            this.recycledIds.add( id );
        }

        public int getLastId() {
            return this.nextId - 1;
        }

    }

    public void setRuleBase( InternalKnowledgeBase kBase ) {
        this.kBase = kBase;

        this.ruleBuilder = kBase.getConfiguration().getComponentFactory().getRuleBuilderFactory().newRuleBuilder();
    }

}