/*
 * Copyright 2010 Red Hat, Inc. and/or its affiliates.
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

package org.drools.core.reteoo.builder;

import org.drools.core.ActivationListenerFactory;
import org.drools.core.base.ClassObjectType;
import org.drools.core.common.BaseNode;
import org.drools.core.common.InternalWorkingMemory;
import org.drools.core.common.UpdateContext;
import org.drools.core.definitions.rule.impl.RuleImpl;
import org.drools.core.impl.InternalKnowledgeBase;
import org.drools.core.phreak.AddRemoveRule;
import org.drools.core.phreak.SegmentUtilities;
import org.drools.core.reteoo.*;
import org.drools.core.rule.Collect;
import org.drools.core.rule.ConditionalBranch;
import org.drools.core.rule.EntryPointId;
import org.drools.core.rule.EvalCondition;
import org.drools.core.rule.Forall;
import org.drools.core.rule.From;
import org.drools.core.rule.GroupElement;
import org.drools.core.rule.InvalidPatternException;
import org.drools.core.rule.MultiAccumulate;
import org.drools.core.rule.NamedConsequence;
import org.drools.core.rule.Pattern;
import org.drools.core.rule.QueryElement;
import org.drools.core.rule.SingleAccumulate;
import org.drools.core.rule.WindowDeclaration;
import org.drools.core.rule.WindowReference;
import org.drools.core.rule.constraint.XpathConstraint;
import org.drools.core.time.TemporalDependencyMatrix;
import org.drools.core.time.impl.Timer;
import org.kie.api.conf.EventProcessingOption;
import org.kie.api.definition.rule.Rule;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class ReteooRuleBuilder implements RuleBuilder {

    protected BuildUtils utils;

    public ReteooRuleBuilder() {
        this.utils = new BuildUtils();

        this.utils.addBuilder( GroupElement.class,
                               new GroupElementBuilder() );
        this.utils.addBuilder( Pattern.class,
                               new PatternBuilder() );
        this.utils.addBuilder( EvalCondition.class,
                               new EvalBuilder() );
        this.utils.addBuilder( QueryElement.class,
                               new QueryElementBuilder() );
        this.utils.addBuilder( From.class,
                               new FromBuilder() );
        this.utils.addBuilder( Collect.class,
                               new CollectBuilder() );
        this.utils.addBuilder( SingleAccumulate.class,
                               new AccumulateBuilder() );
        this.utils.addBuilder( MultiAccumulate.class,
                               new AccumulateBuilder() );
        this.utils.addBuilder( Timer.class,
                               new TimerBuilder() );
        this.utils.addBuilder( Forall.class,
                               new ForallBuilder() );
        this.utils.addBuilder( EntryPointId.class,
                               new EntryPointBuilder() );
        this.utils.addBuilder( WindowReference.class, 
                               new WindowReferenceBuilder() );
        this.utils.addBuilder( NamedConsequence.class,
                               new NamedConsequenceBuilder() );
        this.utils.addBuilder( ConditionalBranch.class,
                               new ConditionalBranchBuilder() );
        this.utils.addBuilder( XpathConstraint.class,
                               new ReactiveFromBuilder() );
    }

    /**
     * Creates the corresponting Rete network for the given <code>Rule</code> and adds it to
     * the given rule base.
     * 
     * @param rule
     *            The rule to add.
     * @param kBase
     *            The rulebase to add the rule to.
     *            
     * @return a List<BaseNode> of terminal nodes for the rule             
     * @throws InvalidPatternException
     */
    public List<TerminalNode> addRule( final RuleImpl rule,
                                        final InternalKnowledgeBase kBase,
                                        final ReteooBuilder.IdGenerator idGenerator ) throws InvalidPatternException {
        // the list of terminal nodes
        final List<TerminalNode> nodes = new ArrayList<TerminalNode>();

        // transform rule and gets the array of subrules
        final GroupElement[] subrules = rule.getTransformedLhs( kBase.getConfiguration().getComponentFactory().getLogicTransformerFactory().getLogicTransformer(),
                                                                kBase.getGlobals() );

        for (int i = 0; i < subrules.length; i++) {

            // creates a clean build context for each subrule
            final BuildContext context = new BuildContext( kBase,
                                                           idGenerator );
            context.setRule( rule );

            // if running in STREAM mode, calculate temporal distance for events
            if (EventProcessingOption.STREAM.equals( kBase.getConfiguration().getEventProcessingMode() )) {
                TemporalDependencyMatrix temporal = this.utils.calculateTemporalDistance( subrules[i] );
                context.setTemporalDistance( temporal );
            }

            if (kBase.getConfiguration().isSequential() ) {
                context.setTupleMemoryEnabled( false );
                context.setObjectTypeNodeMemoryEnabled( false );
            } else {
                context.setTupleMemoryEnabled( true );
                context.setObjectTypeNodeMemoryEnabled( true );
            }

            // adds subrule
            final TerminalNode node = this.addSubRule( context,
                                                       subrules[i],
                                                       i,
                                                       rule );

            // adds the terminal node to the list of terminal nodes
            nodes.add( node );
        }

        return nodes;
    }

    private TerminalNode addSubRule( final BuildContext context,
                                     final GroupElement subrule,
                                     final int subruleIndex,
                                     final RuleImpl rule ) throws InvalidPatternException {
        context.setSubRule(subrule);

        // gets the appropriate builder
        ReteooComponentBuilder builder = this.utils.getBuilderFor( subrule );

        // checks if an initial-fact is needed
        if (builder.requiresLeftActivation( this.utils,
                                            subrule )) {
            this.addInitialFactPattern( subrule );
        }

        // builds and attach
        builder.build( context,
                       this.utils,
                       subrule );

        if (context.isTerminated()) {
            context.setTerminated(false);
            return ((TerminalNode) context.getLastNode());
        }

        if  ( context.getKnowledgeBase().getConfiguration().isPhreakEnabled() && rule.getTimer() != null ) {
            builder = this.utils.getBuilderFor( Timer.class );
            builder.build( context, this.utils, rule.getTimer() );
        }

        ActivationListenerFactory factory = context.getKnowledgeBase().getConfiguration().getActivationListenerFactory( rule.getActivationListener() );
        TerminalNode terminal = factory.createActivationListener( context.getNextId(),
                                                                  context.getTupleSource(),
                                                                  rule,
                                                                  subrule,
                                                                  subruleIndex,
                                                                  context );

        BaseNode baseTerminalNode = (BaseNode) terminal;
        baseTerminalNode.networkUpdated(new UpdateContext());
        baseTerminalNode.attach(context);

        setPathEndNodes(context);

        // adds the terminal node to the list of nodes created/added by this sub-rule
        context.getNodes().add( baseTerminalNode );

        // assigns partition IDs to the new nodes
        //assignPartitionId(context);

        return terminal;
    }

    /**
     * Store the paths in reverse order, this represents the visual order of the graph, if you were looking at it as a tree.
     * Where the Main is far left and the outer most subnetwork is the far right, which forms the firt split.
     * Position 0 is the main path and 1 is the inner most subnetwork n-1 is the outer most subnetwork (i.e. the first split)
     * @param context
     */
    private void setPathEndNodes(BuildContext context) {
        PathEndNode[] pathEndNodes = context.getPathEndNodes().toArray(new PathEndNode[context.getPathEndNodes().size()]);
        for ( int i = 0; i < pathEndNodes.length; i++ ) {
            PathEndNode node = context.getPathEndNodes().get(pathEndNodes.length-1-i);
            node.setPathEndNodes(pathEndNodes);
            pathEndNodes[i] = node;
        }
    }

    /**
     * Creates and return the node memory
     */
    public static void initPath(PathEndNode pnode, LeftTupleNode startTupleSource, Set<Rule> removingRules, Set<Rule> addingRules, List<LeftTupleNode> subjectSplits) {
        if ( ( removingRules != null && addingRules != null) || ( removingRules != null && addingRules != null ) ) {
            throw new IllegalArgumentException("");
        }
        int counter = 1;
        long allLinkedTestMask = 0;

        boolean isSplit = false;
        LeftTupleSource tupleSource = pnode.getLeftTupleSource();
        if ( SegmentUtilities.isRootNode(pnode, removingRules)) {
            counter++;
        }
        recordIfSplitChange(pnode, subjectSplits, addingRules, isSplit);
        boolean wasSplit;

        ConditionalBranchNode cen = getConditionalBranchNode(tupleSource); // segments after a branch CE can notify, but they cannot impact linking
        // @TODO optimization would be to split path's into two, to avoid wasted rule evaluation for segments after the first branch CE

        boolean updateBitInNewSegment = true; // Avoids more than one isBetaNode check per segment
        boolean updateAllLinkedTest = cen == null; // if there is a CEN, do not set bit until it's reached
        boolean subnetworkBoundaryCrossed = false;

        while (  tupleSource.getType() != NodeTypeEnums.LeftInputAdapterNode ) {
            if ( !subnetworkBoundaryCrossed &&  tupleSource.getType() == NodeTypeEnums.ConditionalBranchNode ) {
                // start recording now we are after the BranchCE, but only if we are not outside the target
                // subnetwork
                updateAllLinkedTest = true;
            }

            if ( updateAllLinkedTest && updateBitInNewSegment &&
                 NodeTypeEnums.isBetaNode( tupleSource ) &&
                 NodeTypeEnums.AccumulateNode != tupleSource.getType()) { // accumulates can never be disabled
                BetaNode bn = ( BetaNode) tupleSource;
                if ( bn.isRightInputIsRiaNode() ) {
                    updateBitInNewSegment = false;
                    PathEndNode rian = ( PathEndNode ) bn.getRightInput();
                    if ( rian.getAllLinkedMaskTest() == -1 ) {
                        throw new IllegalStateException("Defensive Programming. Make sure subnetworks are initialized first. Can we remove this later (mdp)");
                    }

                    if ( rian.getAllLinkedMaskTest() != 0 ) {
                        allLinkedTestMask = allLinkedTestMask | 1;
                    }
                } else if ( NodeTypeEnums.NotNode != bn.getType() || ((NotNode)bn).isEmptyBetaConstraints()) {
                    updateBitInNewSegment = false;
                    // non empty not nodes can never be disabled and thus don't need checking
                    allLinkedTestMask = allLinkedTestMask | 1;
                }
            }

            isSplit = false;
            if ( SegmentUtilities.isRootNode( tupleSource, removingRules ) ) {
                // is split
                isSplit = true;
                updateBitInNewSegment = true; // allow bit to be set for segment
                allLinkedTestMask = allLinkedTestMask << 1;
                counter++;
            }
            recordIfSplitChange(pnode, subjectSplits, addingRules, isSplit);

            tupleSource = tupleSource.getLeftTupleSource();
            if ( tupleSource == startTupleSource ) {
                // stop tracking if we move outside of a subnetwork boundary (if one is set)
                subnetworkBoundaryCrossed = true;
                updateAllLinkedTest = false;
            }
        }

        if ( !subnetworkBoundaryCrossed ) {
            allLinkedTestMask = allLinkedTestMask | 1;
        }

        pnode.setSegmentSize(counter);
        pnode.setAllLinkedMaskTest(allLinkedTestMask);
    }

    private static void recordIfSplitChange(LeftTupleNode node, List<LeftTupleNode> subjectSplits, Set<Rule> addingRules, boolean isSplit) {
        boolean wasSplit = SegmentUtilities.isRootNode(node, addingRules);
        if ((isSplit ^ wasSplit)) {
            // record split change. Add parent, as we consider the tip of previous segment as the single reference for a split
            subjectSplits.add(node.getLeftTupleSource());
        }
    }

    private static ConditionalBranchNode getConditionalBranchNode(LeftTupleSource tupleSource) {
        ConditionalBranchNode cen = null;
        while (  tupleSource.getType() != NodeTypeEnums.LeftInputAdapterNode ) {
            // find the first ConditionalBranch, if one exists
            if ( tupleSource.getType() == NodeTypeEnums.ConditionalBranchNode ) {
                cen =  ( ConditionalBranchNode ) tupleSource;
            }
            tupleSource = tupleSource.getLeftTupleSource();
        }
        return cen;
    }

    /**
     * Adds a query pattern to the given subrule
     * 
     * @param subrule
     */
    private void addInitialFactPattern( final GroupElement subrule ) {

        // creates a pattern for initial fact
        final Pattern pattern = new Pattern( 0,
                                             ClassObjectType.InitialFact_ObjectType );

        // adds the pattern as the first child of the given AND group element
        subrule.addChild( 0,
                          pattern );
    }

    public void addEntryPoint( final String id,
            final InternalKnowledgeBase kBase,
            final ReteooBuilder.IdGenerator idGenerator ) {
        // creates a clean build context for each subrule
        final BuildContext context = new BuildContext( kBase,
                                                       idGenerator );
        EntryPointId ep = new EntryPointId( id );
        ReteooComponentBuilder builder = utils.getBuilderFor( ep );
        builder.build(context,
                utils,
                ep);
    }

    public WindowNode addWindowNode( WindowDeclaration window,
                                     InternalKnowledgeBase kBase,
                                     ReteooBuilder.IdGenerator idGenerator ) {
        // creates a clean build context for each subrule
        final BuildContext context = new BuildContext( kBase,
                                                       idGenerator );
        
        if ( kBase.getConfiguration().isSequential() ) {
            context.setTupleMemoryEnabled( false );
            context.setObjectTypeNodeMemoryEnabled( false );
        } else {
            context.setTupleMemoryEnabled( true );
            context.setObjectTypeNodeMemoryEnabled( true );
        }
        
        // gets the appropriate builder
        final WindowBuilder builder = WindowBuilder.INSTANCE;

        // builds and attach
        builder.build( context,
                       this.utils,
                       window );

        return (WindowNode) context.getObjectSource();
    }

}
