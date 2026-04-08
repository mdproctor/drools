package org.drools.core.rete.builder;

import org.drools.base.base.ObjectType;
import org.drools.base.common.RuleBasePartitionId;
import org.drools.base.reteoo.NodeTypeEnums;
import org.drools.base.rule.Declaration;
import org.drools.base.rule.GroupElement;
import org.drools.base.rule.IntervalProviderConstraint;
import org.drools.base.rule.Pattern;
import org.drools.base.rule.RuleElement;
import org.drools.base.rule.constraint.AlphaNodeFieldConstraint;
import org.drools.base.rule.constraint.BetaConstraint;
import org.drools.base.time.Interval;
import org.drools.base.time.TimeUtils;
import org.drools.core.AlphaNode;
import org.drools.core.BaseNode;
import org.drools.core.BetaNode;
import org.drools.core.time.TemporalDependencyMatrix;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class BuildUtils {
    private final Map<Class< ? >, ReteooComponentBuilder> componentBuilders = new HashMap<>();

    /**
     * Adds the given builder for the given target to the builders map
     */
    public void addBuilder(final Class< ? > target,
                           final ReteooComponentBuilder builder) {
        this.componentBuilders.put( target,
                                    builder );
    }

    /**
     * Attaches a node into the network. If a node already exists that could
     * substitute, it is used instead.
     *
     * @param context
     *            The current build context
     * @param candidate
     *            The node to attach.
     *
     * @return the actual attached node that may be the one given as parameter
     *         or eventually one that was already in the cache if sharing is enabled
     */
    public <T extends BaseNode> T attachNode(BuildContext context, T candidate) {
        BaseNode            node      = null;
        RuleBasePartitionId partition = null;
        if (candidate.getType() == NodeTypeEnums.EntryPointNode ) {
            // entry point nodes are always shared
            node = context.getRuleBase().getRete().getEntryPointNode( ((EntryPointNode) candidate).getEntryPoint() );
            // all EntryPointNodes belong to the main partition
            partition = RuleBasePartitionId.MAIN_PARTITION;
        } else if ( candidate.getType() == NodeTypeEnums.ObjectTypeNode ) {
            // object type nodes are always shared
            Map<ObjectType, ObjectTypeNode> map = context.getRuleBase().getRete().getObjectTypeNodes(context.getCurrentEntryPoint());
            if ( map != null ) {
                ObjectTypeNode otn = map.get( ((ObjectTypeNode) candidate).getObjectType() );
                if ( otn != null ) {
                    // adjusting expiration offset
                    otn.mergeExpirationOffset( (ObjectTypeNode) candidate );
                    node = otn;
                }
            }
            // all ObjectTypeNodes belong to the main partition
            partition = RuleBasePartitionId.MAIN_PARTITION;
        } else if ( isSharingEnabledForNode( context,
                                             candidate ) ) {
            if ((context.getLeftInput() != null) && NodeTypeEnums.isLeftTupleSink(candidate) ) {
                node = context.getLeftInput().getSinkPropagator().getMatchingNode(candidate);
            } else if ((context.getLeftInput() != null) && NodeTypeEnums.isObjectSink(candidate) ) {
                node = context.getLeftInput().getObjectSinkPropagator().getMatchingNode(candidate);
            } else {
                throw new RuntimeException( "This is a bug on node sharing verification. Please report to development team." );
            }
        }

        if ( node == null ) {
            // only attach() if it is a new node
            node = candidate;

            // new node, so it must be labeled
            if ( partition == null ) {
                // if it does not has a predefined label
                if ( context.getPartitionId() == null ) {
                    // if no label in current context, create one
                    context.setPartitionId( context.getRuleBase().createNewPartitionId() );
                }
                partition = context.getPartitionId();
            }
            // set node with the actual partition label
            node.setPartitionId( context, partition );
            node.attach(context);
        } else {
            // shared node found
            mergeNodes(node, candidate);
            // undo previous id assignment
            context.releaseId( candidate );
            if ( partition == null && context.getPartitionId() == null ) {
                partition = node.getPartitionId();
                // if no label in current context, create one
                context.setPartitionId( partition );
            }
        }
        // adds the node to the context list to track all added nodes
        context.getNodes().add( node );
        node.addAssociation(context.getRule(), context);
        return (T)node;
    }

    private void mergeNodes(BaseNode node, BaseNode duplicate) {
        if (node instanceof AlphaNode) {
            AlphaNodeFieldConstraint alphaConstraint = ((AlphaNode) node).getConstraint();
            alphaConstraint.addPackageNames(((AlphaNode) duplicate).getConstraint().getPackageNames());
            alphaConstraint.mergeEvaluationContext(((AlphaNode) duplicate).getConstraint());
        } else if (node instanceof BetaNode) {
            BetaConstraint[] betaConstraints = ((BetaNode) node).getConstraints();
            int              i               = 0;
            for (BetaConstraint betaConstraint : betaConstraints) {
                betaConstraint.addPackageNames(((BetaNode) duplicate).getConstraints()[i].getPackageNames());
                betaConstraint.mergeEvaluationContext(((BetaNode) duplicate).getConstraints()[i]);
                i++;
            }
        }
    }

    /**
     * Utility function to check if sharing is enabled for nodes of the given class
     */
    private boolean isSharingEnabledForNode(BuildContext context, BaseNode node) {
        if ( NodeTypeEnums.isLeftTupleSource( node )) {
            return context.getRuleBase().getRuleBaseConfiguration().isShareBetaNodes();
        } else if ( NodeTypeEnums.isObjectSource( node ) ) {
            return context.getRuleBase().getRuleBaseConfiguration().isShareAlphaNodes();
        }
        return false;
    }

    /**
     * Calculates the temporal distance between all event patterns in the given
     * subrule.
     *
     * @param groupElement the root element of a subrule being added to the rulebase
     */
    public TemporalDependencyMatrix calculateTemporalDistance(GroupElement groupElement) {
        // find the events
        List<Pattern> events = new ArrayList<>();
        selectAllEventPatterns( events,
                                groupElement );

        final int size = events.size();
        if ( size >= 1 ) {
            // create the matrix
            Interval[][] source = new Interval[size][];
            for ( int row = 0; row < size; row++ ) {
                source[row] = new Interval[size];
                for ( int col = 0; col < size; col++ ) {
                    if ( row == col ) {
                        source[row][col] = new Interval( 0,
                                                         0 );
                    } else {
                        source[row][col] = new Interval( Interval.MIN,
                                                         Interval.MAX );
                    }
                }
            }

            Interval[][] result;
            if ( size > 1 ) {
                List<Declaration> declarations = new ArrayList<>();
                int               eventIndex   = 0;
                // populate the matrix
                for ( Pattern event : events ) {
                    // references to other events are always backward references, so we can build the list as we go
                    declarations.add( event.getDeclaration() );
                    Map<Declaration, Interval> temporal = new HashMap<>();
                    gatherTemporalRelationships( event.getConstraints(),
                                                 temporal );
                    // intersects default values with the actual constrained intervals
                    for ( Map.Entry<Declaration, Interval> entry : temporal.entrySet() ) {
                        int targetIndex = declarations.indexOf( entry.getKey() );
                        Interval interval = entry.getValue();
                        source[targetIndex][eventIndex].intersect( interval );
                        Interval reverse = new Interval( interval.getUpperBound() == Long.MAX_VALUE ? Long.MIN_VALUE : -interval.getUpperBound(),
                                                         interval.getLowerBound() == Long.MIN_VALUE ? Long.MAX_VALUE : -interval.getLowerBound() );
                        source[eventIndex][targetIndex].intersect( reverse );
                    }
                    eventIndex++;
                }
                result = TimeUtils.calculateTemporalDistance(source);
            } else {
                result = source;
            }
            return new TemporalDependencyMatrix( result, events );
        }
        return null;
    }

    private void gatherTemporalRelationships(List< ? > constraints,
                                             Map<Declaration, Interval> temporal) {
        for ( Object obj : constraints ) {
            if ( obj instanceof IntervalProviderConstraint) {
                IntervalProviderConstraint constr = (IntervalProviderConstraint) obj;
                if ( constr.isTemporal() ) {
                    // if a constraint already exists, calculate the intersection
                    Declaration[] decs = constr.getRequiredDeclarations();
                    // only calculate relationships to other event patterns
                    if( decs.length > 0 && decs[0].isPatternDeclaration() && decs[0].getPattern().getObjectType().isEvent() ) {
                        Declaration target = decs[0];
                        Interval interval = temporal.get( target );
                        if ( interval == null ) {
                            interval = constr.getInterval();
                            temporal.put( target,
                                          interval );
                        } else {
                            interval.intersect( constr.getInterval() );
                        }
                    }
                }
            }
        }
    }

    private void selectAllEventPatterns(List<Pattern> events,
                                        RuleElement rce) {
        if ( rce instanceof Pattern ) {
            Pattern p = (Pattern) rce;
            if ( p.getObjectType().isEvent() ) {
                events.add( p );
            }
        }
        for ( RuleElement child : rce.getNestedElements() ) {
            selectAllEventPatterns( events,
                                    child );
        }
    }

    /**
     * Returns a builder for the given target from the builders map
     */
    public ReteooComponentBuilder getBuilderFor(final RuleElement target) {
        return getBuilderFor( target.getClass() );
    }

    public ReteooComponentBuilder getBuilderFor(final Class cls) {
        ReteooComponentBuilder builder = this.componentBuilders.get( cls );
        return builder != null || cls.getSuperclass() == null ? builder : getBuilderFor(cls.getSuperclass());
    }

}
