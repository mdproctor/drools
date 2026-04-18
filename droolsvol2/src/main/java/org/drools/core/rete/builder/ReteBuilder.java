package org.drools.core.rete.builder;


import org.drools.base.base.ClassObjectType;
import org.drools.base.common.NetworkNode;
import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.base.rule.EntryPointId;
import org.drools.base.rule.GroupElement;
import org.drools.base.rule.Pattern;
import org.drools.base.rule.InvalidPatternException;
import org.drools.base.rule.LogicTransformer;
import org.drools.core.PathEndNode;
import org.drools.core.RuleBase;
import org.drools.core.TerminalNode;
import org.drools.core.time.TemporalDependencyMatrix;
import org.kie.api.conf.EventProcessingOption;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

public class ReteBuilder {
    private BuildUtils buildUtils;

    private RuleBase ruleBase;

    private IdGenerator nodeIdsGenerator = new IdGenerator(1);
    private IdGenerator memoryIdsGenerator = new IdGenerator(1);

    public ReteBuilder(RuleBase ruleBase) {
        this.ruleBase = ruleBase;
        this.buildUtils = new BuildUtils();

        this.buildUtils.addBuilder( GroupElement.class,    new GroupElementBuilder() );
        this.buildUtils.addBuilder( EntryPointId.class,   new EntryPointBuilder()  );
        this.buildUtils.addBuilder( Pattern.class,        new PatternBuilder()     );
    }

    public List<TerminalNode> addRule(RuleImpl rule) {
        return addRule(rule, java.util.Collections.emptyList());
    }

    public List<TerminalNode> addRule(RuleImpl rule, Collection<InternalWorkingMemory> workingMemories) {
        GroupElement group = rule.getBody();

        // the list of terminal nodes
        final List<TerminalNode> termNodes = new ArrayList<>();

        // transform rule and gets the array of subrules
        final GroupElement[] subrules = rule.getTransformedLhs(LogicTransformer.getInstance(), Collections.emptyMap());

        for (int i = 0; i < subrules.length; i++) {
            BuildContext ctx = new BuildContext(ruleBase);
            ctx.setRule(rule);
            ctx.setSubRuleIndex(i);

            // if running in STREAM mode, calculate temporal distance for events
            if (EventProcessingOption.STREAM.equals(ruleBase.getRuleBaseConfiguration().getEventProcessingMode())) {
                TemporalDependencyMatrix temporal = buildUtils.calculateTemporalDistance(subrules[i]);
                ctx.setTemporalDistance( temporal );
            }

            // adds subrule
            ctx.setSubRuleIndex(i);
            addSubRule( ctx, subrules[i], rule );
            // adds the terminal node to the list of terminal nodes

            termNodes.addAll(ctx.getTerminals());
        }

        return termNodes;

    }

    private void addSubRule(BuildContext ctx, GroupElement subrule, RuleImpl rule) throws InvalidPatternException {
        ctx.setSubRule(subrule);

        // gets the appropriate builder
        ReteooComponentBuilder builder = buildUtils.getBuilderFor(subrule);

        // checks if an initial-fact is needed
        if (builder.requiresLeftActivation( buildUtils,
                                            subrule )) {
            addInitialFactPattern( subrule );
        }

        // builds and attach
        builder.build( ctx,
                       buildUtils,
                       subrule );

        TerminalNode terminal;
        if (!ctx.isTerminated()) {
            terminal = buildTerminal(ctx, subrule, rule, buildUtils);
        } else {
            // from a non-conditional NamedConsequence. Conditionals do not generate subrules
            terminal = (TerminalNode) ctx.getLastNode();
        }

        attachTerminalNode(ctx, terminal);
    }

    private void attachTerminalNode(BuildContext ctx, TerminalNode terminal) {
        ctx.getTerminals().add(terminal);
        ctx.terminate();
        terminal.attach(ctx);
        setPathEndNodes(ctx, terminal);
    }

    private static void setPathEndNodes(BuildContext ctx, TerminalNode terminal) {
        PathEndNode[] pathEndNodes = ctx.getPathEndNodes().toArray(new PathEndNode[0]);
        for (PathEndNode endNode : pathEndNodes) {
            endNode.setPathEndNodes(pathEndNodes);
        }
        // visitLeftTupleNodes (addAssociatedTerminal) commented out until path nodes are built
    }

    private TerminalNode buildTerminal(BuildContext ctx, GroupElement subrule, RuleImpl rule, BuildUtils buildUtils) {
        TerminalNode terminal = new TerminalNode(ctx.getNextNodeId(), ctx.getLeftInput(), ctx, rule, subrule, ctx.getSubRuleIndex());
        ctx.getNodes().add(terminal);
        if (ctx.getLeftInput() != null) {
            ctx.getLeftInput().addOutput(terminal);
        }
        return terminal;
    }

    private void addInitialFactPattern(GroupElement subrule) {
        final Pattern pattern = new Pattern(0, ClassObjectType.InitialFact_ObjectType);
        subrule.addChild(0, pattern);
    }

    public IdGenerator getNodeIdsGenerator() {
        return nodeIdsGenerator;
    }

    public IdGenerator getMemoryIdsGenerator() {
        return memoryIdsGenerator;
    }

    public void releaseId(NetworkNode node) {
        memoryIdsGenerator.releaseId(node.getId());
    }
}
