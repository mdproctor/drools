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
package org.drools.core.rete.builder;

import org.drools.base.base.ObjectType;
import org.drools.base.rule.EntryPointId;
import org.drools.base.rule.Pattern;
import org.drools.base.rule.RuleElement;
import org.drools.base.rule.constraint.AlphaNodeFieldConstraint;
import org.drools.base.rule.constraint.BetaConstraint;
import org.drools.base.rule.constraint.Constraint;
import org.drools.core.CoreComponentFactory;
import org.drools.core.EntryPointNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Vol2 minimal PatternBuilder — handles simple patterns with alpha constraints.
 *
 * Not yet supported (throws UnsupportedOperationException with TODO #6648):
 *   - Pattern sources (From, Accumulate, etc.)
 *   - Behaviors / sliding windows
 *   - XPath constraints
 *   - Event expiration offsets
 */
public class PatternBuilder implements ReteooComponentBuilder {

    @Override
    public void build(BuildContext context, BuildUtils utils, RuleElement rce) {
        final Pattern pattern = (Pattern) rce;

        context.setLastBuiltPattern(pattern);
        context.pushRuleComponent(pattern);
        context.syncObjectTypesWithObjectCount();

        attachPattern(context, utils, pattern);

        context.addPattern(pattern);
        context.popRuleComponent();
    }

    private void attachPattern(BuildContext context, BuildUtils utils, Pattern pattern) {
        Constraints constraints = createConstraints(pattern);

        // Set pattern indices relative to current network depth
        int pathIndex = context.getLeftInput() == null ? 0 : context.getLeftInput().getPathIndex() + 1;
        int objectIndex = context.getLeftInput() != null ? context.getLeftInput().getObjectCount() : 0;
        pattern.setTupleIndex(pathIndex);
        pattern.setObjectIndex(objectIndex);

        context.setBetaconstraints(constraints.betaConstraints);

        if (pattern.getSource() != null) {
            throw new UnsupportedOperationException(
                    "vol2 TODO #6648: pattern source '" + pattern.getSource().getClass().getSimpleName() +
                    "' not yet implemented in PatternBuilder");
        }

        // Default entry point — let EntryPointBuilder set context.objectSource
        ReteooComponentBuilder epBuilder = utils.getBuilderFor(EntryPointId.DEFAULT);
        epBuilder.build(context, utils, EntryPointId.DEFAULT);

        if (!pattern.getBehaviors().isEmpty()) {
            throw new UnsupportedOperationException(
                    "vol2 TODO #6648: pattern behaviors (sliding windows) not yet implemented in PatternBuilder");
        }

        attachObjectTypeNode(context, utils, pattern.getObjectType());

        if (context.getObjectSource() != null) {
            attachAlphaNodes(context, utils, constraints.alphaConstraints);
        }

        // XPath constraints — not yet implemented
        if (!constraints.xpathConstraints.isEmpty()) {
            throw new UnsupportedOperationException(
                    "vol2 TODO #6648: xpath constraints not yet implemented in PatternBuilder");
        }
    }

    private void attachObjectTypeNode(BuildContext context, BuildUtils utils, ObjectType objectType) {
        EntryPointNode objectSource = (EntryPointNode) context.getObjectSource();
        context.setObjectSource(utils.attachNode(context,
                CoreComponentFactory.get().getNodeFactoryService()
                        .buildObjectTypeNode(context.getNextNodeId(), objectSource, objectType, context)));
    }

    private void attachAlphaNodes(BuildContext context, BuildUtils utils, List<AlphaNodeFieldConstraint> alphaConstraints) {
        for (AlphaNodeFieldConstraint constraint : alphaConstraints) {
            context.pushRuleComponent(constraint);
            context.setObjectSource(utils.attachNode(context,
                    CoreComponentFactory.get().getNodeFactoryService()
                            .buildAlphaNode(context.getNextNodeId(), constraint, context.getObjectSource(), context)));
            context.popRuleComponent();
        }
    }

    private Constraints createConstraints(Pattern pattern) {
        Constraints constraints = new Constraints();
        for (Constraint constraint : pattern.getConstraints()) {
            switch (constraint.getType()) {
                case ALPHA:
                    constraints.alphaConstraints.add((AlphaNodeFieldConstraint) constraint);
                    break;
                case BETA:
                    constraints.betaConstraints.add((BetaConstraint) constraint);
                    break;
                case XPATH:
                    constraints.xpathConstraints.add(constraint);
                    break;
                default:
                    throw new RuntimeException("Unknown constraint type: " + constraint.getType());
            }
        }
        return constraints;
    }

    @Override
    public boolean requiresLeftActivation(BuildUtils utils, RuleElement rce) {
        Pattern pattern = (Pattern) rce;
        return (pattern.getSource() != null && pattern.getSource().requiresLeftActivation())
               || !pattern.getBehaviors().isEmpty();
    }

    private static class Constraints {
        final List<AlphaNodeFieldConstraint> alphaConstraints = new ArrayList<>();
        final List<BetaConstraint>           betaConstraints  = new ArrayList<>();
        final List<Constraint>               xpathConstraints = new ArrayList<>();
    }
}
