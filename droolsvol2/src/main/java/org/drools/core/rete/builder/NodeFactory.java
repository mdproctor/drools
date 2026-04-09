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
import org.drools.base.definitions.rule.impl.RuleImpl;
import org.drools.base.rule.Accumulate;
import org.drools.base.rule.AsyncReceive;
import org.drools.base.rule.AsyncSend;
import org.drools.base.rule.Declaration;
import org.drools.base.rule.EvalCondition;
import org.drools.base.rule.From;
import org.drools.base.rule.GroupElement;
import org.drools.base.rule.QueryElement;
import org.drools.base.rule.accessor.DataProvider;
import org.drools.base.rule.constraint.AlphaNodeFieldConstraint;
import org.drools.base.time.impl.Timer;
import org.drools.core.AccumulateNode;
import org.drools.core.AlphaNode;
import org.drools.core.AsyncReceiveNode;
import org.drools.core.AsyncSendNode;
import org.drools.core.BaseNode;
import org.drools.core.BetaConstraints;
import org.drools.core.ConditionalBranchEvaluator;
import org.drools.core.ConditionalBranchNode;
import org.drools.core.EntryPointNode;
import org.drools.core.EvalConditionNode;
import org.drools.core.ExistsNode;
import org.drools.core.FromNode;
import org.drools.core.JoinNode;
import org.drools.core.LeftInputAdapterNode;
import org.drools.core.NotNode;
import org.drools.core.ObjectTypeNode;
import org.drools.core.QueryElementNode;
import org.drools.core.ReactiveFromNode;
import org.drools.core.TerminalNode;
import org.drools.core.TimerNode;
import org.drools.core.WindowFilter;
import org.drools.core.WindowNode;

import java.util.List;

public interface NodeFactory {

    AlphaNode buildAlphaNode(int id,
                             AlphaNodeFieldConstraint constraint,
                             BaseNode objectSource,
                             BuildContext context);

    TerminalNode buildTerminalNode(int id,
                                   BaseNode leftInput,
                                   RuleImpl rule,
                                   GroupElement subrule,
                                   int subruleIndex,
                                   BuildContext context);

    ObjectTypeNode buildObjectTypeNode(int id,
                                       EntryPointNode objectSource,
                                       ObjectType objectType,
                                       BuildContext context);

    EvalConditionNode buildEvalNode(int id,
                                    BaseNode leftInput,
                                    EvalCondition eval,
                                    BuildContext context);

    JoinNode buildJoinNode(int id,
                           BaseNode leftInput,
                           BaseNode rightInput,
                           BetaConstraints binder,
                           BuildContext context);

    NotNode buildNotNode(int id,
                         BaseNode leftInput,
                         BaseNode rightInput,
                         BetaConstraints binder,
                         BuildContext context);

    ExistsNode buildExistsNode( int id,
                                BaseNode leftInput,
                                BaseNode rightInput,
                                BetaConstraints binder,
                                BuildContext context );

    AccumulateNode buildAccumulateNode(int id,
                                       BaseNode leftInput,
                                       BaseNode rightInput,
                                       AlphaNodeFieldConstraint[] resultConstraints,
                                       BetaConstraints sourceBinder,
                                       BetaConstraints resultBinder,
                                       Accumulate accumulate,
                                       BuildContext context);

    LeftInputAdapterNode buildLeftInputAdapterNode(int nextId,
                                                   BaseNode objectSource,
                                                   BuildContext context,
                                                   boolean terminal);

    TerminalNode buildQueryTerminalNode( int id,
                                         BaseNode source,
                                         RuleImpl rule,
                                         GroupElement subrule,
                                         int subruleIndex,
                                         BuildContext context );

    QueryElementNode buildQueryElementNode( int nextId,
                                            BaseNode tupleSource,
                                            QueryElement qe,
                                            boolean tupleMemoryEnabled,
                                            boolean openQuery,
                                            BuildContext context );

    FromNode buildFromNode( int id,
                            DataProvider dataProvider,
                            BaseNode leftInput,
                            AlphaNodeFieldConstraint[] alphaNodeFieldConstraints,
                            BetaConstraints betaConstraints,
                            boolean tupleMemoryEnabled,
                            BuildContext context,
                            From from );

    ReactiveFromNode buildReactiveFromNode( int id,
                                            DataProvider dataProvider,
                                            BaseNode leftInput,
                                            AlphaNodeFieldConstraint[] alphaNodeFieldConstraints,
                                            BetaConstraints betaConstraints,
                                            boolean tupleMemoryEnabled,
                                            BuildContext context,
                                            From from );

    TimerNode buildTimerNode( int id,
                              Timer timer,
                              final String[] calendarNames,
                              final Declaration[][]   declarations,
                              BaseNode leftInput,
                              BuildContext context );

    ConditionalBranchNode buildConditionalBranchNode(int id,
                                                     BaseNode tupleSource,
                                                     ConditionalBranchEvaluator branchEvaluator,
                                                     BuildContext context);

    WindowNode buildWindowNode(int id,
                               List<AlphaNodeFieldConstraint> constraints,
                               List<WindowFilter> behaviors,
                               BaseNode leftInput,
                               BuildContext context);

    AsyncSendNode buildAsyncSendNode( int id,
                                      DataProvider dataProvider,
                                      BaseNode leftInput,
                                      AlphaNodeFieldConstraint[] alphaNodeFieldConstraints,
                                      BetaConstraints betaConstraints,
                                      boolean tupleMemoryEnabled,
                                      BuildContext context,
                                      AsyncSend send );

    AsyncReceiveNode buildAsyncReceiveNode( int id,
                                            AsyncReceive receive,
                                            BaseNode leftInput,
                                            AlphaNodeFieldConstraint[] alphaNodeFieldConstraints,
                                            BetaConstraints betaConstraints,
                                            BuildContext context );

    /** TODO #6650: vol2 right input (bi-linear adapter) node not yet implemented. */
    default TupleToObjectNode buildRightInputNode(int id, BaseNode leftInput, BaseNode objectSource, BuildContext context) {
        return new TupleToObjectNode(id, leftInput != null ? leftInput.getPathIndex() + 1 : 0, 0);
    }
}
