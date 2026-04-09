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
import org.drools.base.rule.EvalCondition;
import org.drools.base.rule.From;
import org.drools.base.rule.GroupElement;
import org.drools.base.rule.QueryElement;
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
import org.drools.core.TupleToObjectNode;
import org.drools.core.WindowFilter;
import org.drools.core.WindowNode;

import java.util.List;

/**
 * Vol2 minimal NodeFactory — creates the node types needed for basic Rete construction.
 * Unimplemented methods throw UnsupportedOperationException with a TODO #6648 marker.
 */
public class DefaultNodeFactory implements NodeFactory {

    public static final DefaultNodeFactory INSTANCE = new DefaultNodeFactory();

    /** Not in NodeFactory interface — called directly by EntryPointBuilder. */
    public EntryPointNode buildEntryPointNode(int id, BaseNode objectSource, BuildContext context) {
        EntryPointNode epn = new EntryPointNode(id, 0, 0);
        epn.setLeftInput(objectSource);
        return epn;
    }

    @Override
    public ObjectTypeNode buildObjectTypeNode(int id, EntryPointNode objectSource, ObjectType objectType, BuildContext context) {
        ObjectTypeNode otn = new ObjectTypeNode(id, 0, 0);
        otn.setObjectType(objectType);
        otn.setLeftInput(objectSource);
        return otn;
    }

    @Override
    public AlphaNode buildAlphaNode(int id, AlphaNodeFieldConstraint constraint, BaseNode objectSource, BuildContext context) {
        AlphaNode alpha = new AlphaNode(id, objectSource.getPathIndex(), objectSource.getObjectIndex());
        alpha.setConstraint(constraint);
        alpha.setLeftInput(objectSource);
        return alpha;
    }

    @Override
    public LeftInputAdapterNode buildLeftInputAdapterNode(int id, BaseNode objectSource, BuildContext context, boolean terminal) {
        LeftInputAdapterNode lia = new LeftInputAdapterNode(id, objectSource.getPathIndex() + 1, 0);
        lia.setLeftInput(objectSource);
        return lia;
    }

    @Override
    public TerminalNode buildTerminalNode(int id, BaseNode leftInput, RuleImpl rule, GroupElement subrule, int subruleIndex, BuildContext context) {
        return new TerminalNode(id, leftInput, context, rule, subrule, subruleIndex);
    }

    // --- Not yet implemented in vol2 ---

    @Override
    public EvalConditionNode buildEvalNode(int id, BaseNode leftInput, EvalCondition eval, BuildContext context) {
        throw new UnsupportedOperationException("vol2 TODO #6648: EvalNode not yet implemented");
    }

    @Override
    public JoinNode buildJoinNode(int id, BaseNode leftInput, BaseNode rightInput, BetaConstraints binder, BuildContext context) {
        // leftInput:  LIA (tuple side — left sub-network end)
        // rightInput: OTN or alpha chain (object side — right sub-network entry, bi-linear adapter)
        int pathIndex   = leftInput.getPathIndex() + 1;
        int objectIndex = leftInput.getObjectCount() + 1; // one more object added by right side
        JoinNode node = new JoinNode(id, pathIndex, objectIndex);
        node.setLeftInput(leftInput);
        node.setRightInput(rightInput);
        return node;
    }

    @Override
    public NotNode buildNotNode(int id, BaseNode leftInput, BaseNode rightInput, BetaConstraints binder, BuildContext context) {
        throw new UnsupportedOperationException("vol2 TODO #6648: NotNode not yet implemented");
    }

    @Override
    public ExistsNode buildExistsNode(int id, BaseNode leftInput, BaseNode rightInput, BetaConstraints binder, BuildContext context) {
        throw new UnsupportedOperationException("vol2 TODO #6648: ExistsNode not yet implemented");
    }

    @Override
    public AccumulateNode buildAccumulateNode(int id, BaseNode leftInput, BaseNode rightInput, AlphaNodeFieldConstraint[] resultConstraints, BetaConstraints sourceBinder, BetaConstraints resultBinder, Accumulate accumulate, BuildContext context) {
        throw new UnsupportedOperationException("vol2 TODO #6648: AccumulateNode not yet implemented");
    }

    @Override
    public TerminalNode buildQueryTerminalNode(int id, BaseNode source, RuleImpl rule, GroupElement subrule, int subruleIndex, BuildContext context) {
        throw new UnsupportedOperationException("vol2 TODO #6648: QueryTerminalNode not yet implemented");
    }

    @Override
    public QueryElementNode buildQueryElementNode(int id, BaseNode tupleSource, QueryElement qe, boolean tupleMemoryEnabled, boolean openQuery, BuildContext context) {
        throw new UnsupportedOperationException("vol2 TODO #6648: QueryElementNode not yet implemented");
    }

    @Override
    public FromNode buildFromNode(int id, org.drools.base.rule.accessor.DataProvider dataProvider, BaseNode leftInput, AlphaNodeFieldConstraint[] alphaNodeFieldConstraints, BetaConstraints betaConstraints, boolean tupleMemoryEnabled, BuildContext context, From from) {
        throw new UnsupportedOperationException("vol2 TODO #6648: FromNode not yet implemented");
    }

    @Override
    public ReactiveFromNode buildReactiveFromNode(int id, org.drools.base.rule.accessor.DataProvider dataProvider, BaseNode leftInput, AlphaNodeFieldConstraint[] alphaNodeFieldConstraints, BetaConstraints betaConstraints, boolean tupleMemoryEnabled, BuildContext context, From from) {
        throw new UnsupportedOperationException("vol2 TODO #6648: ReactiveFromNode not yet implemented");
    }

    @Override
    public TimerNode buildTimerNode(int id, Timer timer, String[] calendarNames, org.drools.base.rule.Declaration[][] declarations, BaseNode leftInput, BuildContext context) {
        throw new UnsupportedOperationException("vol2 TODO #6648: TimerNode not yet implemented");
    }

    @Override
    public ConditionalBranchNode buildConditionalBranchNode(int id, BaseNode tupleSource, ConditionalBranchEvaluator branchEvaluator, BuildContext context) {
        throw new UnsupportedOperationException("vol2 TODO #6648: ConditionalBranchNode not yet implemented");
    }

    @Override
    public WindowNode buildWindowNode(int id, List<AlphaNodeFieldConstraint> constraints, List<WindowFilter> behaviors, BaseNode leftInput, BuildContext context) {
        throw new UnsupportedOperationException("vol2 TODO #6648: WindowNode not yet implemented");
    }

    @Override
    public AsyncSendNode buildAsyncSendNode(int id, org.drools.base.rule.accessor.DataProvider dataProvider, BaseNode leftInput, AlphaNodeFieldConstraint[] alphaNodeFieldConstraints, BetaConstraints betaConstraints, boolean tupleMemoryEnabled, BuildContext context, AsyncSend send) {
        throw new UnsupportedOperationException("vol2 TODO #6648: AsyncSendNode not yet implemented");
    }

    @Override
    public AsyncReceiveNode buildAsyncReceiveNode(int id, AsyncReceive receive, BaseNode leftInput, AlphaNodeFieldConstraint[] alphaNodeFieldConstraints, BetaConstraints betaConstraints, BuildContext context) {
        throw new UnsupportedOperationException("vol2 TODO #6648: AsyncReceiveNode not yet implemented");
    }
}
