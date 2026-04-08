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

import org.drools.base.rule.RuleComponent;
import org.kie.api.runtime.rule.FactHandle;

/**
 * An interface for all window filter implementations (e.g. sliding time window, sliding length window).
 * Replaces vol1 BehaviorRuntime.
 */
public interface WindowFilter extends RuleComponent, Cloneable {

    /**
     * Returns the type of the window filter
     */
    WindowFilterType getType();

    /**
     * Creates the context object associated with this filter.
     * The context is passed in all filter callbacks and holds per-instance state.
     */
    WindowFilterContext createContext();

    /**
     * Notifies the filter that a new fact is entering its scope.
     *
     * @return true if propagation should continue, false if the filter vetoes it
     */
    boolean assertFact(Object context,
                       FactHandle fact,
                       PropagationContext pctx,
                       ReteEvaluator reteEvaluator);

    /**
     * Removes a fact from the filter's scope.
     */
    void retractFact(Object context,
                     FactHandle fact,
                     PropagationContext pctx,
                     ReteEvaluator reteEvaluator);

    /**
     * Expires facts that have left the window.
     */
    void expireFacts(Object context,
                     PropagationContext pctx,
                     ReteEvaluator reteEvaluator);

    /**
     * Returns the expiration offset for time-based filters, or -1 if not applicable.
     */
    long getExpirationOffset();
}
