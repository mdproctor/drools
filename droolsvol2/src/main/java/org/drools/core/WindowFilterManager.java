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

import org.kie.api.runtime.rule.FactHandle;

import java.util.List;

/**
 * Manages window filters for a given beta node.
 * Replaces vol1 BehaviorManager.
 */
public class WindowFilterManager {

    public static final WindowFilter[] NO_FILTERS = new WindowFilter[0];

    private WindowFilter[] filters;

    public WindowFilterManager() {
        this(NO_FILTERS);
    }

    public WindowFilterManager(List<WindowFilter> filters) {
        this.filters = filters.toArray(new WindowFilter[filters.size()]);
    }

    public WindowFilterManager(WindowFilter[] filters) {
        this.filters = filters;
    }

    /**
     * Creates the context for each filter.
     */
    public WindowFilterContext[] createFilterContext() {
        WindowFilterContext[] ctx = new WindowFilterContext[filters.length];
        for (int i = 0; i < filters.length; i++) {
            ctx[i] = filters[i].createContext();
        }
        return ctx;
    }

    /**
     * Notifies all filters that a fact is entering scope.
     * Returns false if any filter vetoes the propagation.
     */
    public boolean assertFact(final Object filterContext,
                              final InternalDataHandle factHandle,
                              final PropagationContext pctx,
                              final ReteEvaluator reteEvaluator) {
        boolean result = true;
        for (int i = 0; i < filters.length; i++) {
            result = result && filters[i].assertFact(((Object[]) filterContext)[i],
                                                     factHandle,
                                                     pctx,
                                                     reteEvaluator);
        }
        return result;
    }

    /**
     * Notifies all filters that a fact is leaving scope.
     */
    public void retractFact(final Object filterContext,
                            final FactHandle factHandle,
                            final PropagationContext pctx,
                            final ReteEvaluator reteEvaluator) {
        for (int i = 0; i < filters.length; i++) {
            filters[i].retractFact(((Object[]) filterContext)[i],
                                   factHandle,
                                   pctx,
                                   reteEvaluator);
        }
    }

    public WindowFilter[] getFilters() {
        return filters;
    }
}
