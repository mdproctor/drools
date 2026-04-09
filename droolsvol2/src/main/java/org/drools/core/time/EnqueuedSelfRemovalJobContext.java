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
package org.drools.core.time;

import org.drools.core.ReteEvaluator;
import org.drools.core.time.impl.TimerJobInstance;

import java.util.Map;

public class EnqueuedSelfRemovalJobContext extends SelfRemovalJobContext {
    public EnqueuedSelfRemovalJobContext( JobContext jobContext, Map<Long, TimerJobInstance> timerInstances ) {
        super( jobContext, timerInstances );
    }

    @Override
    public void remove() {
        // TODO: replace with vol2 propagation action once infrastructure is built
        // PropagationEntry.AbstractPropagationEntry (drools-core phreak) not available in vol2.
        // Timer fires → must enqueue onto container's async queue, then execute:
        //   timerInstances.remove( jobContext.getJobHandle().getId() );
        final long id = jobContext.getJobHandle().getId();
        getReteEvaluator().addPropagation( () -> timerInstances.remove(id) );
    }
}
