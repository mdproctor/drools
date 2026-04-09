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

import org.drools.base.time.JobHandle;
import org.drools.core.time.Job;
import org.drools.core.time.JobContext;
import org.drools.core.time.TimerService;
import org.drools.core.time.impl.PointInTimeTrigger;
import org.kie.api.runtime.rule.FactHandle;

import java.util.Collection;
import java.util.PriorityQueue;

/**
 * A time-based window filter implementation.
 * Keeps facts in scope for a fixed duration; facts older than the window size are expired.
 * Timers fire via the container's async queue (vol2 threading model).
 */
public class SlidingTimeWindow implements WindowFilter {

    protected long size;
    // stateless job — one instance shared across all contexts
    private static final WindowFilterJob job = new WindowFilterJob();

    protected int nodeId;

    public SlidingTimeWindow() {
        this(0);
    }

    public SlidingTimeWindow(final long size) {
        this.size = size;
    }

    @Override
    public WindowFilterType getType() {
        return WindowFilterType.TIME_WINDOW;
    }

    public void setNodeId(int nodeId) {
        this.nodeId = nodeId;
    }

    public long getSize() {
        return size;
    }

    public void setSize(final long size) {
        this.size = size;
    }

    @Override
    public WindowFilterContext createContext() {
        return new SlidingTimeWindowContext();
    }

    @Override
    public boolean assertFact(final Object context,
                              final FactHandle fact,
                              final PropagationContext pctx,
                              final ReteEvaluator reteEvaluator) {
        final SlidingTimeWindowContext queue = (SlidingTimeWindowContext) context;
        final EventHandleImpl handle = (EventHandleImpl) fact;
        long currentTime = reteEvaluator.getTimerService().getCurrentTime();
        if (isExpired(currentTime, handle)) {
            return false;
        }
        queue.add(handle);
        if (handle.equals(queue.peek())) {
            updateNextExpiration(handle, reteEvaluator, queue, nodeId);
        }
        return true;
    }

    @Override
    public void retractFact(final Object context,
                            final FactHandle fact,
                            final PropagationContext pctx,
                            final ReteEvaluator reteEvaluator) {
        final SlidingTimeWindowContext queue = (SlidingTimeWindowContext) context;
        final EventHandleImpl handle = (EventHandleImpl) fact;
        final EventHandleImpl peekEvent = queue.peek();
        if (peekEvent != null) {
            if (handle.equals(peekEvent)) {
                queue.poll();
                updateNextExpiration(queue.peek(), reteEvaluator, queue, nodeId);
            } else if (handle.compareTo(peekEvent) >= 0) {
                queue.remove(handle);
            }
        }
        if (queue.isEmpty() && queue.getJobHandle() != null) {
            reteEvaluator.getTimerService().removeJob(queue.getJobHandle());
        }
    }

    @Override
    public void expireFacts(final Object context,
                            final PropagationContext pctx,
                            final ReteEvaluator reteEvaluator) {
        TimerService clock = reteEvaluator.getTimerService();
        long currentTime = clock.getCurrentTime();
        SlidingTimeWindowContext queue = (SlidingTimeWindowContext) context;

        EventHandleImpl handle = queue.peek();
        while (handle != null && isExpired(currentTime, handle)) {
            queue.remove();
            if (handle.isValid()) {
                // expire the fact — propagation infrastructure commented out until rebuilt in vol2
                // final PropagationContext expiresPctx = PhreakPropagationContextFactory
                //         .createPropagationContextForFact(reteEvaluator, handle, PropagationContext.Type.EXPIRATION);
                // ObjectTypeNode.doRetractObject(handle, expiresPctx, reteEvaluator);
            }
            handle = queue.peek();
        }
        updateNextExpiration(handle, reteEvaluator, queue, nodeId);
    }

    protected boolean isExpired(final long currentTime, final EventHandleImpl handle) {
        return handle.getStartTimestamp() + this.size <= currentTime;
    }

    protected void updateNextExpiration(final EventHandleImpl fact,
                                        final ReteEvaluator reteEvaluator,
                                        final WindowFilterContext context,
                                        final int nodeId) {
        TimerService clock = reteEvaluator.getTimerService();
        if (fact != null) {
            long nextTimestamp = fact.getStartTimestamp() + getSize();
            if (nextTimestamp < clock.getCurrentTime()) {
                // past/out-of-order event — schedule immediate expiry via container queue
                reteEvaluator.addPropagation(new WindowFilterExpireAction(nodeId, this, context));
            } else {
                if (context.getJobHandle() != null) {
                    reteEvaluator.getTimerService().removeJob(context.getJobHandle());
                }
                JobContext jobctx = new WindowFilterJobContext(nodeId, reteEvaluator, this, context);
                JobHandle handle = clock.scheduleJob(job,
                                                     jobctx,
                                                     PointInTimeTrigger.createPointInTimeTrigger(nextTimestamp, null));
                jobctx.setJobHandle(handle);
            }
        }
    }

    @Override
    public long getExpirationOffset() {
        return this.size;
    }

    @Override
    public String toString() {
        return "SlidingTimeWindow( size=" + size + " )";
    }

    /**
     * Per-instance context (memory) for a time window.
     */
    public static class SlidingTimeWindowContext implements WindowFilterContext {

        private final PriorityQueue<EventHandleImpl> queue;
        private JobHandle jobHandle;

        public SlidingTimeWindowContext() {
            this.queue = new PriorityQueue<>(16);
        }

        @Override
        public JobHandle getJobHandle() {
            return this.jobHandle;
        }

        @Override
        public void setJobHandle(JobHandle jobHandle) {
            this.jobHandle = jobHandle;
        }

        public void add(EventHandleImpl handle) { queue.add(handle); }
        public void remove(EventHandleImpl handle) { queue.remove(handle); }
        public boolean isEmpty() { return queue.isEmpty(); }
        public EventHandleImpl peek() { return queue.peek(); }
        public EventHandleImpl poll() { return queue.poll(); }
        public EventHandleImpl remove() { return queue.remove(); }

        @Override
        public Collection<EventHandleImpl> getFactHandles() {
            return queue;
        }
    }

    /**
     * Job context for scheduling window expiry via the timer service.
     * Timer fires → puts WindowFilterExpireAction onto the container's async queue.
     */
    public static class WindowFilterJobContext implements JobContext {
        public ReteEvaluator    reteEvaluator;
        public int              nodeId;
        public WindowFilter     filter;
        public WindowFilterContext filterContext;

        public WindowFilterJobContext(int nodeId,
                                      ReteEvaluator reteEvaluator,
                                      WindowFilter filter,
                                      WindowFilterContext filterContext) {
            this.nodeId = nodeId;
            this.reteEvaluator = reteEvaluator;
            this.filter = filter;
            this.filterContext = filterContext;
        }

        @Override
        public JobHandle getJobHandle() {
            return filterContext.getJobHandle();
        }

        @Override
        public void setJobHandle(JobHandle jobHandle) {
            filterContext.setJobHandle(jobHandle);
        }

        @Override
        public ReteEvaluator getReteEvaluator() {
            return reteEvaluator;
        }
    }

    /**
     * Stateless job — triggered by timer, enqueues expiry action onto container queue.
     */
    public static class WindowFilterJob implements Job {
        @Override
        public void execute(JobContext ctx) {
            WindowFilterJobContext context = (WindowFilterJobContext) ctx;
            context.reteEvaluator.addPropagation(
                    new WindowFilterExpireAction(context.nodeId, context.filter, context.filterContext));
        }
    }

    /**
     * Propagation action that triggers fact expiry for a window filter.
     * Commented-out parts depend on vol2 propagation infrastructure not yet built.
     *
     * TODO: extend vol2 propagation base class once available (replaces
     *       PropagationEntry.AbstractPropagationEntry + WorkingMemoryAction from vol1)
     */
    public static class WindowFilterExpireAction implements Runnable {
        protected WindowFilter filter;
        protected WindowFilterContext context;
        protected int nodeId;

        protected WindowFilterExpireAction() { }

        public WindowFilterExpireAction(final int nodeId,
                                        WindowFilter filter,
                                        WindowFilterContext context) {
            this.nodeId = nodeId;
            this.filter = filter;
            this.context = context;
        }

        public void run() { }
        public void internalExecute(ReteEvaluator reteEvaluator) {
            this.filter.expireFacts(context, null, reteEvaluator);
        }
    }
}
