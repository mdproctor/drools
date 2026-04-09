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
import org.drools.core.time.TimerService;
import org.kie.api.runtime.rule.EventHandle;

import java.util.LinkedList;

/**
 * Vol2 event handle — extends ObjectHandleImpl with event timing fields.
 * TODO #6650: full vol2 event handle design TBD (CEP integration with DataSources)
 * Clone/copy methods stripped — ObjectHandleImpl vol2 doesn't have vol1 fields
 * (recency, identityHashCode, linkedTuples, wmEntryPoint, equalityKey, objectHashCode).
 */
public class EventHandleImpl<T> extends ObjectHandleImpl<T> implements EventHandle, Comparable<EventHandleImpl> {

    private static final long serialVersionUID = 510L;
    static final String EVENT_FORMAT_VERSION = "5";

    private long    startTimestamp;
    private long    duration;
    private boolean expired;
    private boolean pendingRemoveFromStore;
    private int     otnCount;

    private EventHandleImpl linkedFactHandle;

    private final transient LinkedList<JobHandle> jobs = new LinkedList<>();

    public EventHandleImpl() {
        super(0L, null, null);
        this.startTimestamp = 0;
        this.duration = 0;
    }

    public EventHandleImpl(long id, T object) {
        super(id, object, null);
        this.startTimestamp = 0;
        this.duration = 0;
    }

    public EventHandleImpl(long id, T object, long startTimestamp, long duration) {
        super(id, object, null);
        this.startTimestamp = startTimestamp;
        this.duration = duration;
    }

    protected String getFormatVersion() {
        return EVENT_FORMAT_VERSION;
    }

    @Override
    public String toString() {
        return toExternalForm();
    }

    @Override
    public boolean isEvent() {
        return true;
    }

    public long getStartTimestamp() {
        return startTimestamp;
    }

    public long getDuration() {
        return duration;
    }

    public long getEndTimestamp() {
        return this.startTimestamp + this.duration;
    }

    public EventHandleImpl getLinkedFactHandle() {
        return linkedFactHandle;
    }

    @Override
    public boolean isExpired() {
        if (linkedFactHandle != null) {
            return linkedFactHandle.isExpired();
        }
        return expired;
    }

    public void setExpired(boolean expired) {
        if (linkedFactHandle != null) {
            linkedFactHandle.setExpired(expired);
        } else {
            this.expired = expired;
        }
    }

    public boolean isPendingRemoveFromStore() {
        return pendingRemoveFromStore;
    }

    public void setPendingRemoveFromStore(boolean pendingRemove) {
        this.pendingRemoveFromStore = pendingRemove;
    }

    public void increaseOtnCount() { otnCount++; }
    public void decreaseOtnCount() { otnCount--; }
    public int getOtnCount() { return otnCount; }
    public void setOtnCount(int otnCount) { this.otnCount = otnCount; }

    @Override
    public int compareTo(EventHandleImpl e) {
        return (getStartTimestamp() < e.getStartTimestamp()) ? -1
                : (getStartTimestamp() == e.getStartTimestamp() ? 0 : 1);
    }

    public void addJob(JobHandle job) {
        synchronized (jobs) {
            jobs.add(job);
        }
    }

    public void removeJob(JobHandle job) {
        synchronized (jobs) {
            if (jobs.contains(job)) {
                jobs.remove(job);
            }
        }
    }

    public void unscheduleAllJobs(ReteEvaluator reteEvaluator) {
        if (!jobs.isEmpty()) {
            synchronized (jobs) {
                TimerService clock = reteEvaluator.getTimerService();
                while (!jobs.isEmpty()) {
                    JobHandle job = jobs.removeFirst();
                    clock.removeJob(job);
                }
            }
        }
    }
}
