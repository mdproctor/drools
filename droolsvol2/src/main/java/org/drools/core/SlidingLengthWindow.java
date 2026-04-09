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

import java.io.Externalizable;
import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Collection;
import java.util.Collections;

/**
 * A length-based window filter implementation.
 * Keeps the last N facts in scope; older facts are expired when the window is full.
 */
public class SlidingLengthWindow implements WindowFilter {

    protected int size;

    public SlidingLengthWindow() {
        this(0);
    }

    public SlidingLengthWindow(final int size) {
        this.size = size;
    }

    @Override
    public WindowFilterType getType() {
        return WindowFilterType.LENGTH_WINDOW;
    }

    public long getSize() {
        return size;
    }

    public void setSize(final int size) {
        this.size = size;
    }

    @Override
    public WindowFilterContext createContext() {
        return new SlidingLengthWindowContext(this.size);
    }

    @Override
    public boolean assertFact(final Object context,
                              final FactHandle handle,
                              final PropagationContext pctx,
                              final ReteEvaluator reteEvaluator) {
        SlidingLengthWindowContext window = (SlidingLengthWindowContext) context;
        window.pos = (window.pos + 1) % window.handles.length;
        if (window.handles[window.pos] != null) {
            final EventHandleImpl previous = window.handles[window.pos];
            // retract previous fact that fell out of the window
            // PhreakPropagationContextFactory and ObjectTypeNode.doRetractObject commented out
            // until vol2 propagation infrastructure is built
            // final PropagationContext expiresPctx = PhreakPropagationContextFactory
            //         .createPropagationContextForFact(reteEvaluator, previous, PropagationContext.Type.EXPIRATION);
            // ObjectTypeNode.doRetractObject(previous, expiresPctx, reteEvaluator);
        }
        window.handles[window.pos] = (EventHandleImpl) handle;
        return true;
    }

    @Override
    public void retractFact(final Object context,
                            final FactHandle handle,
                            final PropagationContext pctx,
                            final ReteEvaluator reteEvaluator) {
        SlidingLengthWindowContext window = (SlidingLengthWindowContext) context;
        final int last = (window.pos == 0) ? window.handles.length - 1 : window.pos - 1;
        for (int i = window.pos; i != last; i = (i + 1) % window.handles.length) {
            if (window.handles[i] == handle) {
                window.handles[i] = null;
                break;
            }
        }
    }

    @Override
    public void expireFacts(final Object context,
                            final PropagationContext pctx,
                            final ReteEvaluator reteEvaluator) {
        // length windows expire facts via assertFact — nothing to do here
    }

    @Override
    public long getExpirationOffset() {
        return -1; // length windows have no time-based expiration
    }

    @Override
    public String toString() {
        return "SlidingLengthWindow( size=" + size + " )";
    }

    /**
     * Per-instance context (memory) for a length window.
     */
    public static class SlidingLengthWindowContext implements WindowFilterContext, Externalizable {

        public EventHandleImpl[] handles;
        public int pos = 0;

        public SlidingLengthWindowContext(final int size) {
            this.handles = new EventHandleImpl[size];
        }

        /** For deserialization only. */
        public SlidingLengthWindowContext() { }

        @Override
        public Collection<EventHandleImpl> getFactHandles() {
            return Collections.emptyList();
        }

        @Override
        public void writeExternal(ObjectOutput out) throws IOException {
            out.writeInt(pos);
            out.writeObject(handles);
        }

        @Override
        public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
            pos = in.readInt();
            handles = (EventHandleImpl[]) in.readObject();
        }
    }
}
