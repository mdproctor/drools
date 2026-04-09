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

import org.drools.core.util.LinkedList;

/**
 * Caches the first Object's hashCode on instantiation — this can never change.
 * Internally references all handles that are equal, and tracks whether facts
 * are STATED or JUSTIFIED (TMS will be redesigned as a specialised DataSource in vol2).
 */
// ObjectHandleImpl<T> extends TupleImpl<T> which implements DoubleLinkedNode<TupleImpl<T>>,
// so LinkedList must be parameterised with TupleImpl<T>, not ObjectHandleImpl<T>.
public abstract class EqualityKey<T> extends LinkedList<TupleImpl<T>> {

    public static final int STATED    = 1;
    public static final int JUSTIFIED = 2;

    private int hashCode;
    private int status;

    public EqualityKey() { }

    public EqualityKey(final ObjectHandleImpl<T> handle) {
        super(handle);
        this.hashCode = handle.hashCode(); // ObjectHandleImpl.hashCode() returns object's hashCode
    }

    public EqualityKey(final ObjectHandleImpl<T> handle, final int status) {
        super(handle);
        this.hashCode = handle.hashCode();
        this.status = status;
    }

    public abstract ObjectHandleImpl<T> getLogicalFactHandle();

    public abstract void setLogicalFactHandle(ObjectHandleImpl<T> logicalFactHandle);

    @SuppressWarnings("unchecked")
    public ObjectHandleImpl<T> getFactHandle() {
        return (ObjectHandleImpl<T>) getFirst();
    }

    public void addFactHandle(final ObjectHandleImpl<T> handle) {
        add(handle);
    }

    public void removeFactHandle(final ObjectHandleImpl<T> handle) {
        remove(handle);
    }

    public int getStatus() {
        return this.status;
    }

    public void setStatus(final int status) {
        this.status = status;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean equals(final Object object) {
        if (object == null) {
            return false;
        }
        if (object instanceof EqualityKey) {
            return this == object;
        }
        return this.getFirst().getObject().equals(object);
    }

    @Override
    public String toString() {
        return switch (this.status) {
            case STATED    -> "[FactStatus status=STATED]";
            case JUSTIFIED -> "[FactStatus status=JUSTIFIED]";
            default        -> "[FactStatus status=UNKNOWN]";
        };
    }
}
