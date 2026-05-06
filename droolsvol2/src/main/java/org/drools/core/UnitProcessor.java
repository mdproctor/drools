package org.drools.core;

import org.drools.api.data.ObjectHandle;

/**
 * Evaluation-layer counterpart to {@link org.drools.api.data.DataProcessor}.
 *
 * Nodes from the {@link Router} downwards implement this interface. They receive
 * a {@link UnitInstance} at propagation time and access per-unit runtime state
 * (beta memories, agenda, context) through it — no runtime state is held in fields.
 *
 * The alpha chain (DataStore → Filter1DataProcessor → ContextRouterAdapter) continues
 * to use {@link org.drools.api.data.DataProcessor} with {@link Context}. The Router
 * is the boundary where {@link UnitInstance} enters the propagation chain.
 */
public interface UnitProcessor<CTX, T> {
    void add(UnitInstance<CTX> unit, ObjectHandle<T> handle);
    void update(UnitInstance<CTX> unit, ObjectHandle<T> handle);
    void remove(UnitInstance<CTX> unit, ObjectHandle<T> handle);
}
