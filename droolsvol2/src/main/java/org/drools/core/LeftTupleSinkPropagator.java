package org.drools.core;
/** TODO #6650: Temporary stub — vol2 uses arrays not linked-list propagators. */
public interface LeftTupleSinkPropagator {
    default int size() { return 0; }
    default BaseNode getFirstLeftTupleSink() { return null; }
}
