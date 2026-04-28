package org.drools.core.function;

import java.io.Serializable;

@FunctionalInterface
public interface CtxLastPredicate1<A, DS> extends Serializable {
    boolean test(A a, DS ds);
}
