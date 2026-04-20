package org.drools.core;

import org.drools.api.data.ObjectHandle;
import org.drools.core.function.Predicate4;

public class Join3<CTX, B, C, D> {
    private BaseNode leftInput;

    private BaseNode rightInput;

    private BaseNode sink;

    private Predicate4 predicate4;

    private void leftAdd(Context<CTX> ctx, ObjectHandle<B> b, ObjectHandle<C> c) {
        ObjectHandle<D> d = null;
        if (predicate4.test(ctx, b, c, d)) {

        }
    }
}
