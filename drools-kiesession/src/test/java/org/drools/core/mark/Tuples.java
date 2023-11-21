package org.drools.core.mark;

import org.drools.core.mark.Predicates.Predicate1;
import org.drools.core.mark.Predicates.Predicate2;
import org.drools.core.mark.Predicates.Predicate3;
import org.drools.core.mark.Predicates.Predicate4;

public class Tuples {
    public static <A> Tuple1<A> from(Predicate1<A> pred1, Class<A> a) {
        return null;
    }

    public class Tuple1<A> {
        public <B> Tuple2<A, B> filter(Predicate2<A, B> pred2, Class<B> b) {
            return null;
        }
    }

    public class Tuple2<A, B> {
        public <C> Tuple3<A, B, C> filter(Predicate3<A, B, C> pred3, Class<C> c) {
            return null;
        }
    }

    public class Tuple3<A, B, C> {
        public <D> Tuple4<A, B, C, D> filter(Predicate4<A, B, C, D> pred4,  Class<C> d) {
            return null;
        }
    }

    public class Tuple4<A, B, C, D> {}
}
