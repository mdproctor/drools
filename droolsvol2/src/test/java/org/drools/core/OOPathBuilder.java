package org.drools.core;

import org.drools.core.PathNode.RootPathNode;
import org.drools.core.RuleOOPathBuilder.OOPathFinisher;
import org.drools.core.RuleOOPathBuilder.Path2;
import org.drools.core.RuleOOPathBuilder.Path3;
import org.drools.core.RuleOOPathBuilder.Path4;
import org.drools.core.RuleOOPathBuilder.Path5;
import org.drools.core.function.Function1;
import org.drools.core.function.Predicate1;

import org.drools.core.function.BaseTuple;
import org.drools.core.function.BaseTuple.Tuple2;
import org.drools.core.function.BaseTuple.Tuple3;
import org.drools.core.function.BaseTuple.Tuple4;
import org.drools.core.function.BaseTuple.Tuple5;

public class OOPathBuilder<END, R, L, T extends BaseTuple> {

    protected END end;

    protected OOPathFinisher<R, L, T> finisher;

    public OOPathBuilder(END end, OOPathFinisher<R, L, T> finisher) {
        this.end = end;
        this.finisher = finisher;
    }

    public static class BuilderEnd<R, L, T extends BaseTuple> {

        private OOPathFinisher<R, L, T> finisher;

        public BuilderEnd(OOPathFinisher<R, L, T> finisher) {
            this.finisher = finisher;
        }

        public OOPath<R, L, T> build() {
            return finisher.finish();
        }
    }

    <A, B, C, D, E> Path4<BuilderEnd<A, E, Tuple5<A, B, C, D, E>>,
                          Tuple5<A, B, C, D, E>, B, C, D, E> path5(Function1<A, ?> fn,
                                                                    Predicate1<B> flt) {
        RootPathNode<A, Tuple5<A, B, C, D, E>> root = new RootPathNode<>((ctx, l) -> true);

        Path5<BuilderEnd<A, E, Tuple5<A, B, C, D, E>>, Tuple5<A, B, C, D, E>, A, B, C, D, E> path5 = new Path5<>((BuilderEnd<A, E, Tuple5<A, B, C, D, E>>)end,
                                                                                                                 (OOPathFinisher<A, E, Tuple5<A, B, C, D, E>>) finisher,
                                                                                                                 root);
        return path5.path((Function1<A, Iterable<B>>) a -> (Iterable<B>) fn.apply(a), flt);
    }

    <A, B, C, D> Path3<BuilderEnd<A, D, Tuple4<A, B, C, D>>, Tuple4<A, B, C, D>, B, C, D> path4(Function1<A, ?> fn,
                                                                                                   Predicate1<B> flt) {
        RootPathNode<A, Tuple4<A, B, C, D>> root = new RootPathNode<>((ctx, l) -> true);

        Path4<BuilderEnd<A, D, Tuple4<A, B, C, D>>, Tuple4<A, B, C, D>, A, B, C, D> path4 = new Path4<>((BuilderEnd<A, D, Tuple4<A, B, C, D>>)end,
                                                                                                        (OOPathFinisher<A, D, Tuple4<A, B, C, D>>) finisher, root);
        return path4.path((Function1<A, Iterable<B>>) a -> (Iterable<B>) fn.apply(a), flt);
    }

    <A, B, C> Path2<BuilderEnd, Tuple3<A, B, C>, B, C> path3(Function1<A, ?> fn,
                                                               Predicate1<B> flt) {
        RootPathNode<A, Tuple3<A, B, C>> root = new RootPathNode<>((ctx, l) -> true);

        Path3<BuilderEnd, Tuple3<A, B, C>, A, B, C> path3 = new Path3<>((BuilderEnd<A, C, Tuple3<A, B, C>>)end,
                                                                        (OOPathFinisher<A, C, Tuple3<A, B, C>>)finisher, root);
        return path3.path((Function1<A, Iterable<B>>) a -> (Iterable<B>) fn.apply(a), flt);
    }

    <A, B> BuilderEnd path2(Function1<A, ?> fn, Predicate1<B> flt) {
        RootPathNode<A, Tuple2<A, B>> root = new RootPathNode<>((ctx, l) -> true);

        Path2<BuilderEnd, Tuple2<A, B>, A, B> path2 = new Path2<>((BuilderEnd<A, B, Tuple2<A, B>>)end,
                                                                  (OOPathFinisher<A, B, Tuple2<A, B>>)finisher, root);
        return path2.path((Function1<A, Iterable<B>>) a -> (Iterable<B>) fn.apply(a), flt);
    }
}
