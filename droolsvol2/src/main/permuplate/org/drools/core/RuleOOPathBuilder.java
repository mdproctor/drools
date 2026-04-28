package org.drools.core;

import io.quarkiverse.permuplate.Permute;
import io.quarkiverse.permuplate.PermuteBody;
import io.quarkiverse.permuplate.PermuteDeclr;
import io.quarkiverse.permuplate.PermuteReturn;
import io.quarkiverse.permuplate.PermuteTypeParam;

import org.drools.core.PathNode.ListPathNode;
import org.drools.core.function.Function1;
import org.drools.core.function.Function2;
import org.drools.core.function.Predicate1;
import org.drools.core.function.CtxLastPredicate1;
import org.drools.core.function.Predicate2;
import java.util.Arrays;
import org.drools.core.function.BaseTuple;

public class RuleOOPathBuilder {

    public static class BasePath<END, A, B, T extends BaseTuple> {
        protected Function2<PathContext<T>, A, ?> fn2;
        protected Predicate2<PathContext<T>, B> flt2;
        protected END end;
        protected OOPathFinisher<?, ?, T> finisher;

        public BasePath(END end,
                        OOPathFinisher<?, ?, T> finisher) {
            this.end = end;
            this.finisher = finisher;
        }

        public Function2<PathContext<T>, A, ?> function() {
            return fn2;
        }

        public Predicate2<PathContext<T>, B> filter() {
            return flt2;
        }
    }

    public static class OOPathFinisher<R, L, T extends BaseTuple> {
        private PathNode<?, ?, T> leaf;

        public PathNode<?, ?, T> getLeaf() {
            return leaf;
        }

        public void setLeaf(PathNode<?, ?, T> leaf) {
            this.leaf = leaf;
        }

        public OOPath<R, L, T> finish() {
            return (OOPath<R, L, T>) new OOPath<>(leaf);
        }
    }

    public static class Path2<END, T extends BaseTuple, A, B> extends BasePath<END, A, B, T> {
        PathNode<A, B, T> path2;

        PathNode<?, A, T> parentPath;

        public Path2(END end, OOPathFinisher<?, ?, T> finisher, PathNode<?, A, T> parentPath) {
            super(end, finisher);
            this.parentPath = parentPath;
        }

        @SuppressWarnings("unchecked")
        private END path(Function2<PathContext<T>, A, ?> fn2,
                         Predicate2<PathContext<T>, B> flt2) {
            path2 = new ListPathNode<>(AccessType.LIST, fn2, flt2, parentPath);
            finisher.setLeaf(path2);
            return end;
        }

        /** No-ctx traversal, no predicate. Method references supported: e.g. {@code Library::rooms}. */
        @SuppressWarnings("unchecked")
        public END path(Function1<A, Iterable<B>> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        /** No-ctx traversal with no-ctx predicate. Method references supported for traversal. */
        @SuppressWarnings("unchecked")
        public END path(Function1<A, Iterable<B>> fn, Predicate1<B> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b));
        }

        /** Ctx-at-end traversal, no predicate — accepts all children. */
        @SuppressWarnings("unchecked")
        public END path(Function2<A, PathContext<T>, Iterable<B>> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a, (PathContext<T>) ctx),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        /** Ctx-at-end traversal with ctx-at-end predicate. If traversal needs ctx, predicate must too. */
        @SuppressWarnings("unchecked")
        public END path(Function2<A, PathContext<T>, Iterable<B>> fn, CtxLastPredicate1<B, PathContext<T>> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a, (PathContext<T>) ctx),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b, (PathContext<T>) ctx));
        }

        @SuppressWarnings("unchecked")
        public END pathArray(Function1<A, B[]> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> Arrays.asList(fn.apply((A) a)),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        @SuppressWarnings("unchecked")
        public END pathArray(Function1<A, B[]> fn, Predicate1<B> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> Arrays.asList(fn.apply((A) a)),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b));
        }

        @SuppressWarnings("unchecked")
        public END pathArray(Function2<A, PathContext<T>, B[]> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> Arrays.asList(fn.apply((A) a, (PathContext<T>) ctx)),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        @SuppressWarnings("unchecked")
        public END pathArray(Function2<A, PathContext<T>, B[]> fn, CtxLastPredicate1<B, PathContext<T>> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> Arrays.asList(fn.apply((A) a, (PathContext<T>) ctx)),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b, (PathContext<T>) ctx));
        }

        @SuppressWarnings("unchecked")
        public END pathSingle(Function1<A, B> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a); return __v != null ? java.util.List.of(__v) : java.util.List.of(); },
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        @SuppressWarnings("unchecked")
        public END pathSingle(Function1<A, B> fn, Predicate1<B> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a); return __v != null ? java.util.List.of(__v) : java.util.List.of(); },
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b));
        }

        @SuppressWarnings("unchecked")
        public END pathSingle(Function2<A, PathContext<T>, B> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a, (PathContext<T>) ctx); return __v != null ? java.util.List.of(__v) : java.util.List.of(); },
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        @SuppressWarnings("unchecked")
        public END pathSingle(Function2<A, PathContext<T>, B> fn, CtxLastPredicate1<B, PathContext<T>> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a, (PathContext<T>) ctx); return __v != null ? java.util.List.of(__v) : java.util.List.of(); },
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b, (PathContext<T>) ctx));
        }
    }

    // Template — generates Path4..Path6
    @Permute(varName = "i", from = 4, to = 6, className = "Path${i}", inline = true, keepTemplate = true)
    public static class Path3<END, T extends BaseTuple, A, B,
            @PermuteTypeParam(varName = "j", from = "3", to = "${i}", name = "${alpha(j)}") C>
            extends BasePath<END, A, B, T> {

        @PermuteDeclr(type = "PathNode<A, B, T>", name = "path${i}")
        PathNode<A, B, T> path3;

        PathNode<?, A, T> parentPath;

        public Path3(END end, OOPathFinisher<?, ?, T> finisher, PathNode<?, A, T> parentPath) {
            super(end, finisher);
            this.parentPath = parentPath;
        }

        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}",
                       typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')",
                       when = "true")
        private Path2<END, T, B, C> path(Function2<PathContext<T>, A, ?> fn2,
                                         Predicate2<PathContext<T>, B> flt2) {
            this.fn2 = fn2;
            this.flt2 = flt2;
            path3 = new ListPathNode<>(AccessType.LIST, fn2, flt2, parentPath);
            return new @PermuteDeclr(type = "Path${i-1}") Path2<>(end, finisher, path3);
        }

        /** No-ctx traversal, no predicate. Method references supported: e.g. {@code Library::rooms}. */
        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}",
                       typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')",
                       when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a), (Predicate2<PathContext<T>, B>) (ctx, b) -> true); }")
        public Path2<END, T, B, C> path(Function1<A, Iterable<B>> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        /** No-ctx traversal with no-ctx predicate. Method references supported for traversal. */
        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}",
                       typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')",
                       when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a), (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b)); }")
        public Path2<END, T, B, C> path(Function1<A, Iterable<B>> fn, Predicate1<B> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b));
        }

        /** Ctx-at-end traversal, no predicate — accepts all children. */
        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}",
                       typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')",
                       when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a, (PathContext<T>) ctx), (Predicate2<PathContext<T>, B>) (ctx, b) -> true); }")
        public Path2<END, T, B, C> path(Function2<A, PathContext<T>, Iterable<B>> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a, (PathContext<T>) ctx),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        /** Ctx-at-end traversal with ctx-at-end predicate. If traversal needs ctx, predicate must too. */
        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}",
                       typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')",
                       when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a, (PathContext<T>) ctx), (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b, (PathContext<T>) ctx)); }")
        public Path2<END, T, B, C> path(Function2<A, PathContext<T>, Iterable<B>> fn, CtxLastPredicate1<B, PathContext<T>> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> (Iterable<B>) fn.apply((A) a, (PathContext<T>) ctx),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b, (PathContext<T>) ctx));
        }

        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}", typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')", when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> java.util.Arrays.asList(fn.apply((A) a)), (Predicate2<PathContext<T>, B>) (ctx, b) -> true); }")
        public Path2<END, T, B, C> pathArray(Function1<A, B[]> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> Arrays.asList(fn.apply((A) a)),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}", typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')", when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> java.util.Arrays.asList(fn.apply((A) a)), (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b)); }")
        public Path2<END, T, B, C> pathArray(Function1<A, B[]> fn, Predicate1<B> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> Arrays.asList(fn.apply((A) a)),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b));
        }

        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}", typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')", when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> java.util.Arrays.asList(fn.apply((A) a, (PathContext<T>) ctx)), (Predicate2<PathContext<T>, B>) (ctx, b) -> true); }")
        public Path2<END, T, B, C> pathArray(Function2<A, PathContext<T>, B[]> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> Arrays.asList(fn.apply((A) a, (PathContext<T>) ctx)),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}", typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')", when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> java.util.Arrays.asList(fn.apply((A) a, (PathContext<T>) ctx)), (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b, (PathContext<T>) ctx)); }")
        public Path2<END, T, B, C> pathArray(Function2<A, PathContext<T>, B[]> fn, CtxLastPredicate1<B, PathContext<T>> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> Arrays.asList(fn.apply((A) a, (PathContext<T>) ctx)),
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b, (PathContext<T>) ctx));
        }

        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}", typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')", when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a); return __v != null ? java.util.List.of(__v) : java.util.List.of(); }, (Predicate2<PathContext<T>, B>) (ctx, b) -> true); }")
        public Path2<END, T, B, C> pathSingle(Function1<A, B> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a); return __v != null ? java.util.List.of(__v) : java.util.List.of(); },
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}", typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')", when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a); return __v != null ? java.util.List.of(__v) : java.util.List.of(); }, (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b)); }")
        public Path2<END, T, B, C> pathSingle(Function1<A, B> fn, Predicate1<B> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a); return __v != null ? java.util.List.of(__v) : java.util.List.of(); },
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b));
        }

        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}", typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')", when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a, (PathContext<T>) ctx); return __v != null ? java.util.List.of(__v) : java.util.List.of(); }, (Predicate2<PathContext<T>, B>) (ctx, b) -> true); }")
        public Path2<END, T, B, C> pathSingle(Function2<A, PathContext<T>, B> fn) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a, (PathContext<T>) ctx); return __v != null ? java.util.List.of(__v) : java.util.List.of(); },
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> true);
        }

        @SuppressWarnings("unchecked")
        @PermuteReturn(className = "Path${i-1}", typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')", when = "true")
        @PermuteBody(body = "{ return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a, (PathContext<T>) ctx); return __v != null ? java.util.List.of(__v) : java.util.List.of(); }, (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b, (PathContext<T>) ctx)); }")
        public Path2<END, T, B, C> pathSingle(Function2<A, PathContext<T>, B> fn, CtxLastPredicate1<B, PathContext<T>> flt) {
            return path((Function2<PathContext<T>, A, Iterable<B>>) (ctx, a) -> { B __v = (B) fn.apply((A) a, (PathContext<T>) ctx); return __v != null ? java.util.List.of(__v) : java.util.List.of(); },
                        (Predicate2<PathContext<T>, B>) (ctx, b) -> flt.test((B) b, (PathContext<T>) ctx));
        }
    }
}
