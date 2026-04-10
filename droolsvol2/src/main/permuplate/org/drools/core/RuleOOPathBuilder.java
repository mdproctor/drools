package org.drools.core;

import io.quarkiverse.permuplate.Permute;
import io.quarkiverse.permuplate.PermuteDeclr;
import io.quarkiverse.permuplate.PermuteReturn;
import io.quarkiverse.permuplate.PermuteTypeParam;

import org.drools.core.PathNode.ListPathNode;
import org.drools.core.function.Function2;
import org.drools.core.function.Predicate2;
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

        public END path(Function2<PathContext<T>, A, ?> fn2,
                        Predicate2<PathContext<T>, B> flt2) {

            path2 = new ListPathNode<>(AccessType.LIST, fn2, flt2, parentPath);

            finisher.setLeaf(path2);

            return end;
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

        @PermuteReturn(className = "Path${i-1}",
                       typeArgs = "'END, T, ' + typeArgList(2, i, 'alpha')",
                       when = "true")
        public Path2<END, T, B, C> path(Function2<PathContext<T>, A, ?> fn2,
                                        Predicate2<PathContext<T>, B> flt2) {
            this.fn2 = fn2;
            this.flt2 = flt2;

            path3 = new ListPathNode<>(AccessType.LIST, fn2, flt2, parentPath);

            return new @PermuteDeclr(type = "Path${i-1}") Path2<>(end, finisher, path3);
        }
    }
}
