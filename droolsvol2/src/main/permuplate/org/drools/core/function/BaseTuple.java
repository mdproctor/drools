package org.drools.core.function;

import io.quarkiverse.permuplate.Permute;
import io.quarkiverse.permuplate.PermuteDeclr;
import io.quarkiverse.permuplate.PermuteExtends;
import io.quarkiverse.permuplate.PermuteParam;
import io.quarkiverse.permuplate.PermuteCase;
import io.quarkiverse.permuplate.PermuteStatements;
import io.quarkiverse.permuplate.PermuteTypeParam;
import io.quarkiverse.permuplate.PermuteValue;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public abstract class BaseTuple implements Tuple {
    protected int size;

    // Does not need to be concurrent, as the value is always the same for the key, it'll eventually be consistent.
    private static Map<String, Constructor<?>> constructors = new ConcurrentHashMap<>();

    public abstract <T> T get(int index);

    public abstract <T> void set(int index, T t);

    private <T> Constructor<T> getConstructor(Class<T> cls) {
        Constructor<?> con = constructors.computeIfAbsent(cls.getName(), (k) -> {
            Constructor<?>[] cons = cls.getDeclaredConstructors();
            for (Constructor<?> i : cons) {
                if (i.getParameterCount() == size) {
                    return i;
                }
            }
            throw new IllegalStateException("Unable to resolve constructor for class" + cls.getCanonicalName());
        });

        return (Constructor<T>) con;
    }

    public <T> T as(T... v) {
        Class cls = v.getClass().getComponentType();
        Constructor<T> con = getConstructor(cls);
        try {
            Object[] args = new Object[size];
            for (int k = 0; k < size; k++) {
                args[k] = get(k);
            }
            return con.newInstance(args);
        } catch (InvocationTargetException | InstantiationException | IllegalAccessException e) {
            throw new RuntimeException(e);
        }
    }

    public int size() {
        return size;
    }

    public static class Tuple0 extends BaseTuple {
        public static Tuple0 INSTANCE = new Tuple0();

        public Tuple0() {
            this.size = 0;
        }

        @Override
        public <T> T get(int index) {
            throw new UnsupportedOperationException();
        }

        @Override
        public <T> void set(int index, T t) {
            throw new UnsupportedOperationException();
        }
    }

    public static class Tuple1<A> extends BaseTuple {
        protected A a;

        public Tuple1() {
            super();
        }

        public Tuple1(A a) {
            this.a = a;
            this.size = 1;
        }

        public A getA() {
            return a;
        }

        public void setA(A a) {
            this.a = a;
        }

        @Override
        public <T> T get(int index) {
            switch (index) {
                case 0: {
                    return (T) a;
                }
                default:
                    throw new IndexOutOfBoundsException(index);
            }
        }

        public <T> void set(int index, T t) {
            switch (index) {
                case 0: {
                    this.a = (A) t;
                    break;
                }
                default:
                    throw new IndexOutOfBoundsException(index);
            }
        }
    }

    // Template — generates Tuple2..Tuple6 as nested static siblings inside BaseTuple.
    // The template class itself (Tuple1T) is removed from the output (keepTemplate = false).
    // Tuple1 (hand-written above) is kept unchanged and inherited by each generated TupleN.
    @Permute(varName = "i", from = "2", to = "6", className = "Tuple${i}", inline = true)
    @PermuteExtends(className = "Tuple${i-1}", typeArgVarName = "k", typeArgFrom = "1", typeArgTo = "${i-1}", typeArgName = "${alpha(k)}")
    public static class Tuple1T<A, @PermuteTypeParam(varName = "k", from = "2", to = "${i}", name = "${alpha(k)}") B>
            extends Tuple1<A> {

        // The new field for this arity: B b for Tuple2, C c for Tuple3, etc.
        // @PermuteDeclr renames A a → ${alpha(i)} ${lower(i)} and propagates all NameExpr
        // usages of the old name throughout the class body.
        @PermuteDeclr(type = "${alpha(i)}", name = "${lower(i)}")
        protected B b;

        public Tuple1T() {
            super();
        }

        // Constructor expands via three annotations (applied in pipeline order):
        //   1. @PermuteParam  (runs 4th): sentinel "A a" expands to (A a, B b, ...) for each arity
        //   2. @PermuteValue  (runs 7th): replaces this.size = 1 → this.size = ${i}
        //   3. @PermuteStatements (runs 8th): inserts this.a=a; this.b=b; ... before this.size
        @PermuteValue(index = 0, value = "${i}")
        @PermuteStatements(varName = "k", from = "1", to = "${i}", position = "first", body = "this.${lower(k)} = ${lower(k)};")
        public Tuple1T(@PermuteParam(varName = "k", from = "1", to = "${i}", type = "${alpha(k)}", name = "${lower(k)}") A a) {
            this.size = 1;
        }

        // @PermuteCase (runs 6th, after @PermuteDeclr): generates all switch cases k=1..i.
        // The body uses JEXL-evaluated string literals — NOT subject to @PermuteDeclr rename.
        // case (k-1): return (T) lower(k);  → case 0: return (T) a; etc.
        @PermuteCase(varName = "k", from = "1", to = "${i}", index = "${k-1}", body = "return (T) ${lower(k)};")
        @Override
        public <T> T get(int index) {
            switch (index) {
                default:
                    throw new IndexOutOfBoundsException(index);
            }
        }

        @PermuteCase(varName = "k", from = "1", to = "${i}", index = "${k-1}", body = "this.${lower(k)} = (${alpha(k)}) t; break;")
        @Override
        public <T> void set(int index, T t) {
            switch (index) {
                default:
                    throw new IndexOutOfBoundsException(index);
            }
        }
    }
}
