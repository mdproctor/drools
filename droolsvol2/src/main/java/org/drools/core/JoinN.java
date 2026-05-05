package org.drools.core;

import org.drools.core.function.BiLinearTuplePredicateCache;
import org.drools.core.function.LinearTuplePredicateCache;
import org.drools.core.function.Predicate5;
import org.drools.core.function.Predicate6;
import org.drools.core.function.Predicate7;
import org.drools.core.function.Predicate8;
import org.drools.core.rete.NetworkNode;
import org.drools.core.util.AbstractDoubleLinkedNode;
import org.drools.core.util.FastIterator;

public class JoinN<CTX, T>  {
    private BaseNode leftInput;

    private BaseNode rightInput;

    private BaseNode sink;

    private Predicate8<Context<CTX>, Object, Object, Object, Object, Object, Object, Object> predicate8;
    private Predicate7<Context<CTX>, Object, Object, Object, Object, Object, Object> predicate7;
    private Predicate6<Context<CTX>, Object, Object, Object, Object, Object> predicate6;
    private Predicate5<Context<CTX>, Object, Object, Object, Object> predicate5;

    private int rightSize;


    private BiLinearTuplePredicateCache cache;

    public void test1() {
        Join4Memory j = new Join4Memory();

    }

    private static class Join4Memory extends AbstractDoubleLinkedNode<Memory> implements Memory {
        TupleMemory leftMemory;
        TupleMemory rightMemory;

        public TupleMemory leftMemory() {
            return leftMemory;
        }

        public TupleMemory rightMemory() {
            return rightMemory;
        }

        @Override
        public int getNodeType() {
            return 0;
        }

        @Override
        public SegmentMemory getSegmentMemory() {
            return null;
        }

        @Override
        public void setSegmentMemory(SegmentMemory segmentMemory) {

        }

        @Override
        public void reset() {

        }
    }


    private void leftAdd(Context<CTX> ctx, TupleImpl<T> lt) {
        Join4Memory             memory      = ctx.getMemory(this);
        TupleMemory             rightMemory = memory.rightMemory();
        TupleImpl               rt          = rightMemory.getFirstN(lt);
        FastIterator<TupleImpl> it          = rightMemory.fastIterator();

        cache.setLeft(lt);

        while ((rt = it.next(rt)) != null) {
            if (cache.applyRight(ctx, rt)) {

            }
        }
    }

//        switch (rightSize) {
//            case 1:
//                while ((rightTp = it.next(rightTp)) != null) {
//                    //if (predicate6.test(ctx, b, c, d, e, rightTp)) {
//                    if (predicate6.test(ctx,
//                                        b.get(), c.get(), d.get(), e.get(),
//                                        rightTp.get())) {
//
//                    }
//                }
//                break;
//            case 2:
//                while ((rightTp = it.next(rightTp)) != null) {
//                    if (predicate7.test(ctx,
//                                        b.get(), c.get(), d.get(), e.get(),
//                                        rightTp.get(), rightTp.getLeftParent().get())) {
//
//                    }
//                }
//            case 3:
//        }
////        if (predicate5.test(ds, b, c, d, e)) {
////            //sink.leftAdd(ds, b, c, d, e);
////        }
//    }


//    private void join(Context<CTX> ctx, DataHandle<B> b, DataHandle<C> c, DataHandle<D> d, DataHandle<E> e) {
//        int joins = 0;
//        switch(joins) {
//            case 1:
//            case 2:
//            case 3:
//            case 4:
//            case 5:
//        }
//    }
}
