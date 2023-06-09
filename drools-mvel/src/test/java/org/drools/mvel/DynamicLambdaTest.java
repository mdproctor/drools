package org.drools.mvel;

import org.mvel2.MVEL;
import org.mvel2.ParserContext;
import org.mvel2.asm.ClassWriter;
import org.mvel2.asm.MethodVisitor;

import java.lang.invoke.MethodHandles;
import java.lang.reflect.Constructor;
import java.util.HashMap;
import java.util.Map;

import static org.mvel2.asm.Opcodes.ACC_PUBLIC;
import static org.mvel2.asm.Opcodes.ACC_SUPER;
import static org.mvel2.asm.Opcodes.ALOAD;
import static org.mvel2.asm.Opcodes.IADD;
import static org.mvel2.asm.Opcodes.ILOAD;
import static org.mvel2.asm.Opcodes.INVOKESPECIAL;
import static org.mvel2.asm.Opcodes.IRETURN;
import static org.mvel2.asm.Opcodes.RETURN;
import static org.mvel2.asm.Opcodes.V1_6;

public class DynamicLambdaTest {

    @org.junit.Test
    public void test() throws Throwable {
        final int MAX_TEST_RUNS = 100;
        final int MAX_COMPILE_RUNS = 10000;
        final int MAX_EXEC_RUNS = 10000;
        final TestRunnerFactory HIDDEN_FACTORY = new TestRunnerHiddenFactory();
        final TestRunnerFactory MVEL_FACTORY = new TestRunnerMVELFactory();

        Runtime runtime = Runtime.getRuntime();
        long usedMemoryBefore = runtime.totalMemory() - runtime.freeMemory();


        run(MAX_TEST_RUNS, MAX_COMPILE_RUNS, MAX_EXEC_RUNS, HIDDEN_FACTORY);
        run(MAX_TEST_RUNS, MAX_COMPILE_RUNS, MAX_EXEC_RUNS, MVEL_FACTORY);

        try {
            // Give an opportunity to GC
            System.gc();
            Thread.sleep(0);
            System.gc();
            Thread.sleep(5000);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }

        long usedMemoryAfter = runtime.totalMemory() - runtime.freeMemory();
        System.out.println("All Memory before:" + usedMemoryBefore);
        System.out.println("All Memory after:" + usedMemoryAfter );
        System.out.println("All Memory increased:" + (usedMemoryAfter-usedMemoryBefore));
    }

    public interface Test {
        int test(int i);
    }

    public interface TestRunner<T> {
        T compile(int x);

        void exec(T unit, int x, int maxRuns);

        String getType();
    }

    public interface TestRunnerFactory {
        TestRunner get();

        String getType();
    }

    public class TestRunnerHiddenFactory implements TestRunnerFactory {
        public TestRunner get() {
            return new HiddenTest();
        }

        @Override
        public String getType() {
            return "Hidden";
        }
    }

    public class TestRunnerMVELFactory implements TestRunnerFactory {
        public TestRunner get() {
            return new MVELTest();
        }

        @Override
        public String getType() {
            return "MVEL";
        }
    }



    private static void run(final int maxTestRuns,
                            final int maxCompileRuns,
                            final int maxExecRuns,
                            final TestRunnerFactory factory) {

        Runtime runtime = Runtime.getRuntime();
        long usedMemoryBefore = runtime.totalMemory() - runtime.freeMemory();

        compileAndExecuteSerially(maxTestRuns, maxCompileRuns, maxExecRuns, factory);

        long usedMemoryAfter = runtime.totalMemory() - runtime.freeMemory();
        System.out.println(factory.getType() + " Serial Memory before:" + usedMemoryBefore);
        System.out.println(factory.getType() + " Serial Memory after:" + usedMemoryAfter );
        System.out.println(factory.getType() + " Serial Memory increased:" + (usedMemoryAfter-usedMemoryBefore));

        try {
            // Give an opportunity to GC
            System.gc();
            Thread.sleep(0);
            System.gc();
            Thread.sleep(5000);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        //-------

        usedMemoryBefore = runtime.totalMemory() - runtime.freeMemory();

        compileAllExecAll(maxTestRuns, maxCompileRuns, maxExecRuns, factory);

        usedMemoryAfter = runtime.totalMemory() - runtime.freeMemory();
        System.out.println(factory.getType() + " All Memory before:" + usedMemoryBefore);
        System.out.println(factory.getType() + " All Memory after:" + usedMemoryAfter );
        System.out.println(factory.getType() + " All Memory increased:" + (usedMemoryAfter-usedMemoryBefore));

        try {
            // Give an opportunity to GC
            System.gc();
            Thread.sleep(0);
            Thread.sleep(5000);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    private static void compileAllExecAll(int maxTestRuns, int maxCompileRuns, int maxExecRuns, TestRunnerFactory factory) {
        System.out.println("Compile all and then execute all");
        TestRunner runner = factory.get();
        long start = System.currentTimeMillis();

        Object[] units = new Object[maxCompileRuns];
        for (int z = 0; z < maxTestRuns; z++) {
            for (int x = 0; x < maxCompileRuns; x++) {
                units[x] = runner.compile(x);
            }
        }

        for (int x = 0; x < maxCompileRuns; x++) {
            runner.exec(units[x], x, maxExecRuns);
        }
        long end = System.currentTimeMillis();

        System.out.println(runner);
        System.out.println(factory.getType() + ": " + (end - start));
    }

    private static void compileAndExecuteSerially(int maxTestRuns, int maxCompileRuns, int maxExecRuns, TestRunnerFactory factory) {
        TestRunner runner = factory.get();

        System.out.println("Compile and execute serially");
        long start = System.currentTimeMillis();

        for (int z = 0; z < maxTestRuns; z++) {
            for (int x = 0; x < maxCompileRuns; x++) {
                Object o = runner.compile(x);
                runner.exec(o, x, maxExecRuns);
            }
        }

        long end = System.currentTimeMillis();

        System.out.println(runner);
        System.out.println(factory.getType() + ": " + (end - start));
    }


    public static abstract class BaseTestRunner {
        private long compileTime;
        private long compileIterations;
        private long runtimeTime;

        private long runtimeIterations;

        private String type;

        public BaseTestRunner(String type) {
            this.type = type;
        }

        public void addToCompileTime(long time) {
            compileTime += time;
        }

        public void addToRuntimetTime(long time) {
            runtimeTime += time;
        }

        public void incCompileIteration() {
            compileIterations++;
        }

        public void incRuntimeIteration() {
            runtimeIterations++;
        }

        public long getCompileTimeAverage() {
            return compileTime / compileIterations;
        }

        public long getRuntimeTimeAverage() {
            return runtimeTime / runtimeIterations;
        }

        public long getCompileTime() {
            return compileTime;
        }

        public long getCompileIterations() {
            return compileIterations;
        }

        public long getRuntimeTime() {
            return runtimeTime;
        }

        public long getRuntimeIterations() {
            return runtimeIterations;
        }

        @Override
        public String toString() {
            return "BaseTestRunner{" +
                   "compileTimeAverage=" + getCompileTimeAverage() +
                   ", runtimeTimeAverage=" + getRuntimeTimeAverage() +
                   ", compileTime=" + compileTime +
                   ", compileIterations=" + compileIterations +
                   ", runtimeTime=" + runtimeTime +
                   ", runtimeIterations=" + runtimeIterations +
                   ", type='" + type + '\'' +
                   '}';
        }

        public String getType() {
            return type;
        }

    }

    public static class HiddenTest  extends BaseTestRunner  implements TestRunner<Test> {

        public HiddenTest() {
            super("Hidden");
        }

        @Override
        public Test compile(int x) {
            long start = System.currentTimeMillis();

            MethodHandles.Lookup lookup = MethodHandles.lookup();
            ClassWriter cw = GenerateClass.getClassWriter(HiddenTest.class, x);
            byte[] bytes = cw.toByteArray();

            Constructor<?> constructor = null;
            Test test = null;

            try {
                Class<?> c = lookup.defineHiddenClass(bytes, true).lookupClass();
                constructor = c.getConstructor(null);
                Object object = constructor.newInstance(null);
                test = (Test) object;
            } catch (Exception e) {
                throw new RuntimeException("Unbale to instantiate Lamda");
            }
            long end = System.currentTimeMillis();

            addToCompileTime(end-start);
            incCompileIteration();

            return test;
        }

        @Override
        public void exec(Test test, int x, int maxRuns) {
            long start = System.currentTimeMillis();

            for (int i = 0; i < maxRuns; i++) {
                int result = test.test(i);

                if (result != (x + i)) {
                    throw new RuntimeException("Invalid Hidden result=" + result + " x=" + x + " i=" + i);
                }
            }

            long end = System.currentTimeMillis();

            addToRuntimetTime(end-start);
            incRuntimeIteration();
        }
    }

    public static class MVELTest extends BaseTestRunner implements TestRunner<Object> {

        public MVELTest() {
            super("MVEL");
        }

        @Override
        public Object compile(int x) {
            long start = System.currentTimeMillis();

            ParserContext ctx = new ParserContext();
            ctx.addInput("i", int.class);
            ctx.setStrongTyping(true);
            ctx.setStrictTypeEnforcement(true);

            Object unit = MVEL.compileExpression("return " + x + " + i;");

            long end = System.currentTimeMillis();

            addToCompileTime(end-start);
            incCompileIteration();
            return unit;
        }

        @Override
        public void exec(Object unit, int x, int maxRuns) {
            long start = System.currentTimeMillis();

            for (int i = 0; i < maxRuns; i++) {
                Map<String, Object> vars = new HashMap<>();
                vars.put("i", i);
                int result = (int) MVEL.executeExpression(unit, vars);
                if (result != (x + i)) {
                    throw new RuntimeException("Invalid MVEL result=" + result + " x=" + x + " i=" + i);
                }
            }

            long end = System.currentTimeMillis();

            addToRuntimetTime(end-start);
            incRuntimeIteration();
        }
    }

    public static int test(int i) {
        return i + Integer.MAX_VALUE;
    }

    public static class GenerateClass {

        private static String getHiddenClassName(Class<?> lookupClass) {
            return lookupClass.getName().replace('.', '/');
        }

        public static ClassWriter getClassWriter(Class<?> ownerClassName, int x) {
            ClassWriter cw = new ClassWriter(ClassWriter.COMPUTE_MAXS);

            cw.visit(V1_6, ACC_PUBLIC + ACC_SUPER, getHiddenClassName(ownerClassName),
                     null, "java/lang/Object", new String[] {DynamicLambdaTest.class.getName().replace('.', '/') + "$Test"});

            //default constructor
            {
                MethodVisitor mv = cw.visitMethod(ACC_PUBLIC, "<init>", "()V", null, null);
                mv.visitCode();
                mv.visitVarInsn(ALOAD, 0);
                mv.visitMethodInsn(INVOKESPECIAL, "java/lang/Object", "<init>", "()V");
                mv.visitInsn(RETURN);
                mv.visitMaxs(0, 0);
                mv.visitEnd();
            }

            //test method
            {
                MethodVisitor mv = cw.visitMethod(ACC_PUBLIC, "test",
                                                  "(I)I", null, null);
                mv.visitVarInsn(ILOAD, 1);
                mv.visitLdcInsn(x);
                mv.visitInsn(IADD);
                mv.visitInsn(IRETURN);
                mv.visitMaxs(0, 0);
                mv.visitEnd();
            }

            cw.visitEnd();
            return cw;
        }
    }
}
