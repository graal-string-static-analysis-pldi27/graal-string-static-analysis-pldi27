package org.apache.commons.codec.language.bm;

import java.lang.reflect.Method;

/**
 * C98 hunt3 batch4 (#42): harness-only main for the upstream JUnit perf test
 * PhoneticEnginePerformanceTest (batch3 handlebars HbsBench precedent: a minimal main that runs the
 * upstream benchmark method unchanged). The test class is package-private; this main lives in the same
 * package and invokes the @Test method test() directly (80000 x engine.encode("Angelo"), unchanged).
 */
public class Hunt3PerfMain {
    public static void main(String[] args) throws Exception {
        Class<?> cls = Class.forName("org.apache.commons.codec.language.bm.PhoneticEnginePerformanceTest");
        Object t = cls.getDeclaredConstructor().newInstance();
        Method m = cls.getDeclaredMethod("test");
        m.setAccessible(true);
        m.invoke(t);
    }
}
