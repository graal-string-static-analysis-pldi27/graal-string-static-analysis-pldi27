/*
 * C98 hunt3 batch3 harness-only port (#22, jknack/handlebars.java HbsBench).
 * Minimal main that calls the UPSTREAM benchmark methods unchanged:
 *   HbsBench.setup()    (guarded upstream by assumeTrue(run.bench); we pass -Drun.bench=true)
 *   HbsBench.benchmark()  (the upstream Bench(1000, 5, 30) harness: 5 warmup + 30 measured 1s iterations)
 * Nothing else: no workload code here, upstream JUnit test methods are invoked as-is.
 */
package com.github.jknack.handlebars.bench;

public class Hunt3BenchMain {

  public static void main(String[] args) throws Exception {
    HbsBench bench = new HbsBench();
    bench.setup();
    bench.benchmark();
  }
}
