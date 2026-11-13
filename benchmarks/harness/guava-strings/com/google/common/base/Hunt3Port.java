package com.google.common.base;

// Hunt3 batch2 harness-only port (#17 Guava Caliper base benchmarks). Upstream benchmarks are
// Caliper 1.0-beta-3 (which runs fine on the JVM; see jvm-run.log). This class ONLY sets the
// upstream @Param fields to the FULL upstream @Param value sets, calls the upstream setUp()
// (@BeforeExperiment), and loops the upstream @Benchmark methods (int x(int reps) / void
// x(long reps)). No benchmark logic is changed or duplicated. Calibrate reps so one call takes
// ~TARGET_MS; WARM warm-up + MEAS measured calls; print PORT-RESULT lines. Args: WARM MEAS.
import java.lang.reflect.Method;

public class Hunt3Port {

  static final long TARGET_MS = 80;

  interface Call { int call(int reps) throws Exception; }

  public static void main(String[] args) throws Exception {
    int warm = args.length > 0 ? Integer.parseInt(args[0]) : 2;
    int meas = args.length > 1 ? Integer.parseInt(args[1]) : 4;
    long checksum = 0;

    // ---- JoinerBenchmark: count {3,30,300} x componentLength {0,1,16,32,100}, 7 methods
    for (int count : new int[] {3, 30, 300}) {
      for (int componentLength : new int[] {0, 1, 16, 32, 100}) {
        JoinerBenchmark b = new JoinerBenchmark();
        b.count = count;
        b.componentLength = componentLength;
        b.setUp();
        String ps = "count=" + count + " componentLength=" + componentLength;
        checksum ^= run("joinerWithStringDelimiter", ps, warm, meas, b::joinerWithStringDelimiter);
        checksum ^= run("joinerWithCharacterDelimiter", ps, warm, meas, b::joinerWithCharacterDelimiter);
        checksum ^= run("joinerInlined", ps, warm, meas, b::joinerInlined);
        checksum ^= run("stringBuilderIsEmpty", ps, warm, meas, b::stringBuilderIsEmpty);
        checksum ^= run("booleanIfFirst", ps, warm, meas, b::booleanIfFirst);
        checksum ^= run("assignDelimiter", ps, warm, meas, b::assignDelimiter);
        checksum ^= run("alwaysAppendThenBackUp", ps, warm, meas, b::alwaysAppendThenBackUp);
      }
    }

    // ---- SplitterBenchmark: length {1,10,100,1000} x text {xxxx,xxXx,xXxX,XXXX}, 2 methods
    for (int length : new int[] {1, 10, 100, 1000}) {
      for (String text : new String[] {"xxxx", "xxXx", "xXxX", "XXXX"}) {
        SplitterBenchmark b = new SplitterBenchmark();
        b.length = length;
        b.text = text;
        b.setUp();
        String ps = "length=" + length + " text=" + text;
        checksum ^= run("charSplitter", ps, warm, meas, b::charSplitter);
        checksum ^= run("stringSplitter", ps, warm, meas, b::stringSplitter);
      }
    }

    // ---- ToStringHelperBenchmark: dataSize {0,1,5} x omitNulls {false,true} x dataset (3), 1 method
    for (int dataSize : new int[] {0, 1, 5}) {
      for (boolean omitNulls : new boolean[] {false, true}) {
        for (ToStringHelperBenchmark.Dataset dataset : ToStringHelperBenchmark.Dataset.values()) {
          ToStringHelperBenchmark b = new ToStringHelperBenchmark();
          b.dataSize = dataSize;
          b.omitNulls = omitNulls;
          b.dataset = dataset;
          // no @BeforeExperiment in this benchmark: toString() builds its own helper each rep
          checksum ^= run("toString", "dataSize=" + dataSize + " omitNulls=" + omitNulls
              + " dataset=" + dataset, warm, meas, b::toString);
        }
      }
    }

    // ---- CharMatcherBenchmark: config (9) x length {64,1024} x percent {0,10,50,100}
    //      x precomputed {true} x size {DEFAULT,SMALL} x forceSlow {false} x web {false}, 2 methods
    for (BenchmarkHelpers.SampleMatcherConfig config : BenchmarkHelpers.SampleMatcherConfig.values()) {
      for (int length : new int[] {64, 1024}) {
        for (int percent : new int[] {0, 10, 50, 100}) {
          for (CharMatcherBenchmark.Size size : CharMatcherBenchmark.Size.values()) {
            CharMatcherBenchmark b = new CharMatcherBenchmark();
            b.config = config;
            b.length = length;
            b.percent = percent;
            b.precomputed = true;
            b.size = size;
            b.forceSlow = false;
            b.web = false;
            b.setUp();
            String ps = "config=" + config + " length=" + length + " percent=" + percent
                + " size=" + size;
            checksum ^= run("trimAndCollapseFromString", ps, warm, meas, b::trimAndCollapseFromString);
            checksum ^= run("matches", ps, warm, meas, b::matches);
          }
        }
      }
    }

    // ---- StringsRepeatBenchmark: count {1,5,25,125} x length {1,10}, 3 methods (void, long reps)
    for (int count : new int[] {1, 5, 25, 125}) {
      for (int length : new int[] {1, 10}) {
        StringsRepeatBenchmark b = new StringsRepeatBenchmark();
        b.count = count;
        b.length = length;
        b.setUp();
        String ps = "count=" + count + " length=" + length;
        checksum ^= runVoid(b, "oldRepeat", ps, warm, meas);
        checksum ^= runVoid(b, "mikeRepeat", ps, warm, meas);
        checksum ^= runVoid(b, "martinRepeat", ps, warm, meas);
      }
    }
    System.out.println("PORT-DONE checksum=" + checksum);
  }

  static int run(String name, String params, int warm, int meas, Call c) throws Exception {
    int reps = 1;
    while (reps <= (1 << 24)) {
      long t = System.nanoTime();
      c.call(reps);
      if (System.nanoTime() - t > TARGET_MS * 1_000_000L) break;
      reps *= 2;
    }
    for (int i = 0; i < warm; i++) c.call(reps);
    long best = Long.MAX_VALUE;
    int dummy = 0;
    for (int i = 0; i < meas; i++) {
      long t = System.nanoTime();
      dummy ^= c.call(reps);
      best = Math.min(best, System.nanoTime() - t);
    }
    System.out.println("PORT-RESULT bench=" + name + " " + params + " reps=" + reps
        + " nsPerRep=" + (best / reps) + " (best of " + meas + ")");
    return dummy;
  }

  // void x(long reps) methods: no return value to defeat optimization (upstream relies on the
  // length check inside); time via the same calibrate/warm/measure shape.
  static int runVoid(StringsRepeatBenchmark b, String name, String params, int warm, int meas)
      throws Exception {
    Method m = StringsRepeatBenchmark.class.getDeclaredMethod(name, long.class);
    long reps = 1;
    while (reps <= (1 << 24)) {
      long t = System.nanoTime();
      m.invoke(b, reps);
      if (System.nanoTime() - t > TARGET_MS * 1_000_000L) break;
      reps *= 2;
    }
    for (int i = 0; i < warm; i++) m.invoke(b, reps);
    long best = Long.MAX_VALUE;
    for (int i = 0; i < meas; i++) {
      long t = System.nanoTime();
      m.invoke(b, reps);
      best = Math.min(best, System.nanoTime() - t);
    }
    System.out.println("PORT-RESULT bench=" + name + " " + params + " reps=" + reps
        + " nsPerRep=" + (best / reps) + " (best of " + meas + ")");
    return (int) (best ^ reps);
  }
}
