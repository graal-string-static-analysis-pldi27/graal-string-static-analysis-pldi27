package com.google.gson.metrics;

// Hunt3 harness-only port (batch1 #9). Upstream gson metrics benchmarks are Caliper 1.0-beta-3
// (whose runner artifact is not even a declared dependency at this pin). This class ONLY sets the
// upstream @Param fields to the values named in the hunt3 deployment notes, calls the upstream
// setUp() (@BeforeExperiment), and loops the upstream timeParse(int reps) /
// timeObjectSerialization(int reps) methods. No benchmark logic is changed or duplicated.
import java.lang.reflect.Field;

public class Hunt3Port {

  public static void main(String[] args) throws Exception {
    // ParseBenchmark: document x api (deployment-note values); private enums -> reflection
    String[] documents = {"TWEETS", "READER_SHORT", "READER_LONG"};
    String[] apis = {"GSON_STREAM", "GSON_DOM", "GSON_BIND"};
    for (String doc : documents) {
      for (String api : apis) {
        ParseBenchmark bench = new ParseBenchmark();
        setEnum(bench, "document", doc);
        setEnum(bench, "api", api);
        bench.setUp();
        int reps = calibrateParse(bench);
        for (int i = 0; i < 3; i++) bench.timeParse(reps);
        long best = Long.MAX_VALUE;
        for (int i = 0; i < 8; i++) {
          long t = System.nanoTime();
          bench.timeParse(reps);
          best = Math.min(best, System.nanoTime() - t);
        }
        System.out.println("PORT-RESULT bench=parse document=" + doc + " api=" + api
            + " reps=" + reps + " nsPerRep=" + (best / reps) + " (best of 8)");
      }
    }
    // SerializationBenchmark: pretty in {false, true}
    for (String pretty : new String[] {"false", "true"}) {
      SerializationBenchmark bench = new SerializationBenchmark();
      Field f = SerializationBenchmark.class.getDeclaredField("pretty");
      f.setAccessible(true);
      f.setBoolean(bench, Boolean.parseBoolean(pretty));
      bench.setUp();
      int reps = calibrateSer(bench);
      for (int i = 0; i < 3; i++) bench.timeObjectSerialization(reps);
      long best = Long.MAX_VALUE;
      for (int i = 0; i < 8; i++) {
        long t = System.nanoTime();
        bench.timeObjectSerialization(reps);
        best = Math.min(best, System.nanoTime() - t);
      }
      System.out.println("PORT-RESULT bench=serialize pretty=" + pretty
          + " reps=" + reps + " nsPerRep=" + (best / reps) + " (best of 8)");
    }
    System.out.println("PORT-DONE");
  }

  @SuppressWarnings({"unchecked", "rawtypes"})
  static void setEnum(Object o, String field, String value) throws Exception {
    Field f = o.getClass().getDeclaredField(field);
    f.setAccessible(true);
    Class<? extends Enum> t = (Class<? extends Enum>) f.getType();
    f.set(o, Enum.valueOf(t, value));
  }

  static int calibrateParse(ParseBenchmark b) throws Exception {
    int reps = 1;
    while (reps <= (1 << 20)) {
      long t = System.nanoTime();
      b.timeParse(reps);
      if (System.nanoTime() - t > 250_000_000L) break;
      reps *= 2;
    }
    return reps;
  }

  static int calibrateSer(SerializationBenchmark b) {
    int reps = 1;
    while (reps <= (1 << 26)) {
      long t = System.nanoTime();
      b.timeObjectSerialization(reps);
      if (System.nanoTime() - t > 250_000_000L) break;
      reps *= 2;
    }
    return reps;
  }

  private Hunt3Port() {}
}
