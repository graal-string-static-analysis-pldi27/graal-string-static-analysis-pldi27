package gg.jte.bench;

import gg.jte.output.Utf8ByteOutput;
import org.openjdk.jmh.annotations.*;

import java.util.concurrent.TimeUnit;

/** C96 jte phase 2 JMH benchmark; settings as upstream TemplateOutputTest (avgt ns, 5x1s warmup, 5x1s measurement). */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Thread)
@Fork(1)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
public class JteBench {
    private Variants v;

    @Setup
    public void setup() {
        v = new Variants();
    }

    @Benchmark
    public String engineString() {
        return v.engineString();
    }

    @Benchmark
    public Utf8ByteOutput engineUtf8() {
        return v.engineUtf8();
    }

    @Benchmark
    public String directString() {
        return v.directString();
    }

    @Benchmark
    public String engineStringEsc() {
        return v.engineStringEsc();
    }

    @Benchmark
    public Utf8ByteOutput engineUtf8Esc() {
        return v.engineUtf8Esc();
    }
}
