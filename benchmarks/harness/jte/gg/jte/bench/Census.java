package gg.jte.bench;

import gg.jte.output.Utf8ByteOutput;

import java.lang.management.ManagementFactory;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.zip.CRC32;

/**
 * C96 jte phase 2 census (JVM and native image): per variant
 *   OUT <variant> len=<bytes> crc=<crc32>      the rendered page (String -> UTF-8 bytes; Utf8ByteOutput.toByteArray)
 *   CENSUS <variant> bop=<B/op> nsop=<ns/op> a1=<bytes> a2=<bytes>
 * B/op = exact per-thread allocated bytes (com.sun.management.ThreadMXBean, supported by SubstrateThreadMXBean),
 * two-length slope (N2 - N1 renders) after a warmup; -1 if the bean is unavailable. The render results are consumed
 * only through length()/getContentLength() in the loops (whitelisted usages), and through getBytes/toByteArray for
 * the output check. args: [variant regex]; -Dcensus.dump=<dir> writes <variant>.out files; -Dcensus.warm/n1/n2.
 */
public final class Census {
    static final String[] NAMES = {"upstreamTemplateOutput", "upstreamStringBuilder", "engineString", "engineUtf8",
            "directString", "engineStringEsc", "engineUtf8Esc"};
    static long sinkLen;

    static long once(Variants v, int k) {
        switch (k) {
            case 0: return v.upstreamTemplateOutput().length();
            case 1: return v.upstreamStringBuilder().length();
            case 2: return v.engineString().length();
            case 3: return v.engineUtf8().getContentLength();
            case 4: return v.directString().length();
            case 5: return v.engineStringEsc().length();
            case 6: return v.engineUtf8Esc().getContentLength();
            default: throw new IllegalArgumentException("variant " + k);
        }
    }

    static byte[] output(Variants v, int k) {
        switch (k) {
            case 0: return v.upstreamTemplateOutput().getBytes(StandardCharsets.UTF_8);
            case 1: return v.upstreamStringBuilder().getBytes(StandardCharsets.UTF_8);
            case 2: return v.engineString().getBytes(StandardCharsets.UTF_8);
            case 3: return v.engineUtf8().toByteArray();
            case 4: return v.directString().getBytes(StandardCharsets.UTF_8);
            case 5: return v.engineStringEsc().getBytes(StandardCharsets.UTF_8);
            case 6: return v.engineUtf8Esc().toByteArray();
            default: throw new IllegalArgumentException("variant " + k);
        }
    }

    static long allocated() {
        try {
            return ((com.sun.management.ThreadMXBean) ManagementFactory.getThreadMXBean()).getCurrentThreadAllocatedBytes();
        } catch (Throwable t) {
            return -1;
        }
    }

    public static void main(String[] args) throws Exception {
        String only = args.length > 0 ? args[0] : ".*";
        long warm = Long.getLong("census.warm", 200_000L);
        long n1 = Long.getLong("census.n1", 200_000L);
        long n2 = Long.getLong("census.n2", 1_000_000L);
        String dump = System.getProperty("census.dump");
        Variants v = new Variants();
        for (int k = 0; k < NAMES.length; k++) {
            if (!NAMES[k].matches(only)) {
                continue;
            }
            byte[] out = output(v, k);
            CRC32 crc = new CRC32();
            crc.update(out);
            System.out.println("OUT " + NAMES[k] + " len=" + out.length + " crc=" + Long.toHexString(crc.getValue()));
            if (dump != null) {
                Files.createDirectories(Path.of(dump));
                Files.write(Path.of(dump, NAMES[k] + ".out"), out);
            }
            for (long i = 0; i < warm; i++) {
                sinkLen += once(v, k);
            }
            long a0 = allocated();
            for (long i = 0; i < n1; i++) {
                sinkLen += once(v, k);
            }
            long a1 = allocated() - a0;
            long b0 = allocated();
            long t0 = System.nanoTime();
            for (long i = 0; i < n2; i++) {
                sinkLen += once(v, k);
            }
            long t = System.nanoTime() - t0;
            long a2 = allocated() - b0;
            double bop = a0 < 0 ? -1 : (double) (a2 - a1) / (n2 - n1);
            System.out.printf("CENSUS %s bop=%.1f nsop=%.1f a1=%d a2=%d%n", NAMES[k], bop, (double) t / n2, a1, a2);
        }
        System.out.println("sink " + sinkLen);
    }
}
