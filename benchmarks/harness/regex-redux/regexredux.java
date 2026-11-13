
/*
   The Computer Language Benchmarks Game
   https://salsa.debian.org/benchmarksgame-team/benchmarksgame/

   contributed by Francois Green
*/

import java.io.*;

import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.Map.Entry;
import java.util.function.*;
import java.util.regex.*;

import static java.util.stream.Collectors.*;

public class regexredux {

  public static void main(String[] args) throws IOException {
    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    {
        byte[] buf = new byte[65536];
        int count;
        while ((count = System.in.read(buf)) > 0) {
            baos.write(buf, 0, count);
        }
    }
    // C99 uniform protocol: stdin is read once; hunt.iters iterations (default 1) of the rest of main (decode ..
    // replacements.join()), one "HUNT-ITER <k> ns=<n>" stderr line per iteration when iters > 1; the result lines
    // of the last iteration are printed after the loop (stdout unchanged)
    final int iters = Integer.getInteger("hunt.iters", 1);
    List<String> out = null;
    for (int k = 1; k <= iters; k++) {
    final long t0 = System.nanoTime();
    final List<String> lines = new ArrayList<>();
    final String input = baos.toString("US-ASCII");

    final int initialLength = input.length();

    final String sequence = input.replaceAll(">.*\n|\n", "");

    CompletableFuture<String> replacements = CompletableFuture.supplyAsync(() -> {
        final Map<String, String> iub = new LinkedHashMap<>();
        iub.put("tHa[Nt]", "<4>");
        iub.put("aND|caN|Ha[DS]|WaS", "<3>");
        iub.put("a[NSt]|BY", "<2>");
        iub.put("<[^>]*>", "|");
        iub.put("\\|[^|][^|]*\\|", "-");

        String buffer = sequence;
        for (Map.Entry<String, String> entry : iub.entrySet()) {
            buffer = Pattern.compile(entry.getKey()).matcher(buffer).replaceAll(entry.getValue());
        }
        return buffer;
    });

    final int codeLength = sequence.length();

    final List<String> variants = Arrays.asList("agggtaaa|tttaccct",
                                                "[cgt]gggtaaa|tttaccc[acg]",
                                                "a[act]ggtaaa|tttacc[agt]t",
                                                "ag[act]gtaaa|tttac[agt]ct",
                                                "agg[act]taaa|ttta[agt]cct",
                                                "aggg[acg]aaa|ttt[cgt]ccct",
                                                "agggt[cgt]aa|tt[acg]accct",
                                                "agggta[cgt]a|t[acg]taccct",
                                                "agggtaa[cgt]|[acg]ttaccct");

    BiFunction<String, String, Entry<String, Long>> counts = (v, s) -> {
      Long count = Pattern.compile(v).splitAsStream(s).count() - 1; //Off by one
      return new AbstractMap.SimpleEntry<>(v, count);
    };

    final Map<String, Long> results = variants.parallelStream()
                                              .map(variant -> counts.apply(variant, sequence))
                                              .collect(toMap(Map.Entry::getKey, Map.Entry::getValue));

    variants.forEach(variant -> lines.add(variant + " " + results.get(variant)));

    lines.add("");
    lines.add(String.valueOf(initialLength));
    lines.add(String.valueOf(codeLength));
    lines.add(String.valueOf(replacements.join().length()));
    final long ns = System.nanoTime() - t0;
    if (iters > 1) System.err.println("HUNT-ITER " + k + " ns=" + ns);
    out = lines;
    }
    for (String l : out) System.out.println(l);
  }
}
    