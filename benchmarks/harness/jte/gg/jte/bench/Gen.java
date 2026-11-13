package gg.jte.bench;

import gg.jte.ContentType;
import gg.jte.TemplateEngine;
import gg.jte.resolve.DirectoryCodeResolver;

import java.nio.file.Path;

/**
 * C96 jte phase 2: generates the Java sources of the upstream benchmark templates (jte/src/test/resources/benchmark)
 * exactly as the upstream jte Benchmark/Benchmark_Binary configure the engine (ContentType.Html, trimControlStructures),
 * in "generate" mode (no runtime javac; the classes are compiled ahead of time and loaded by the application class
 * loader through TemplateEngine.createPrecompiled, as a native image requires).
 * usage: Gen <template dir> <out dir> <package> <binary:true|false>
 */
public final class Gen {
    public static void main(String[] a) {
        TemplateEngine e = TemplateEngine.create(new DirectoryCodeResolver(Path.of(a[0])), Path.of(a[1]), ContentType.Html, null, a[2]);
        e.setTrimControlStructures(true);
        e.setBinaryStaticContent(Boolean.parseBoolean(a[3]));
        System.out.println("generated " + e.generateAll());
    }
}
