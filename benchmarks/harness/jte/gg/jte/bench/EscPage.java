package gg.jte.bench;

import gg.jte.benchmark.WelcomePage;

/**
 * NOT upstream: the upstream page data contains no character that jte escapes, so gg.jte.html.escape.Escape never
 * splits a value. This page puts escapable characters into the title (tag body: htmlContent) and the description
 * (attribute: htmlAttribute) to exercise Escape.flushAndEscape -> writeContent(value, from, to), which on
 * Utf8ByteOutput is value.substring(from, to).getBytes(UTF_8) (the only StringView candidate on the render path).
 */
public class EscPage extends WelcomePage {
    public EscPage(int visits) {
        super(visits);
    }

    @Override
    public String getTitle() {
        return "Tom & Jerry <Welcome> page of the benchmark site";
    }

    @Override
    public String getDescription() {
        return "Say \"hi\" & 'bye' to the <benchmark> site, a long description that is split by escapes";
    }
}
