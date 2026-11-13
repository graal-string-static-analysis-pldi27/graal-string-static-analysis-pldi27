/*
 * Copyright (c) 2026, 2026, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package com.oracle.svm.hosted.stringanalysis;

import java.lang.reflect.Method;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.RepConcat;
import com.oracle.svm.core.stringrep.StringView;

/**
 * Concat operand copies: the copy-shape function, the child's acceptance and
 * {@code CONCAT_COPY} emission, the profile round trip, the parent's factory choice, and {@link RepConcat}'s
 * equivalence with the JDK's indy concat (hosted fallback; the image path is pinned by the full-path shapes).
 */
public class ConcatCopyTest {

    private static final String MCWC = "makeConcatWithConstants";

    @Test
    public void knobDefaultsOn() {
        Assert.assertFalse("the diagnostic is off by default", RepConcat.COUNT);
    }

    @Test
    public void copyShapeTruthTable() {
        Assert.assertEquals(StringAtoms.CopyShape.UNARY, StringAtoms.scfCopyShape(MCWC, "\u0001", new boolean[]{false}));
        Assert.assertEquals(StringAtoms.CopyShape.BINARY, StringAtoms.scfCopyShape(MCWC, "\u0001\u0001", new boolean[]{false, false}));
        Assert.assertEquals(StringAtoms.CopyShape.UNARY, StringAtoms.scfCopyShape("makeConcat", null, new boolean[]{false}));
        Assert.assertEquals(StringAtoms.CopyShape.BINARY, StringAtoms.scfCopyShape("makeConcat", null, new boolean[]{false, false}));
        Assert.assertEquals("a primitive unary", StringAtoms.CopyShape.NONE, StringAtoms.scfCopyShape(MCWC, "\u0001", new boolean[]{true}));
        Assert.assertEquals("a primitive binary", StringAtoms.CopyShape.NONE, StringAtoms.scfCopyShape(MCWC, "\u0001\u0001", new boolean[]{false, true}));
        Assert.assertEquals("a prefix", StringAtoms.CopyShape.NONE, StringAtoms.scfCopyShape(MCWC, "x\u0001", new boolean[]{false}));
        Assert.assertEquals("a separator", StringAtoms.CopyShape.NONE, StringAtoms.scfCopyShape(MCWC, "\u0001-\u0001", new boolean[]{false, false}));
        Assert.assertEquals("three operands", StringAtoms.CopyShape.NONE, StringAtoms.scfCopyShape(MCWC, "\u0001\u0001\u0001", new boolean[]{false, false, false}));
        Assert.assertEquals("a \\2 tag", StringAtoms.CopyShape.UNKNOWN, StringAtoms.scfCopyShape(MCWC, "\u0002\u0001", new boolean[]{false}));
        Assert.assertEquals("malformed", StringAtoms.CopyShape.UNKNOWN, StringAtoms.scfCopyShape(MCWC, "\u0001", new boolean[]{false, false}));
        Assert.assertEquals("no recipe", StringAtoms.CopyShape.UNKNOWN, StringAtoms.scfCopyShape(MCWC, null, new boolean[]{false}));
        Assert.assertEquals("another bootstrap", StringAtoms.CopyShape.UNKNOWN, StringAtoms.scfCopyShape("other", "\u0001", new boolean[]{false}));
        // scfCopiesOperand is exactly "not NONE"
        Assert.assertTrue(StringAtoms.scfCopiesOperand(MCWC, "\u0002\u0001", new boolean[]{false}));
        Assert.assertFalse(StringAtoms.scfCopiesOperand(MCWC, "x\u0001", new boolean[]{false}));
    }

    // ---------------------------------------------------------------- child

    private static SugVertex substringCandidate(StringUtilizationGraph graph, String loc) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName("substring");
        v.setMethodSignature("I,I");
        v.setDeclaringClass("java.lang.String");
        v.setSourceLocation(loc);
        v.setEnclosingClassName("TestUserClass");
        return v;
    }

    private static SugVertex copySite(StringUtilizationGraph graph, String loc, StringAtoms.CopyShape shape, String enclosing) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        v.setMethodName(MCWC);
        v.setSourceLocation(loc);
        v.setEnclosingClassName(enclosing);
        if (shape != null) {
            v.markScfCopyShape(shape);
        }
        return v;
    }

    @Test
    public void lowerableCopySiteRule() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex user = copySite(graph, "U#m()V@3", StringAtoms.CopyShape.BINARY, "TestUserClass");
        Assert.assertTrue(StringViewHeuristic.isLowerableCopySite(user));
        Assert.assertFalse("a JDK-internal site", StringViewHeuristic.isLowerableCopySite(copySite(graph, "java.util.X#m()V@3", StringAtoms.CopyShape.BINARY, "java.util.X")));
        Assert.assertFalse("no enclosing class", StringViewHeuristic.isLowerableCopySite(copySite(graph, "U#m()V@4", StringAtoms.CopyShape.UNARY, null)));
        Assert.assertFalse("UNKNOWN / unmarked", StringViewHeuristic.isLowerableCopySite(copySite(graph, "U#m()V@5", null, "TestUserClass")));
    }

    /** A view at a user-code copying site ADMITs and is listed as a CONCAT_COPY site; a JDK-internal or unmarked one rejects. */
    @Test
    public void viewAtCopyingSiteAdmitsAndIsEmitted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "U#a()V@1");
        SugVertex c = copySite(graph, "U#a()V@9", StringAtoms.CopyShape.BINARY, "TestUserClass");
        graph.addEdge(sub, c, SugEdgeType.CONCAT_LEFT, -1);
        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);
        Assert.assertEquals(heuristic.getRejections().toString(), 1, decisions.size());
        Assert.assertEquals(Map.of("U#a()V@9", StringAtoms.CopyShape.BINARY), StringViewHeuristic.copyingConcatSites(graph, sub));
        Assert.assertTrue("not a non-copying operand site (the IC concat group listing is unchanged)", StringViewHeuristic.concatOperandSites(graph, sub).isEmpty());
        Assert.assertEquals(List.of("U#a()V@9 CONCAT_COPY BINARY"), StringViewHeuristic.concatCopyLines(graph, decisions));

        for (String enclosing : new String[]{"java.util.X", null}) {
            StringUtilizationGraph g = new StringUtilizationGraph();
            SugVertex s = substringCandidate(g, "U#a()V@1");
            g.addEdge(s, copySite(g, "U#a()V@9", StringAtoms.CopyShape.UNARY, enclosing), SugEdgeType.CONCAT_LEFT, -1);
            StringViewHeuristic h = new StringViewHeuristic();
            Assert.assertTrue(String.valueOf(enclosing), h.apply(g).isEmpty());
            Assert.assertTrue(h.getRejections().get(0).contains("concat expression @ U#a()V@9"));
            Assert.assertTrue(StringViewHeuristic.copyingConcatSites(g, s).isEmpty());
        }
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex s = substringCandidate(g, "U#a()V@1");
        g.addEdge(s, copySite(g, "U#a()V@9", null, "TestUserClass"), SugEdgeType.CONCAT_LEFT, -1);
        Assert.assertTrue("an UNKNOWN copying site keeps the reject", new StringViewHeuristic().apply(g).isEmpty());
    }

    /** A kept LAZY_CONCAT decision at a CONCAT_COPY key is the nested-concat pass's invariant violation: it fails. */
    @Test
    public void concatCopyWithKeptLazySiteFails() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "U#a()V@1");
        SugVertex c = copySite(graph, "U#a()V@9", StringAtoms.CopyShape.BINARY, "TestUserClass");
        graph.addEdge(sub, c, SugEdgeType.CONCAT_LEFT, -1);
        List<InstrumentationDecision> decisions = new StringViewHeuristic().apply(graph);
        List<InstrumentationDecision> both = new java.util.ArrayList<>(decisions);
        both.add(new InstrumentationDecision(c, OptimizationType.LAZY_CONCAT, "ROPE"));
        Assert.assertThrows(IllegalStateException.class, () -> StringViewHeuristic.concatCopyLines(graph, both));
    }

    // ---------------------------------------------------------------- profile

    private static RepresentationProfile load(String... lines) throws Exception {
        Path p = Files.createTempFile("c97-cat", ".txt");
        try {
            Files.write(p, List.of(lines));
            return RepresentationProfileLoader.load(p.toString());
        } finally {
            Files.deleteIfExists(p);
        }
    }

    @Test
    public void profileRoundTrip() throws Exception {
        RepresentationProfile prof = load("U#a()V@1 STRING_VIEW", "U#a()V@9 CONCAT_COPY BINARY", "U#b()V@2 CONCAT_COPY UNARY");
        Assert.assertEquals("BINARY", prof.getConcatCopyShape("U#a()V@9"));
        Assert.assertEquals("UNARY", prof.getConcatCopyShape("U#b()V@2"));
        Assert.assertNull(prof.getConcatCopyShape("U#a()V@1"));
        Assert.assertEquals("CONCAT_COPY lines are not entries", 1, prof.getTotalCount());
        Assert.assertThrows(IllegalArgumentException.class, () -> load("U#a()V@9 CONCAT_COPY UNKNOWN"));
        Assert.assertThrows(IllegalArgumentException.class, () -> load("U#a()V@9 CONCAT_COPY BINARY", "U#a()V@9 CONCAT_COPY UNARY"));
        Assert.assertThrows(IllegalArgumentException.class, () -> load("U#a()V@9 CONCAT_COPY BINARY", "U#a()V@9 LAZY_CONCAT ROPE"));
    }

    // ---------------------------------------------------------------- parent

    @Test
    public void factoryByDeclaredTypes() throws Exception {
        Method m = StringRepresentationReplacementPlugin.repConcatFactory(new Class<?>[]{String.class, String.class});
        Assert.assertEquals(List.of(String.class, String.class), List.of(m.getParameterTypes()));
        m = StringRepresentationReplacementPlugin.repConcatFactory(new Class<?>[]{CharSequence.class, String.class});
        Assert.assertEquals(List.of(Object.class, String.class), List.of(m.getParameterTypes()));
        m = StringRepresentationReplacementPlugin.repConcatFactory(new Class<?>[]{Integer.class});
        Assert.assertEquals("concat1", m.getName());
        Assert.assertEquals(List.of(Object.class), List.of(m.getParameterTypes()));
        Assert.assertThrows(NoSuchMethodException.class, () -> StringRepresentationReplacementPlugin.repConcatFactory(new Class<?>[]{int.class}));
        Assert.assertThrows(NoSuchMethodException.class, () -> StringRepresentationReplacementPlugin.repConcatFactory(new Class<?>[]{String.class, String.class, String.class}));
    }

    // ---------------------------------------------------------------- RepConcat vs the JDK

    /** Counts its toString() calls; returns {@code value} (possibly null). */
    static final class Probe {
        final String value;
        int calls;

        Probe(String value) {
            this.value = value;
        }

        @Override
        public String toString() {
            calls++;
            return value;
        }
    }

    private static void assertFreshEqual(String expected, String actual, Object... operands) {
        Assert.assertEquals(expected, actual);
        Assert.assertSame(String.class, actual.getClass());
        Assert.assertEquals(expected.hashCode(), actual.hashCode());
        Assert.assertEquals(expected.isLatin1(), actual.isLatin1());
        for (Object o : operands) {
            Assert.assertNotSame("JLS 15.18.1: a newly created String", o, actual);
        }
    }

    /** A plain compact String with the content of {@code s} (a view's chars through its own toCharArray). */
    private static String plain(String s) {
        return String.valueOf(s.toCharArray());
    }

    private static String latin1View() {
        return StringView.create("xhello", 1, 6); // "hello"
    }

    private static String utf16View() {
        return StringView.create("x€abĀ", 1, 5); // "€abĀ"
    }

    @Test
    public void viewsAreRealViews() {
        Assert.assertSame(StringView.class, latin1View().getClass());
        Assert.assertSame(StringView.class, utf16View().getClass());
    }

    @Test
    public void binaryMatchesJdk() {
        String[] plain = {"", "a", "abc", "€", new String("")};
        java.util.List<String> ops = new java.util.ArrayList<>(List.of(plain));
        ops.add(latin1View());
        ops.add(utf16View());
        for (String a : ops) {
            for (String b : ops) {
                String jdk = plain(a) + plain(b); // the JDK reference on plain copies (stock copies a view's value(): null)
                assertFreshEqual(jdk, RepConcat.concat2(a, b), a, b);
                assertFreshEqual(jdk, RepConcat.concat2((Object) a, (Object) b), a, b);
                assertFreshEqual(jdk, RepConcat.concat2(a, (Object) b), a, b);
                assertFreshEqual(jdk, RepConcat.concat2((Object) a, b), a, b);
            }
        }
        assertFreshEqual("null" + "x", RepConcat.concat2((String) null, "x"));
        assertFreshEqual("xnull", RepConcat.concat2("x", (String) null));
        assertFreshEqual("nullnull", RepConcat.concat2((Object) null, (Object) null));
    }

    @Test
    public void unaryMatchesJdk() {
        for (String s : new String[]{"", "a", "€z", latin1View(), utf16View()}) {
            assertFreshEqual("" + plain(s), RepConcat.concat1(s), s);
            assertFreshEqual("" + plain(s), RepConcat.concat1((Object) s), s);
        }
        assertFreshEqual("null", RepConcat.concat1((String) null));
        assertFreshEqual("null", RepConcat.concat1((Object) null));
        CharSequence sb = new StringBuilder("sb");
        assertFreshEqual("" + sb, RepConcat.concat1((Object) sb));
    }

    /** stringOf: a null toString() gives "null"; each toString() exactly once, first operand first. */
    @Test
    public void toStringOnceInOrder() {
        StringBuilder order = new StringBuilder();
        Object a = new Object() {
            @Override
            public String toString() {
                order.append('a');
                return "";
            }
        };
        Object b = new Object() {
            @Override
            public String toString() {
                order.append('b');
                return null;
            }
        };
        Assert.assertEquals("" + a + b, "null");
        order.setLength(0);
        assertFreshEqual("null", RepConcat.concat2(a, b));
        Assert.assertEquals("ab", order.toString());
        Probe p = new Probe("v");
        assertFreshEqual("v", RepConcat.concat1(p));
        Assert.assertEquals(1, p.calls);
        Probe q = new Probe(null);
        assertFreshEqual("vnull", RepConcat.concat2(p, q));
        Assert.assertEquals(2, p.calls);
        Assert.assertEquals(1, q.calls);
    }

    /** The empty-operand path: a plain other side is the JDK's new String(s) (fresh, equal); a view gets a flat copy. */
    @Test
    public void emptyOperandPath() {
        String s = "abc";
        String r = RepConcat.concat2("", s);
        Assert.assertNotSame(s, r);
        Assert.assertEquals(s, r);
        String v = latin1View();
        String rv = RepConcat.concat2(v, "");
        Assert.assertSame(String.class, rv.getClass());
        Assert.assertEquals("hello", rv);
        Assert.assertTrue(rv.isLatin1());
        String uv = utf16View();
        String ru = RepConcat.concat2("", uv);
        Assert.assertSame(String.class, ru.getClass());
        Assert.assertEquals("€abĀ", ru);
        Assert.assertFalse(ru.isLatin1());
    }

    /** Any failure inside lowerCopyIndy becomes a ConcatCopyFailure (the build fails, never stock). */
    @Test
    public void lowerCopyFailureNeverStock() {
        RuntimeException e = StringRepresentationReplacementPlugin.asConcatCopyFailure("M.m@3", new IllegalStateException("x"));
        Assert.assertTrue(e instanceof StringRepresentationReplacementPlugin.ConcatCopyFailure);
        Assert.assertTrue(e.getMessage().contains("CONCAT_COPY M.m@3"));
        Assert.assertTrue(e.getCause() instanceof IllegalStateException);
        RuntimeException e2 = StringRepresentationReplacementPlugin.asConcatCopyFailure("M.m@3", new LinkageError("y"));
        Assert.assertTrue(e2 instanceof StringRepresentationReplacementPlugin.ConcatCopyFailure);
        Assert.assertSame(e, StringRepresentationReplacementPlugin.asConcatCopyFailure("M.m@4", e));
    }
}
