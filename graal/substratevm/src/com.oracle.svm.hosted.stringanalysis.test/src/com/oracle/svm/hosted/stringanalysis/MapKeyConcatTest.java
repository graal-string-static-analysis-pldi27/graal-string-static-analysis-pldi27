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

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Pins: (1) the String map keys rule: the compareTo-argument terminal keys on the
 * resolved target {@code String.compareTo(String)} / its bridge {@code compareTo(Object)}, never on the name; its usage is
 * terminal evidence; the lazy whitelist's receiver rule; the F2 tree-bin data (the representation-insensitive class
 * checks and the same-class callback are real sites of the table, and exactly the pinned ones); (2) the concat
 * rule: the {@code StringConcatFactory} copy test mirrors {@code makeSimpleConcat} (JDK 25), and a String View
 * operand is a supported usage only at a non-copying site.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.meta"})
public class MapKeyConcatTest {

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    /** A user Comparable whose compareTo(Object) bridge and compareTo(Key) are entered, never terminal. */
    static final class Key implements Comparable<Key> {
        @Override
        public int compareTo(Key o) {
            return 0;
        }
    }

    private ResolvedJavaMethod method(Class<?> c, String name, Class<?>... params) throws NoSuchMethodException {
        return metaAccess.lookupJavaMethod(c.getDeclaredMethod(name, params));
    }

    @Test
    public void resolvedTargetIsStringCompareTo() throws NoSuchMethodException {
        Assert.assertTrue(StringAtoms.isStringCompareTo(method(String.class, "compareTo", String.class)));
        Assert.assertTrue("the Comparable bridge", StringAtoms.isStringCompareTo(method(String.class, "compareTo", Object.class)));
        Assert.assertFalse(StringAtoms.isStringCompareTo(method(String.class, "compareToIgnoreCase", String.class)));
        Assert.assertFalse(StringAtoms.isStringCompareTo(method(Key.class, "compareTo", Key.class)));
        Assert.assertFalse(StringAtoms.isStringCompareTo(method(Key.class, "compareTo", Object.class)));
        Assert.assertFalse(StringAtoms.isStringCompareTo(method(Integer.class, "compareTo", Integer.class)));
        Assert.assertFalse(StringAtoms.isStringCompareTo(method(String.class, "equals", Object.class)));
        Assert.assertFalse(StringAtoms.isStringCompareTo((ResolvedJavaMethod) null));
    }

    @Test
    public void resolvedTargetIsStringCompareToPure() {
        Assert.assertTrue(StringAtoms.isStringCompareTo(false, "java.lang.String", "compareTo", "(Ljava/lang/String;)I"));
        Assert.assertTrue(StringAtoms.isStringCompareTo(false, "java.lang.String", "compareTo", "(Ljava/lang/Object;)I"));
        Assert.assertFalse(StringAtoms.isStringCompareTo(true, "java.lang.String", "compareTo", "(Ljava/lang/String;)I"));
        Assert.assertFalse(StringAtoms.isStringCompareTo(false, "java.lang.Comparable", "compareTo", "(Ljava/lang/Object;)I"));
        Assert.assertFalse(StringAtoms.isStringCompareTo(false, "java.lang.String", "compareTo", "(Ljava/lang/String;)Z"));
    }

    @Test
    public void compareToArgumentSlotRow() {
        // the compareTo-argument terminal is site-keyed (StringAtoms.compareToArgRow; the full table in CompareToMirrorTest)
        Assert.assertEquals(StringAtoms.CmpArgRow.TERMINAL, StringAtoms.compareToArgRow(true, 1, true, false, true));
        Assert.assertEquals("the receiver slot", StringAtoms.CmpArgRow.NONE, StringAtoms.compareToArgRow(true, 0, true, false, true));
        Assert.assertEquals("a container atom", StringAtoms.CmpArgRow.NONE, StringAtoms.compareToArgRow(false, 1, true, false, true));
        Assert.assertEquals("another target", StringAtoms.CmpArgRow.NONE, StringAtoms.compareToArgRow(true, 1, false, false, true));
    }

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

    private static SugVertex call(StringUtilizationGraph graph, String name, String sig, String loc) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName(name);
        v.setMethodSignature(sig);
        v.setDeclaringClass("java.lang.String");
        v.setSourceLocation(loc);
        return v;
    }

    /** The compareTo argument (slot 1, both signatures) is a usage and terminal evidence: ADMIT, no warning. */
    @Test
    public void compareToArgumentIsTerminalEvidence() {
        for (String sig : new String[]{"Ljava/lang/String;", "Ljava/lang/Object;"}) {
            StringUtilizationGraph graph = new StringUtilizationGraph();
            SugVertex sub = substringCandidate(graph, "S.java:1");
            SugVertex cmp = call(graph, "compareTo", sig, "S.java:2");
            graph.addEdge(sub, cmp, SugEdgeType.PARAMETER, 1);
            StringViewHeuristic heuristic = new StringViewHeuristic();
            List<InstrumentationDecision> decisions = heuristic.apply(graph);
            Assert.assertEquals(sig, 1, decisions.size());
            Assert.assertTrue(heuristic.getWarnings().isEmpty());
        }
    }

    /** Slot 0 as a PARAMETER tag, compareToIgnoreCase, or another signature: no terminal evidence. */
    @Test
    public void onlySlot1OfStringCompareToIsTheTerminalArgument() {
        for (String[] c : new String[][]{{"compareTo", "Ljava/lang/String;", "0"}, {"compareToIgnoreCase", "Ljava/lang/String;", "1"}, {"compareTo", "I", "1"}}) {
            StringUtilizationGraph graph = new StringUtilizationGraph();
            SugVertex sub = substringCandidate(graph, "S.java:1");
            SugVertex site = call(graph, c[0], c[1], "S.java:2");
            graph.addEdge(sub, site, SugEdgeType.PARAMETER, Integer.parseInt(c[2]));
            StringViewHeuristic heuristic = new StringViewHeuristic();
            // a non-terminal PARAMETER usage still ADMITs (a usage: no warning) but carries NO
            // positive downstream proof — the compareTo-argument distinction holds at the predicate level.
            Assert.assertEquals(String.join(" ", c), 1, heuristic.apply(graph).size());
            Assert.assertTrue(String.join(" ", c), heuristic.getWarnings().isEmpty());
            Assert.assertFalse(String.join(" ", c), AdmissionProof.hasPositiveDownstreamProof(graph, sub));
        }
    }

    /** K (2): the receiver role of compareTo in the lazy whitelist, for every variant (StringView had it already). */
    @Test
    public void lazyWhitelistHasCompareToReceiver() {
        for (String variant : new String[]{"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED"}) {
            Assert.assertTrue(variant, LazyConcatWhitelist.isWhitelisted("compareTo", "java.lang.String", "Ljava/lang/String;", variant));
            Assert.assertTrue(variant, LazyConcatWhitelist.isWhitelisted("compareTo", "java.lang.String", "Ljava/lang/Object;", variant));
            Assert.assertFalse(variant, LazyConcatWhitelist.isWhitelisted("compareToIgnoreCase", "java.lang.String", "Ljava/lang/String;", variant));
        }
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("compareTo", "java.lang.String", "Ljava/lang/String;"));
        Assert.assertTrue(StringViewWhitelist.isWhitelistedUsage("compareTo", "java.lang.String", "Ljava/lang/Object;"));
    }

    /** The F2 tree-bin data are real sites of the F2 table: class-check sites and a callback site, and exactly the pinned ones. */
    @Test
    public void treeBinSitesAreRealTableSites() {
        Set<String> classChecks = new HashSet<>();
        Set<String> compareCallbacks = new HashSet<>();
        for (JdkModels.Op op : JdkModels.F2.table.values()) {
            for (JdkModels.Effect e : op.effects()) {
                if (e instanceof JdkModels.ClassCheck cc) {
                    classChecks.addAll(cc.sites());
                } else if (e instanceof JdkModels.Callback cb && cb.cb().startsWith("java.lang.Comparable#compareTo")) {
                    compareCallbacks.addAll(cb.sites());
                }
            }
        }
        Assert.assertEquals(Set.of("java.util.HashMap#comparableClassFor(Ljava/lang/Object;)Ljava/lang/Class;@8",
                        "java.util.HashMap#compareComparables(Ljava/lang/Class;Ljava/lang/Object;Ljava/lang/Object;)I@5",
                        "java.util.HashMap$TreeNode#tieBreakOrder(Ljava/lang/Object;Ljava/lang/Object;)I@9",
                        "java.util.HashMap$TreeNode#tieBreakOrder(Ljava/lang/Object;Ljava/lang/Object;)I@16"), JdkModels.F2.repInsensitiveClassChecks);
        Assert.assertTrue("every rep-insensitive site is a class check of the table", classChecks.containsAll(JdkModels.F2.repInsensitiveClassChecks));
        Assert.assertEquals("every class check of F2 is a tree-bin one", classChecks, JdkModels.F2.repInsensitiveClassChecks);
        Assert.assertEquals(Set.of("java.util.HashMap#compareComparables(Ljava/lang/Class;Ljava/lang/Object;Ljava/lang/Object;)I@21"), JdkModels.F2.sameClassCallbacks);
        Assert.assertTrue("the same-class site is a compareTo callback of the table", compareCallbacks.containsAll(JdkModels.F2.sameClassCallbacks));
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            if (f != JdkModels.F2) {
                Assert.assertTrue(f.id, f.repInsensitiveClassChecks.isEmpty() && f.sameClassCallbacks.isEmpty());
            }
        }
    }

    private static boolean copies(String boot, String recipe, boolean... primitive) {
        return StringAtoms.scfCopiesOperand(boot, recipe, primitive);
    }

    /** K task 2: the copy test against StringConcatFactory.makeSimpleConcat (the K probes ran each row on the JVM and the image). */
    @Test
    public void scfCopyTestMirrorsMakeSimpleConcat() {
        String w = "makeConcatWithConstants";
        Assert.assertTrue("\"\" + v: newStringOf", copies(w, "\u0001", false));
        Assert.assertTrue("a + b: simpleConcat", copies(w, "\u0001\u0001", false, false));
        Assert.assertTrue("makeConcat, one reference", copies("makeConcat", null, false));
        Assert.assertTrue("makeConcat, two references", copies("makeConcat", null, false, false));
        Assert.assertFalse("makeConcat, three references: the hidden class", copies("makeConcat", null, false, false, false));
        Assert.assertFalse("v + \"!\": simpleConcat with a non-empty constant", copies(w, "\u0001!", false));
        Assert.assertFalse("\"<\" + v", copies(w, "<\u0001", false));
        Assert.assertFalse("\"<\" + v + \">\": the hidden class", copies(w, "<\u0001>", false));
        Assert.assertFalse("a + \"-\" + b", copies(w, "\u0001-\u0001", false, false));
        Assert.assertFalse("v + i: a primitive operand", copies(w, "\u0001\u0001", false, true));
        Assert.assertFalse("\"\" + i: one primitive", copies(w, "\u0001", true));
        Assert.assertFalse("a + b + c", copies(w, "\u0001\u0001\u0001", false, false, false));
        Assert.assertTrue("a \\2 constant: conservative", copies(w, "\u0002\u0001", false));
        Assert.assertTrue("a malformed recipe: conservative", copies(w, "\u0001", false, false));
        Assert.assertTrue("no recipe: conservative", copies(w, null, false));
        Assert.assertTrue("another bootstrap: conservative", copies("other", "<\u0001>", false));
    }

    private static SugVertex concat(StringUtilizationGraph graph, String loc, boolean noCopy) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        v.setMethodName("makeConcatWithConstants");
        v.setSourceLocation(loc);
        if (noCopy) {
            v.markScfNoCopy();
        }
        return v;
    }

    /** K task 2: a String View operand of a non-copying concat is a supported usage; of a copying (or unmarked) one it rejects. */
    @Test
    public void stringViewConcatOperandOnlyAtANonCopyingSite() {
        for (boolean noCopy : new boolean[]{true, false}) {
            StringUtilizationGraph graph = new StringUtilizationGraph();
            SugVertex sub = substringCandidate(graph, "S.java:1");
            SugVertex c = concat(graph, "S.java:2", noCopy);
            graph.addEdge(sub, c, SugEdgeType.CONCAT_LEFT, -1);
            StringViewHeuristic heuristic = new StringViewHeuristic();
            List<InstrumentationDecision> decisions = heuristic.apply(graph);
            if (noCopy) {
                Assert.assertEquals(1, decisions.size());
                Assert.assertEquals(Set.of("S.java:2"), StringViewHeuristic.concatOperandSites(graph, sub));
            } else {
                Assert.assertTrue(decisions.isEmpty());
                Assert.assertTrue(heuristic.getRejections().get(0).contains("concat expression @ S.java:2"));
                Assert.assertTrue(StringViewHeuristic.concatOperandSites(graph, sub).isEmpty());
            }
        }
    }
}
