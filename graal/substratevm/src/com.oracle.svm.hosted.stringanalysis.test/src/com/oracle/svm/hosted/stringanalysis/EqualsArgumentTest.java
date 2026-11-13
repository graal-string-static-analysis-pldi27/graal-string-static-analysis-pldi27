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

import java.util.List;
import java.util.Objects;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;

import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Equals-argument pins: the equals-argument terminal keys on the resolved target {@code String.equals(Object)}, never
 * on the name (keying on the name {@code equals(Object)} makes a false
 * ADMIT; this test's user-override rows catch it); the no-site refusal; the knob defaults. The argument-only redirect
 * and the conflict rule have their pure pins in {@code EqualsMatrixHeuristicTest} and {@code CrossRepConflictTest}.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.meta"})
public class EqualsArgumentTest {

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    /** A user class with its own {@code equals(Object)} override (the attack shape: a user equals is entered). */
    static final class Box {
        final String s;

        Box(String s) {
            this.s = s;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof String t && t.replace('a', 'b').equals(s);
        }

        @Override
        public int hashCode() {
            return 0;
        }

        /** An overload named equals with another signature. */
        boolean equals(String o) {
            return s.equals(o);
        }
    }

    private ResolvedJavaMethod method(Class<?> c, String name, Class<?>... params) throws NoSuchMethodException {
        return metaAccess.lookupJavaMethod(c.getDeclaredMethod(name, params));
    }

    /** (a): the resolved target String.equals(Object) only; a user override, Object.equals, overloads and statics are not. */
    @Test
    public void resolvedTargetIsStringEquals() throws NoSuchMethodException {
        Assert.assertTrue(StringAtoms.isStringEquals(method(String.class, "equals", Object.class)));
        Assert.assertFalse("a user equals(Object) override is entered", StringAtoms.isStringEquals(method(Box.class, "equals", Object.class)));
        Assert.assertFalse("Object.equals", StringAtoms.isStringEquals(method(Object.class, "equals", Object.class)));
        Assert.assertFalse("an equals overload", StringAtoms.isStringEquals(method(Box.class, "equals", String.class)));
        Assert.assertFalse("the static Objects.equals", StringAtoms.isStringEquals(method(Objects.class, "equals", Object.class, Object.class)));
        Assert.assertFalse(StringAtoms.isStringEquals(method(String.class, "equalsIgnoreCase", String.class)));
        Assert.assertFalse("contentEquals is covered through its body's this.equals(cs), not as a terminal",
                        StringAtoms.isStringEquals(method(String.class, "contentEquals", CharSequence.class)));
        Assert.assertFalse(StringAtoms.isStringEquals((ResolvedJavaMethod) null));
    }

    /** The equals-argument tag is terminal evidence (PDP(b)) only at slot 1 of an equals(Object) vertex. */
    @Test
    public void terminalEqualsArgumentTag() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex eq = graph.newVertex();
        eq.setNodeType(SugNodeType.STRING_METHOD_CALL);
        eq.setMethodName("equals");
        eq.setMethodSignature("Ljava/lang/Object;");
        Assert.assertTrue(AdmissionProof.isTerminalEqualsArgument(new UsageTag(eq, UsageRole.PARAMETER, 1)));
        Assert.assertFalse(AdmissionProof.isTerminalEqualsArgument(new UsageTag(eq, UsageRole.PARAMETER, 0)));
        eq.setMethodSignature("(Ljava/lang/Object;)");
        Assert.assertFalse("the static Objects.equals vertex", AdmissionProof.isTerminalEqualsArgument(new UsageTag(eq, UsageRole.PARAMETER, 1)));
    }

    @Test
    public void resolvedTargetIsStringEqualsPure() {
        Assert.assertTrue(StringAtoms.isStringEquals(false, "java.lang.String", "equals", "(Ljava/lang/Object;)Z"));
        Assert.assertFalse(StringAtoms.isStringEquals(false, "C92EqArgMixedRecvLeak$Box", "equals", "(Ljava/lang/Object;)Z"));
        Assert.assertFalse(StringAtoms.isStringEquals(true, "java.lang.String", "equals", "(Ljava/lang/Object;)Z"));
        Assert.assertFalse(StringAtoms.isStringEquals(false, "java.lang.String", "equals", "(Ljava/lang/String;)Z"));
    }

    /** The slot row: slot 1 of String.equals is the terminal at a Phase-A site and refused by name without one. */
    @Test
    public void equalsArgRow() {
        Assert.assertEquals(StringAtoms.EqArgRow.TERMINAL, StringAtoms.equalsArgRow(true, 1, true, true));
        Assert.assertEquals("no Phase-A site: refused by name, never entered", StringAtoms.EqArgRow.NO_SITE, StringAtoms.equalsArgRow(true, 1, true, false));
        // the reflection bridge (RecursiveTracking.bridgedInvokeUsage) passes hasPhaseASite = false (a reflective call
        // never has a Phase-A equals site), and an inlined-scope invoke does the same: NO_SITE
        Assert.assertEquals("the reflection bridge / an inlined-scope invoke", StringAtoms.EqArgRow.NO_SITE, StringAtoms.equalsArgRow(true, 1, true, false));
        Assert.assertEquals("the receiver slot", StringAtoms.EqArgRow.NONE, StringAtoms.equalsArgRow(true, 0, true, true));
        Assert.assertEquals("another target (a user override)", StringAtoms.EqArgRow.NONE, StringAtoms.equalsArgRow(true, 1, false, true));
        Assert.assertEquals("a container atom", StringAtoms.EqArgRow.NONE, StringAtoms.equalsArgRow(false, 1, true, true));
    }

    /** The no-site refusal: a new non-budget name appended last. */
    @Test
    public void noSiteRefusal() {
        RTrackRefusal[] all = RTrackRefusal.values();
        // after it: LITERAL_IDENTITY (the SB literal seed), CLASS_ESCAPE, HOLDER_END_UNEXPLAINED,
        // COMPARETO_ARG_NO_SITE (compareTo mirror), HIDDEN_SINK, MIRROR_ARG_NO_SITE (builder-append mirror)
        Assert.assertEquals(RTrackRefusal.EQUALS_ARG_NO_SITE, all[all.length - 7]);
        Assert.assertEquals(RTrackRefusal.LITERAL_IDENTITY, all[all.length - 6]);
        Assert.assertEquals(RTrackRefusal.CLASS_ESCAPE, all[all.length - 5]);
        Assert.assertEquals(RTrackRefusal.HOLDER_END_UNEXPLAINED, all[all.length - 4]);
        Assert.assertEquals(RTrackRefusal.COMPARETO_ARG_NO_SITE, all[all.length - 3]);
        Assert.assertEquals(RTrackRefusal.HIDDEN_SINK, all[all.length - 2]);
        Assert.assertEquals(RTrackRefusal.MIRROR_ARG_NO_SITE, all[all.length - 1]);
        Assert.assertFalse(RTrackRefusal.EQUALS_ARG_NO_SITE.budgetClass);
        Assert.assertEquals(TransferFacts.IncompleteReason.UNTRACKABLE_CONTAINER, RTrackRefusal.EQUALS_ARG_NO_SITE.verdictReason());
    }

    /**
     * The equals argument is an ordinary usage for the no-usage detector. The same candidate with no
     * usage at all is admitted with the detector's warning; with the equals-argument usage it is admitted without a warning (the terminal argument is
     * terminal evidence, as a safe-sink argument).
     */
    @Test
    public void equalsArgumentUsageShowsNoNoUsageWarning() {
        for (boolean withEqualsArgument : new boolean[]{false, true}) {
            StringUtilizationGraph graph = new StringUtilizationGraph();
            SugVertex sub = graph.newVertex();
            sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
            sub.setMethodName("substring");
            sub.setMethodSignature("I,I");
            sub.setDeclaringClass("java.lang.String");
            sub.setSourceLocation("S.java:1");
            sub.setEnclosingClassName("TestUserClass");
            if (withEqualsArgument) {
                SugVertex eq = graph.newVertex();
                eq.setNodeType(SugNodeType.STRING_METHOD_CALL);
                eq.setMethodName("equals");
                eq.setMethodSignature("Ljava/lang/Object;");
                eq.setDeclaringClass("java.lang.String");
                eq.setSourceLocation("S.java:2");
                graph.addEdge(sub, eq, SugEdgeType.PARAMETER, 1);
            }
            StringViewHeuristic sv = new StringViewHeuristic();
            List<InstrumentationDecision> decisions = sv.apply(graph);
            // both ADMIT; only the no-usage twin carries the warning
            Assert.assertEquals(1, decisions.size());
            Assert.assertEquals(0, sv.getRejections().size());
            Assert.assertEquals(withEqualsArgument ? 0 : 1, sv.getWarnings().size());
            Assert.assertEquals(!withEqualsArgument, AdmissionProof.hasNoUsage(sub));
        }
    }
}
