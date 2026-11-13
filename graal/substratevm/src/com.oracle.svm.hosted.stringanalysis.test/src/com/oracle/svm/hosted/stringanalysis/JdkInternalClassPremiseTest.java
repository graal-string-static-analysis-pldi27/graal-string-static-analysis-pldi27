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

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.core.stringrep.ThreeWayString;

/**
 * Premise pins of the heuristics' "JDK-internal" classification boundary ({@code StringAnalysisPolicy.isInternalClass})
 * applied to the enclosing method of a site, pinned over representative populations: the JDK concat machinery and {@code StringJoiner}, the benchmark/user
 * side (lucene, the dacapo harness, the json-parser, the probe classes), and, as documentation, our own
 * representation classes and the hosted SVM classes, which classify internal (they carry no {@code INLINE_CACHE}
 * entries: the child's universe never contains them).
 */
public class JdkInternalClassPremiseTest {

    @Test
    public void jdkInternalBoundaryIsTheAnalysisSideBoundary() {
        // the concat-machinery / StringJoiner enclosing bodies
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("java.lang.StringConcatHelper"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("java.lang.StringJoiner"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("java.util.HashMap"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("java.lang.AbstractStringBuilder"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("java.lang.String"));
        // the other internal prefixes of the policy table
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("javax.swing.Icon"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("jdk.internal.misc.Unsafe"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("sun.nio.cs.UTF_8"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("org.graalvm.word.WordBase"));
        // the benchmark/user side
        Assert.assertFalse(StringAnalysisPolicy.isInternalClass("org.apache.lucene.index.IndexFileNames"));
        Assert.assertFalse("the dacapo harness is user code for the policy",
                        StringAnalysisPolicy.isInternalClass("org.dacapo.harness.Benchmark"));
        Assert.assertFalse("the json-parser is user code (isDigit's 10 REDIRECT sites keep the zero-indirect lowering)",
                        StringAnalysisPolicy.isInternalClass("json.JsonPureStringParser"));
        Assert.assertFalse(StringAnalysisPolicy.isInternalClass("C94Avjdk"));
        Assert.assertFalse(StringAnalysisPolicy.isInternalClass("json.Foo"));
        Assert.assertFalse("null is never internal (isUserCodeClass(null) is false too)",
                        StringAnalysisPolicy.isInternalClass(null));
        Assert.assertFalse(StringAnalysisPolicy.isUserCodeClass(null));
        Assert.assertTrue(StringAnalysisPolicy.isUserCodeClass("org.dacapo.harness.Benchmark"));
        // documentation pin: our own representation classes and the hosted SVM classes classify internal: they
        // carry no INLINE_CACHE entries (the child's universe never contains them), so the gate never fires there
        for (Class<?> rep : new Class<?>[]{StringView.class, SingleByteString.class, RopeString.class,
                        ThreeWayString.class, FixedConcat4.class, ArrayLazyString.class, InterleavedStringArray.class}) {
            Assert.assertTrue(rep.getName() + " is internal for the policy", StringAnalysisPolicy.isInternalClass(rep.getName()));
        }
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass(InlineCacheTrivialMethodNodePlugin.class.getName()));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass(StringAnalysisPolicy.class.getName()));
    }

    /**
     * The knob's gate consumes the enclosing method of the parse ({@code b.getMethod()}'s declaring class) — the
     * same method that keys the profile lookup ({@code SiteKeys.profileKey(b.getMethod(), b.bci())}) — so the
     * classification the plugins apply is per the profile's own site key, never the invoke's target class. Pinned
     * by construction here: the profile key of a JDK body site is the JDK class#method, and the policy classifies
     * that class; a divergence between the two spellings would silently move the gate's population.
     */
    @Test
    public void enclosingMethodKeyMatchesThePolicyClassification() {
        Assert.assertEquals("java.util.StringJoiner#add(Ljava/lang/CharSequence;)Ljava/util/StringJoiner;@82",
                        SiteKeys.profileKey(stringJoinerAdd(), 82));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass(
                        enclosingName(stringJoinerAdd())));
    }

    private static jdk.vm.ci.meta.ResolvedJavaMethod stringJoinerAdd() {
        try {
            return jdk.vm.ci.hotspot.HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess()
                            .lookupJavaMethod(java.util.StringJoiner.class.getDeclaredMethod("add", CharSequence.class));
        } catch (NoSuchMethodException e) {
            throw new RuntimeException(e);
        }
    }

    private static String enclosingName(jdk.vm.ci.meta.ResolvedJavaMethod m) {
        return m.getDeclaringClass().toJavaName();
    }
}
