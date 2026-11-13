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

public class StringAnalysisPolicyTest {

    @Test
    public void internalClassPrefixes() {
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("java.lang.String"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("javax.swing.JFrame"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("jdk.internal.misc.Unsafe"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("sun.misc.Unsafe"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("com.sun.proxy.jdk.proxy1.$Proxy"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("org.ietf.jgss.GSSManager"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("org.w3c.dom.Node"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("org.xml.sax.Parser"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("org.graalvm.polyglot.Context"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("com.oracle.graal.pointsto.BigBang"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("com.oracle.svm.core.feature.Feature"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("com.oracle.truffle.api.CallTarget"));
        Assert.assertTrue(StringAnalysisPolicy.isInternalClass("com.oracle.javac.code.Symbol"));
    }

    @Test
    public void userCodeClasses() {
        Assert.assertTrue(StringAnalysisPolicy.isUserCodeClass("AccumulatorTest"));
        Assert.assertTrue(StringAnalysisPolicy.isUserCodeClass("StringViewTest"));
        Assert.assertTrue(StringAnalysisPolicy.isUserCodeClass("InterProcTest"));
        Assert.assertTrue(StringAnalysisPolicy.isUserCodeClass("com.mycompany.app.Main"));
        Assert.assertTrue(StringAnalysisPolicy.isUserCodeClass("org.myorg.util.Helper"));
    }

    @Test
    public void internalClassesAreNotUserCode() {
        Assert.assertFalse(StringAnalysisPolicy.isUserCodeClass("java.lang.String"));
        Assert.assertFalse(StringAnalysisPolicy.isUserCodeClass("com.oracle.svm.core.foo.Bar"));
    }

    @Test
    public void nullClassIsNotUserCode() {
        Assert.assertFalse(StringAnalysisPolicy.isUserCodeClass(null));
        Assert.assertFalse(StringAnalysisPolicy.isInternalClass(null));
    }

    @Test
    public void enclosingClassNameReflectsSetEnclosingClassName() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex v = graph.newVertex();
        v.setEnclosingClassName("TestUserClass");
        Assert.assertEquals("TestUserClass", StringAnalysisPolicy.enclosingClassName(v));
    }

    @Test
    public void enclosingClassNameNullWhenNotSet() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex v = graph.newVertex();
        Assert.assertNull(StringAnalysisPolicy.enclosingClassName(v));
    }
}
