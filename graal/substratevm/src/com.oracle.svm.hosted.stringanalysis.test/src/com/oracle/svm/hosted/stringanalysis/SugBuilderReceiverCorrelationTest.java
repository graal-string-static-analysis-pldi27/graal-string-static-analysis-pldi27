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

public class SugBuilderReceiverCorrelationTest {

    private static SugVertex newAccumulator(StringUtilizationGraph graph, String loc, String sourceKey) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.NEW_ACCUMULATOR);
        v.setDeclaringClass("java.lang.StringBuilder");
        v.setSourceLocation(loc);
        v.setSourceKey(sourceKey);
        return v;
    }

    @Test
    public void sameLineAccumulatorsDisambiguatedBySourceKey() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc1 = newAccumulator(graph, "A.java:1", "pkg.Cls#<init>()V@5");
        SugVertex acc2 = newAccumulator(graph, "A.java:1", "pkg.Cls#<init>()V@7");

        SugVertex r1 = ReceiverCorrelation.correlateReceiverByKey(graph, "pkg.Cls#<init>()V@5", "A.java:1", null);
        SugVertex r2 = ReceiverCorrelation.correlateReceiverByKey(graph, "pkg.Cls#<init>()V@7", "A.java:1", null);

        Assert.assertSame(acc1, r1);
        Assert.assertSame(acc2, r2);
    }

    @Test
    public void ambiguousFileLineWithoutSourceKeyReturnsNull() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc1 = newAccumulator(graph, "A.java:1", null);
        SugVertex acc2 = newAccumulator(graph, "A.java:1", null);

        SugVertex r = ReceiverCorrelation.correlateReceiverByKey(graph, null, "A.java:1", null);

        Assert.assertNull(r);
        Assert.assertNotSame(acc1, r);
        Assert.assertNotSame(acc2, r);
    }

    @Test
    public void inlinedCallerReceiverCorrelatedBySourceKey() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex allocator = newAccumulator(graph, "Caller.java:9", "pkg.Caller#<init>()V@12");

        SugVertex byKey = ReceiverCorrelation.correlateReceiverByKey(graph, "pkg.Caller#<init>()V@12", "Inlinee.java:24", null);
        Assert.assertSame(allocator, byKey);

        SugVertex byFileLineOnly = ReceiverCorrelation.correlateReceiverByKey(graph, null, "Inlinee.java:24", null);
        Assert.assertNull(byFileLineOnly);
    }

    @Test
    public void sourceKeyAbsentFallsBackToFileLine() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph, "A.java:1", null);

        SugVertex r = ReceiverCorrelation.correlateReceiverByKey(graph, null, "A.java:1", null);

        Assert.assertSame(acc, r);
    }

    @Test
    public void noMatchReturnsNull() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        newAccumulator(graph, "A.java:1", "pkg.Cls#<init>()V@5");

        SugVertex r = ReceiverCorrelation.correlateReceiverByKey(graph, "pkg.Cls#<init>()V@99", "B.java:9", null);

        Assert.assertNull(r);
    }
}
