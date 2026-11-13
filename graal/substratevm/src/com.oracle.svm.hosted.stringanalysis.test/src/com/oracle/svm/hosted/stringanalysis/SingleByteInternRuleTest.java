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

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

/**
 * {@code intern()} is a rejecting use for a SINGLE_BYTE candidate
 * ({@link SingleByteHeuristic#reachesIntern}): directly, or through a usage site's own usages.
 */
public class SingleByteInternRuleTest {

    private final StringUtilizationGraph g = new StringUtilizationGraph();
    private final List<UsageTag> tags = new ArrayList<>();

    private SugVertex vertex(SugNodeType type, String method) {
        SugVertex v = g.newVertex();
        v.setNodeType(type);
        v.setMethodName(method);
        v.setUsageTags(new BitSet());
        return v;
    }

    private void use(SugVertex source, SugVertex site, UsageRole role) {
        tags.add(new UsageTag(site, role, role == UsageRole.PARAMETER ? 0 : -1));
        source.getUsageTags().set(tags.size() - 1);
        g.setUsageTags(tags);
    }

    @Test
    public void aDirectInternRejects() {
        SugVertex c = vertex(SugNodeType.STRING_METHOD_CALL, "substring");
        use(c, vertex(SugNodeType.STRING_METHOD_CALL, "intern"), UsageRole.RECEIVER);
        Assert.assertTrue(SingleByteHeuristic.reachesIntern(g, c));
    }

    @Test
    public void svmsInternSupportCallRejects() {
        SugVertex c = vertex(SugNodeType.STRING_METHOD_CALL, "substring");
        use(c, vertex(SugNodeType.JDK_LIBRARY_CALL, "intern"), UsageRole.PARAMETER);
        Assert.assertTrue(SingleByteHeuristic.reachesIntern(g, c));
    }

    @Test
    public void anInternDownstreamOfAUseRejects() {
        SugVertex c = vertex(SugNodeType.STRING_METHOD_CALL, "substring");
        SugVertex ts = vertex(SugNodeType.STRING_METHOD_CALL, "toString");
        use(c, ts, UsageRole.RECEIVER);
        use(ts, vertex(SugNodeType.STRING_METHOD_CALL, "intern"), UsageRole.RECEIVER);
        Assert.assertTrue(SingleByteHeuristic.reachesIntern(g, c));
    }

    @Test
    public void noInternNoRejectionAndCyclesTerminate() {
        SugVertex c = vertex(SugNodeType.STRING_METHOD_CALL, "substring");
        SugVertex eq = vertex(SugNodeType.STRING_METHOD_CALL, "equals");
        use(c, eq, UsageRole.RECEIVER);
        use(eq, c, UsageRole.RECEIVER); // a cycle
        use(c, vertex(SugNodeType.JDK_LIBRARY_CALL, "println"), UsageRole.PARAMETER);
        Assert.assertFalse(SingleByteHeuristic.reachesIntern(g, c));
        Assert.assertFalse(SingleByteHeuristic.isInternCall(vertex(SugNodeType.STRING_LITERAL, "intern")));
    }
}
