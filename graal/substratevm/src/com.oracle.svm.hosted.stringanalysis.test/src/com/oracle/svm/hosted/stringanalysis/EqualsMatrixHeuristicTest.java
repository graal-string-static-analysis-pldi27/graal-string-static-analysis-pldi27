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

public class EqualsMatrixHeuristicTest {

    /** A candidate and one equals site; the candidate reaches it in the given roles. */
    private static final class Site {
        final StringUtilizationGraph graph;
        final SugVertex creationSite;
        final SugVertex equalsVertex;

        Site(String signature, boolean receiver, boolean argument) {
            this(signature, receiver, argument, SugNodeType.STRING_METHOD_CALL, "TestUserClass");
        }

        Site(String signature, boolean receiver, boolean argument, SugNodeType equalsType, String equalsEnclosingClass) {
            graph = new StringUtilizationGraph();
            creationSite = graph.newVertex();
            creationSite.setNodeType(SugNodeType.STRING_METHOD_CALL);
            creationSite.setMethodName("substring");
            creationSite.setDeclaringClass("java.lang.String");
            creationSite.setEnclosingClassName("TestUserClass");

            equalsVertex = graph.newVertex();
            equalsVertex.setNodeType(equalsType);
            equalsVertex.setMethodName("equals");
            equalsVertex.setMethodSignature(signature);
            equalsVertex.setDeclaringClass("java.lang.String");
            equalsVertex.setEnclosingClassName(equalsEnclosingClass);

            if (receiver) {
                graph.addEdge(creationSite, equalsVertex, SugEdgeType.QUALIFIER, -1);
            }
            if (argument) {
                graph.addEdge(creationSite, equalsVertex, SugEdgeType.PARAMETER, 1);
            }
            UsageSourceBuilder.build(graph);
        }

        List<InstrumentationDecision> apply(EqualsMatrixHeuristic h, boolean admitted) {
            Set<SugVertex> custom = new HashSet<>();
            if (admitted) {
                custom.add(creationSite);
            }
            return h.apply(graph, custom);
        }
    }

    private static final String OBJ = "Ljava/lang/Object;";

    @Test
    public void admittedRepAsTheArgumentRedirects() {
        Site g = new Site(OBJ, false, true);
        EqualsMatrixHeuristic heuristic = new EqualsMatrixHeuristic();
        List<InstrumentationDecision> decisions = g.apply(heuristic, true);
        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.EQUALS_MATRIX, decisions.get(0).getType());
        Assert.assertEquals(EqualsMatrixHeuristic.VARIANT_REDIRECT, decisions.get(0).getVariant());
        Assert.assertSame(g.equalsVertex, decisions.get(0).getCandidate());
        Assert.assertEquals(1, heuristic.getRedirectCount());
    }

    /** The receiver role needs no REDIRECT (the parent's devirtualized call dispatches to the rep's own equals). */
    @Test
    public void admittedRepAsTheReceiverOnlyIsFastPath() {
        Site g = new Site(OBJ, true, false);
        EqualsMatrixHeuristic heuristic = new EqualsMatrixHeuristic();
        Assert.assertTrue(g.apply(heuristic, true).isEmpty());
        Assert.assertEquals(1, heuristic.getFastPathCount());
    }

    /**
     * A JDK-internal {@code equals(Object)} site (a {@code JDK_LIBRARY_CALL} vertex, e.g.
     * {@code java.util.Objects#equals@11} or {@code String#contentEquals@52}) with an admitted rep as the argument
     * is redirected like a user site (the rule applies globally by design). Profile dumps are filtered to user classes,
     * so only this test pins it.
     */
    @Test
    public void jdkInternalSiteArgumentRedirects() {
        Site g = new Site(OBJ, false, true, SugNodeType.JDK_LIBRARY_CALL, "java.util.Objects");
        Assert.assertTrue(EqualsMatrixHeuristic.isEqualsObjectCall(g.equalsVertex));
        EqualsMatrixHeuristic heuristic = new EqualsMatrixHeuristic();
        List<InstrumentationDecision> decisions = g.apply(heuristic, true);
        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(EqualsMatrixHeuristic.VARIANT_REDIRECT, decisions.get(0).getVariant());
        Assert.assertSame(g.equalsVertex, decisions.get(0).getCandidate());
        Assert.assertEquals(1, heuristic.getRedirectCount());
        // the receiver role at the same JDK-internal site needs none
        Assert.assertTrue(new Site(OBJ, true, false, SugNodeType.JDK_LIBRARY_CALL, "java.util.Objects").apply(new EqualsMatrixHeuristic(), true).isEmpty());
    }

    @Test
    public void bothRolesRedirectForTheArgument() {
        Site g = new Site(OBJ, true, true);
        Assert.assertEquals(1, g.apply(new EqualsMatrixHeuristic(), true).size());
    }

    @Test
    public void notAdmittedArgumentIsFastPath() {
        Site g = new Site(OBJ, false, true);
        EqualsMatrixHeuristic heuristic = new EqualsMatrixHeuristic();
        Assert.assertTrue(g.apply(heuristic, false).isEmpty());
        Assert.assertEquals(0, heuristic.getRedirectCount());
        Assert.assertEquals(1, heuristic.getFastPathCount());
    }

    /** Phase A's static {@code Objects.equals} call vertex (signature {@code (Ljava/lang/Object;)}) is not rewritable. */
    @Test
    public void nonEqualsObjectVertexIsFastPath() {
        Site g = new Site("(Ljava/lang/Object;)", false, true);
        Assert.assertFalse(EqualsMatrixHeuristic.isEqualsObjectCall(g.equalsVertex));
        Assert.assertTrue(g.apply(new EqualsMatrixHeuristic(), true).isEmpty());
        Assert.assertTrue(EqualsMatrixHeuristic.isEqualsObjectCall(new Site(OBJ, false, false).equalsVertex));
    }

    @Test
    public void redirectsForPure() {
        Assert.assertTrue(EqualsMatrixHeuristic.redirectsFor(UsageRole.PARAMETER, 1));
        Assert.assertFalse("the receiver role", EqualsMatrixHeuristic.redirectsFor(UsageRole.RECEIVER, -1));
        Assert.assertFalse("slot 0 is not the argument", EqualsMatrixHeuristic.redirectsFor(UsageRole.PARAMETER, 0));
        Assert.assertFalse(EqualsMatrixHeuristic.redirectsFor(UsageRole.NONE, -1));
    }
}
