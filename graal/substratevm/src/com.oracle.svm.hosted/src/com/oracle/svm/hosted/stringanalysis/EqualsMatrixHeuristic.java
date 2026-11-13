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
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class EqualsMatrixHeuristic implements Heuristic {

    public static final String VARIANT_REDIRECT = "REDIRECT";
    public static final String VARIANT_FAST_PATH = "FAST_PATH";

    private final List<String> rejections = new ArrayList<>();
    private int redirectCount;
    private int fastPathCount;

    public EqualsMatrixHeuristic() {
    }

    @Override
    public List<InstrumentationDecision> apply(StringUtilizationGraph graph) {
        return apply(graph, Collections.emptySet());
    }

    public List<InstrumentationDecision> apply(StringUtilizationGraph graph, Set<SugVertex> customRepCandidates) {
        rejections.clear();
        redirectCount = 0;
        fastPathCount = 0;
        List<InstrumentationDecision> decisions = new ArrayList<>();
        for (SugVertex v : graph.getVertices()) {
            if (!isEqualsVertex(v) && !isCompareToStringCall(v)) {
                continue;
            }
            String variant = classify(graph, v, customRepCandidates);
            if (VARIANT_REDIRECT.equals(variant)) {
                redirectCount++;
                decisions.add(new InstrumentationDecision(v, OptimizationType.EQUALS_MATRIX, VARIANT_REDIRECT));
            } else {
                fastPathCount++;
            }
        }
        return decisions;
    }

    public List<String> getRejections() {
        return rejections;
    }

    public int getRedirectCount() {
        return redirectCount;
    }

    public int getFastPathCount() {
        return fastPathCount;
    }

    public Map<String, Integer> variantCounts() {
        Map<String, Integer> counts = new LinkedHashMap<>();
        counts.put(VARIANT_REDIRECT, redirectCount);
        counts.put(VARIANT_FAST_PATH, fastPathCount);
        return counts;
    }

    /** A String or JDK-library call vertex of a method named {@code equals} (any signature). */
    static boolean isEqualsVertex(SugVertex v) {
        SugNodeType t = v.getNodeType();
        if (t != SugNodeType.STRING_METHOD_CALL && t != SugNodeType.JDK_LIBRARY_CALL) {
            return false;
        }
        return "equals".equals(v.getMethodName());
    }

    /**
     * An {@code equals(Object)} call vertex, the site the parent can REDIRECT (the builder names String and Object
     * {@code equals} sites {@code java.lang.String.equals} with signature {@code Ljava/lang/Object;}; the static
     * {@code Objects.equals} vertex carries {@code (Ljava/lang/Object;)} and is not one).
     */
    static boolean isEqualsObjectCall(SugVertex v) {
        return isEqualsVertex(v) && "Ljava/lang/Object;".equals(v.getMethodSignature());
    }

    /**
     * compareTo mirror: a String-declared {@code compareTo(String)} call vertex: a user site or the bridge
     * {@code String#compareTo(Object)}'s internal call, the one image-wide site every generic {@code Comparable} caller
     * funnels into. The parent replaces a REDIRECTed one by {@code String.maybeCustomStringCompareTo} (profile type
     * {@code EQUALS_MATRIX REDIRECT}; the parent dispatches on the invoke's name).
     */
    static boolean isCompareToStringCall(SugVertex v) {
        SugNodeType t = v.getNodeType();
        if (t != SugNodeType.STRING_METHOD_CALL && t != SugNodeType.JDK_LIBRARY_CALL) {
            return false;
        }
        return "compareTo".equals(v.getMethodName()) && "java.lang.String".equals(v.getDeclaringClass()) && "Ljava/lang/String;".equals(v.getMethodSignature());
    }

    /**
     * Pure (JUnit): the child grants the equals / compareTo(String) argument terminal (a PARAMETER usage instead of
     * entering the stock body) only at a vertex this heuristic will REDIRECT when an admitted rep is tagged there
     * ({@link #isEqualsObjectCall} / {@link #isCompareToStringCall}). At any other vertex (none is known; census
     * {@code argSiteNotRedir=}) the argument is refused ({@code EQUALS_ARG_NO_SITE} / {@code COMPARETO_ARG_NO_SITE}).
     */
    static boolean redirectableArgSite(SugVertex phaseA, boolean compareTo) {
        return phaseA != null && (compareTo ? isCompareToStringCall(phaseA) : isEqualsObjectCall(phaseA));
    }

    /**
     * REDIRECT exactly where an admitted rep reaches an {@code equals(Object)} (or {@code compareTo(String)}) site as the
     * argument (a PARAMETER source tag at slot 1). The receiver role needs none (the devirtualized call on a rep receiver
     * dispatches to the rep's own {@code equals}/{@code compareTo}). A REDIRECT at a JDK-internal site applies to every
     * caller of that method (intended).
     */
    private static String classify(StringUtilizationGraph graph, SugVertex v, Set<SugVertex> customRepCandidates) {
        if (!isEqualsObjectCall(v) && !isCompareToStringCall(v)) {
            return VARIANT_FAST_PATH;
        }
        BitSet tags = v.getSourceTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            SourceTag tag = graph.getSourceTag(i);
            if (redirectsFor(tag.role(), tag.paramIndex()) && customRepCandidates.contains(tag.creationSite())) {
                return VARIANT_REDIRECT;
            }
        }
        return VARIANT_FAST_PATH;
    }

    /** Pure (pinned by JUnit): whether an admitted rep's source tag of this role asks for a REDIRECT. */
    static boolean redirectsFor(UsageRole role, int paramIndex) {
        return role == UsageRole.PARAMETER && paramIndex == 1;
    }
}
