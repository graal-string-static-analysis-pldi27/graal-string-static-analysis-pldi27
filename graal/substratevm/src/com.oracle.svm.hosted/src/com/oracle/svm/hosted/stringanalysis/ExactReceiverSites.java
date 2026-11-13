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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.infrastructure.GraphProvider;
import com.oracle.graal.pointsto.flow.AbstractVirtualInvokeTypeFlow;
import com.oracle.graal.pointsto.flow.InvokeTypeFlow;
import com.oracle.graal.pointsto.flow.MethodFlowsGraph;
import com.oracle.graal.pointsto.flow.MethodTypeFlow;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisMethod;
import com.oracle.graal.pointsto.typestate.TypeState;
import com.oracle.svm.hosted.substitute.AnnotatedMethod;
import com.oracle.svm.hosted.substitute.SubstitutionMethod;

import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin;
import jdk.vm.ci.code.BytecodePosition;

/**
 * Exact-receiver sites (child side): the supertype-declared ({@code CharSequence}/{@code Object}/...) virtual or
 * interface invokes of a String IC member that carry a rep-list {@code INLINE_CACHE} entry and where stock would bind
 * the call to {@code String.<m>}: the child's receiver state is exactly {String} (the child instantiates no rep; rep
 * types are subtracted anyway), not saturated, and the invoke has exactly one callee, a String method. Each such key gets
 * the line {@code <key> EXACT_RECV STRING}; the parent lowers it to the all-direct exact-first chain
 * ({@code InlineCacheTrivialMethodNodePlugin.lowerExactReceiverSuperSite}). A site without the proof gets no line and
 * stays virtual.
 * <p>
 * The key must name the parse the parent sees: the invoke's own bytecode position, one invoke per key, the bytecode's
 * own target equal to the flow's, a bytecode-parsed graph, the enclosing method not inlined before the analysis (its
 * keys live in the callers' graphs), not in a hidden class. {@code EQUALS_MATRIX} keys and {@code KT:} entries are left
 * out. A proven key gets the line only if no listed rep overrides the member ({@link #hasLiveRepArm}; the parent's
 * {@code super-collapsed} form), otherwise it stays a stock virtual/interface call ({@link Verdict#LIVE_REP_ARM}).
 */
final class ExactReceiverSites {

    static final String LINE_TYPE = "EXACT_RECV";
    static final String VARIANT = "STRING";

    private static final String STRING = "java.lang.String";

    private ExactReceiverSites() {
    }

    /** The outcome per examined rep-list key (pure; pinned by the JUnit). */
    enum Verdict {
        PROVEN,
        NOT_SUPER_OWNER,
        NOT_MEMBER,
        NOT_VIRTUAL,
        NOT_OWN_POSITION,
        KEY_NOT_UNIQUE,
        BC_TARGET_MISMATCH,
        HIDDEN_CLASS,
        NO_BYTECODE,
        CUSTOM_GRAPH,
        INLINED_BEFORE_ANALYSIS,
        SATURATED,
        EMPTY_STATE,
        OTHER_TYPES,
        CALLEES_NOT_ONE_STRING,
        /** Proven, but (mode 2) a listed rep overrides the member: the parent would build a live rep arm. */
        LIVE_REP_ARM
    }

    /**
     * Does the rep list {@code variant} of an INLINE_CACHE entry leave a live arm for the member {@code nd}
     * (name + descriptor)? The parent's rule ({@code InlineCacheTrivialMethodNodePlugin.lowerRepList}): a listed rep gets
     * an arm iff the JVM's selection for it ({@link TerminalBodyKinds#implementingClass}) is not String's body. An
     * unresolvable rep or member counts as live (conservative: no line, the site stays stock).
     */
    static boolean hasLiveRepArm(String variant, String nd) {
        java.lang.reflect.Method member = StringIcMethods.lookup(nd);
        if (variant == null || member == null) {
            return true;
        }
        List<String> reps = InlineCacheTrivialMethodNodePlugin.parseRepNames(variant, variant.startsWith("EXACT,"));
        if (reps.isEmpty()) {
            return true;
        }
        for (String r : reps) {
            Class<?> repClass = InlineCacheRegistry.getRepClass(r);
            Class<?> impl = repClass == null ? null : TerminalBodyKinds.implementingClass(repClass, member);
            if (impl != String.class) {
                return true;
            }
        }
        return false;
    }

    /** The facts of one invoke at a rep-list key (pure data). */
    record Facts(String owner, boolean ownerProperStringSuper, boolean member, boolean virtual, boolean ownPosition, int keyCount, String[] bytecodeTarget, String name, String desc,
                    boolean hidden, boolean hasBytecode, boolean customGraph, boolean inlined, boolean saturated, List<String> receiverTypes, List<String> callees) {
    }

    /** The proof predicate (pure). */
    static Verdict verdict(Facts f) {
        if (!f.ownerProperStringSuper()) {
            return Verdict.NOT_SUPER_OWNER;
        }
        if (!f.member()) {
            return Verdict.NOT_MEMBER;
        }
        if (!f.virtual()) {
            return Verdict.NOT_VIRTUAL;
        }
        if (f.hidden()) {
            return Verdict.HIDDEN_CLASS;
        }
        if (!f.hasBytecode()) {
            return Verdict.NO_BYTECODE;
        }
        if (f.customGraph()) {
            return Verdict.CUSTOM_GRAPH;
        }
        if (f.inlined()) {
            return Verdict.INLINED_BEFORE_ANALYSIS;
        }
        if (!f.ownPosition()) {
            return Verdict.NOT_OWN_POSITION;
        }
        if (f.keyCount() != 1) {
            return Verdict.KEY_NOT_UNIQUE;
        }
        String[] bt = f.bytecodeTarget();
        if (bt == null || !bt[0].equals(f.owner()) || !bt[1].equals(f.name()) || !bt[2].equals(f.desc())) {
            return Verdict.BC_TARGET_MISMATCH;
        }
        if (f.saturated() || f.receiverTypes() == null) {
            return Verdict.SATURATED;
        }
        List<String> nonRep = f.receiverTypes(); // the scan already left out the String subtypes (reps)
        if (nonRep.isEmpty()) {
            return Verdict.EMPTY_STATE;
        }
        if (nonRep.size() != 1 || !STRING.equals(nonRep.get(0))) {
            return Verdict.OTHER_TYPES;
        }
        List<String> callees = f.callees();
        if (callees == null || callees.size() != 1 || !callees.get(0).startsWith(STRING + "#")) {
            return Verdict.CALLEES_NOT_ONE_STRING;
        }
        return Verdict.PROVEN;
    }

    /** The rep-list INLINE_CACHE keys of the dumped decisions (first per key, as the profile keeps), minus EQUALS_MATRIX keys and KT entries. */
    static Set<String> repListKeys(List<InstrumentationDecision> dumped) {
        return new TreeSet<>(repListVariants(dumped).keySet());
    }

    /** {@link #repListKeys} with each key's rep-list variant. */
    static Map<String, String> repListVariants(List<InstrumentationDecision> dumped) {
        Set<String> seen = new HashSet<>();
        Set<String> emKeys = new HashSet<>();
        Map<String, String> out = new TreeMap<>();
        for (InstrumentationDecision d : dumped) {
            if (d.getSourceLocation() != null && d.getType() == OptimizationType.EQUALS_MATRIX) {
                emKeys.add(d.getSourceLocation());
            }
        }
        for (InstrumentationDecision d : dumped) {
            if (d.getSourceLocation() == null || d.getType() != OptimizationType.INLINE_CACHE || !seen.add(d.getSourceLocation())) {
                continue;
            }
            String v = d.getVariant();
            if (v == null || TerminalBodyKinds.stripMarker(v) != null || emKeys.contains(d.getSourceLocation())) {
                continue;
            }
            if (!v.equals("UNKNOWN") && !v.equals("EXACT_STRING") && !v.equals(InlineCacheProfilingHeuristic.UNPROVEN)) {
                out.put(d.getSourceLocation(), v);
            }
        }
        return out;
    }

    /** The child's result: profile lines ({@code <key> EXACT_RECV STRING}) and print-only census lines. */
    record Emission(List<String> profileLines, List<String> logLines) {
    }

    static Emission compute(PointsToAnalysis bb, AnalysisUniverse universe, List<InstrumentationDecision> dumped, boolean repTypesUnreachable, String repTypesStatus) {
        List<String> log = new ArrayList<>();
        Map<String, String> variants = repListVariants(dumped);
        Set<String> keys = variants.keySet();
        if (!repTypesUnreachable) {
            log.add("[sug-exact-recv] OFF(rtypes=" + repTypesStatus + ") replist=" + keys.size() + " sites=0");
            return new Emission(List.of(), log);
        }
        Map<String, Verdict> verdicts = new TreeMap<>();
        Map<String, String> members = new HashMap<>();
        if (!keys.isEmpty()) {
            scan(bb, universe, keys, verdicts, members);
        }
        verdicts.replaceAll((k, v) -> v == Verdict.PROVEN && hasLiveRepArm(variants.get(k), members.get(k)) ? Verdict.LIVE_REP_ARM : v);
        List<String> lines = new ArrayList<>();
        Map<Verdict, Integer> by = new TreeMap<>();
        for (Map.Entry<String, Verdict> e : verdicts.entrySet()) {
            by.merge(e.getValue(), 1, Integer::sum);
            if (e.getValue() == Verdict.PROVEN) {
                lines.add(e.getKey() + " " + LINE_TYPE + " " + VARIANT);
            }
            log.add("[sug-exact-recv-site] " + e.getValue() + " " + e.getKey());
        }
        log.add(0, "[sug-exact-recv] rtypes=" + repTypesStatus + " replist=" + keys.size() + " superSites=" + verdicts.size() + " sites=" + lines.size() + " by=" + by);
        return new Emission(lines, log);
    }

    /**
     * Debug only (parent, {@code ic.exactfirst.super.check=1}): per exact-receiver site, the parent's points-to state of the
     * argument of the {@code D1Check.check} call that replaced the trusted String narrowing (the Part-B filter is left out
     * in that mode), i.e. what reaches the else: String from the exact-first arm, plus whatever the rep tests let through.
     * A type that is neither String nor a String subtype there is a parent-only flow the child's proof did not see.
     */
    static List<String> parentCheckLines(PointsToAnalysis bb, AnalysisUniverse universe) {
        AnalysisType stringType = bb.getMetaAccess().lookupJavaType(String.class);
        Map<String, String> lines = new TreeMap<>();
        int foreign = 0;
        for (AnalysisMethod am : universe.getMethods()) {
            if (!am.isReachable() || !(am instanceof PointsToAnalysisMethod ptm)) {
                continue;
            }
            MethodTypeFlow mtf = ptm.getTypeFlow();
            if (mtf == null || !mtf.flowsGraphCreated() || mtf.getMethodFlowsGraph() == null) {
                continue;
            }
            for (InvokeTypeFlow inv : mtf.getMethodFlowsGraph().getInvokes()) {
                AnalysisMethod t = inv.getTargetMethod();
                if (t == null || !t.getName().equals("check") || !t.getDeclaringClass().toJavaName(true).equals("com.oracle.svm.core.stringrep.D1Check")) {
                    continue;
                }
                String key = inv.getSource() instanceof BytecodePosition pos && pos.getMethod() instanceof AnalysisMethod pm ? SiteKeys.profileKey(pm, pos.getBCI()) : "?";
                TypeFlow<?>[] actual = inv.getActualParameters();
                List<String> types = new ArrayList<>();
                boolean f = false;
                if (actual != null && actual.length > 0 && actual[0] != null) {
                    TypeState st = mtf.foldTypeFlow(bb, actual[0]);
                    if (st != null) {
                        for (AnalysisType at : st.types(bb)) {
                            types.add(at.toJavaName(true));
                            f |= !stringType.isAssignableFrom(at);
                        }
                        if (st.canBeNull()) {
                            types.add("null");
                        }
                    }
                }
                types.sort(null);
                foreign += f ? 1 : 0;
                lines.merge(key + " in " + am.format("%H.%n"), (f ? "NON-STRING " : "") + types, (a, b) -> a + " | " + b);
            }
        }
        List<String> out = new ArrayList<>();
        out.add("[d1-check] sites=" + lines.size() + " with a non-String type=" + foreign);
        lines.forEach((k, v) -> out.add("[d1-check-site] " + k + " else-state=" + v));
        return out;
    }

    private static void scan(PointsToAnalysis bb, AnalysisUniverse universe, Set<String> keys, Map<String, Verdict> verdicts, Map<String, String> members) {
        AnalysisType stringType = bb.getMetaAccess().lookupJavaType(String.class);
        for (AnalysisMethod am : universe.getMethods()) {
            if (!am.isReachable() || !(am instanceof PointsToAnalysisMethod ptm) || !am.isOriginalMethod()) {
                continue;
            }
            MethodTypeFlow mtf = ptm.getTypeFlow();
            if (mtf == null || !mtf.flowsGraphCreated()) {
                continue;
            }
            MethodFlowsGraph graph = mtf.getMethodFlowsGraph();
            if (graph == null || graph.isStub()) {
                continue;
            }
            Map<Integer, Integer> perBci = new HashMap<>();
            List<InvokeTypeFlow> atKeys = new ArrayList<>();
            for (InvokeTypeFlow inv : graph.getInvokes()) {
                if (inv.getSource() instanceof BytecodePosition pos && pos.getCaller() == null && am.equals(pos.getMethod())) {
                    perBci.merge(pos.getBCI(), 1, Integer::sum);
                    if (keys.contains(SiteKeys.profileKey(am, pos.getBCI()))) {
                        atKeys.add(inv);
                    }
                }
            }
            if (atKeys.isEmpty()) {
                continue;
            }
            boolean hasBytecode = am.getCodeSize() > 0;
            boolean hidden = isHidden(am.getDeclaringClass());
            boolean custom = hasBytecode && hasCustomGraph(bb, am);
            byte[] code = null;
            if (hasBytecode) {
                try {
                    code = am.getCode();
                } catch (Throwable e) {
                    code = null;
                }
            }
            for (InvokeTypeFlow inv : atKeys) {
                AnalysisMethod target = inv.getTargetMethod();
                if (target == null || !target.hasReceiver()) {
                    continue;
                }
                int bci = ((BytecodePosition) inv.getSource()).getBCI();
                String key = SiteKeys.profileKey(am, bci);
                AnalysisType owner = target.getDeclaringClass();
                String ownerName = owner.toJavaName(true);
                boolean properSuper = !STRING.equals(ownerName) && owner.isAssignableFrom(stringType);
                if (!properSuper) {
                    continue; // a String-declared (or unrelated) invoke at the key: the ordinary IC path
                }
                String nd = target.getName() + target.getSignature().toMethodDescriptor();
                boolean virtual = inv instanceof AbstractVirtualInvokeTypeFlow;
                boolean saturated = false;
                List<String> recvTypes = null;
                List<String> callees = null;
                if (virtual) {
                    TypeFlow<?> recv = inv.getReceiver();
                    saturated = recv == null || mtf.isSaturated(bb, recv) || inv.isSaturated();
                    if (!saturated) {
                        TypeState st = mtf.foldTypeFlow(bb, recv);
                        recvTypes = new ArrayList<>();
                        if (st != null) {
                            for (AnalysisType at : st.types(bb)) {
                                if (!at.equals(stringType) && stringType.isAssignableFrom(at)) {
                                    continue; // a rep is a proper String subtype (not a package test)
                                }
                                recvTypes.add(at.toJavaName(true));
                            }
                        }
                        recvTypes.sort(null);
                        callees = new ArrayList<>();
                        for (AnalysisMethod c : inv.getOriginalCallees()) {
                            callees.add(c.getDeclaringClass().toJavaName(true) + "#" + c.getName() + c.getSignature().toMethodDescriptor());
                        }
                        callees.sort(null);
                    }
                }
                Facts f = new Facts(ownerName, true, StringIcMethods.lookup(nd) != null, virtual, true, perBci.getOrDefault(bci, 0), bytecodeTarget(am, code, bci),
                                target.getName(), target.getSignature().toMethodDescriptor(), hidden, hasBytecode, custom, am.isInlined(), saturated, recvTypes, callees);
                Verdict v = verdict(f);
                members.putIfAbsent(key, nd);
                Verdict prev = verdicts.putIfAbsent(key, v);
                if (prev != null && prev != v) {
                    verdicts.put(key, Verdict.KEY_NOT_UNIQUE);
                }
            }
        }
    }

    static boolean isHidden(AnalysisType t) {
        try {
            Class<?> c = t.getJavaClass();
            if (c != null && c.isHidden()) {
                return true;
            }
        } catch (Throwable ignored) {
            // fall back to the name
        }
        String n = t.toJavaName(true);
        return n.contains("/0x") || n.contains("$$Lambda");
    }

    private static final int INVOKEVIRTUAL = 0xb6;
    private static final int INVOKESPECIAL = 0xb7;
    private static final int INVOKEINTERFACE = 0xb9;

    /** {owner, name, descriptor} of the invokevirtual/invokespecial/invokeinterface at {@code bci}, or null. */
    static String[] bytecodeTarget(AnalysisMethod am, byte[] code, int bci) {
        if (code == null || bci < 0 || bci + 2 >= code.length) {
            return null;
        }
        int op = code[bci] & 0xff;
        if (op != INVOKEVIRTUAL && op != INVOKESPECIAL && op != INVOKEINTERFACE) {
            return null;
        }
        int cpi = ((code[bci + 1] & 0xff) << 8) | (code[bci + 2] & 0xff);
        try {
            // the analysis universe's view of the pool: substitution aliases (Target_java_lang_String) map to their originals
            jdk.vm.ci.meta.JavaMethod jm = am.getConstantPool().lookupMethod(cpi, op);
            if (jm == null) {
                return null;
            }
            return new String[]{jm.getDeclaringClass().toJavaName(true), jm.getName(), jm.getSignature().toMethodDescriptor()};
        } catch (Throwable e) {
            return null;
        }
    }

    /**
     * The analysis graph is not parsed from the method's bytecode: a {@code GraphProvider} somewhere in the
     * substitution chain (custom substitution, non-bytecode, polymorphic-signature wrapper), or a non-inline-only
     * intrinsic invocation plugin ({@code AnalysisParsedGraph.parseBytecode}'s order). Unreadable = custom (fail closed).
     */
    static boolean hasCustomGraph(PointsToAnalysis bb, AnalysisMethod am) {
        try {
            Object m = am.getWrapped();
            for (int i = 0; i < 16 && m != null; i++) {
                if (m instanceof SubstitutionMethod sm) {
                    m = sm.getAnnotated();
                } else if (m instanceof AnnotatedMethod an) {
                    m = an.getOriginal();
                } else {
                    if (m instanceof GraphProvider) {
                        return true;
                    }
                    break;
                }
            }
            InvocationPlugin plugin = bb.getProviders(am).getGraphBuilderPlugins().getInvocationPlugins().lookupInvocation(am, bb.getOptions());
            return plugin != null && !plugin.inlineOnly();
        } catch (Throwable e) {
            return true;
        }
    }
}
