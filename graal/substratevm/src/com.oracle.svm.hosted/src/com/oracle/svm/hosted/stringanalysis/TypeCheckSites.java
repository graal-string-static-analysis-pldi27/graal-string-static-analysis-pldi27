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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisMethod;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.NodeSourcePosition;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.printer.GraalDebugHandlersFactory;
import jdk.vm.ci.meta.JavaType;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Type-check IC, child side: one profile line {@code <key> TYPE_CHECK CAST|INST <variant>} per
 * {@code checkcast}/{@code instanceof java.lang.String} bytecode site whose {@code InstanceOfNode} is in the child IR
 * (own bytecode position, non-exact or an exact source-shape fold). The variant is the IC receiver variant
 * ({@link InlineCacheProfilingHeuristic#receiverVariant}) of the creation sites of the STRING atoms whose walk reached
 * the node (an observation, never a usage: no verdict reads it): rep-free, a rep list, or {@code UNPROVEN} (a depth
 * cut). A terminal-body site gets a line only in an argument-deflection body with the KT kind set on, united with that
 * set and {@code KT:}-marked. Flat closure: if the profile carries any {@code FLAT_HANDOFF_UNDELIVERED} line,
 * {@code SBS} is added to every line that is not UNPROVEN (an undelivered hand-off hands an untagged SBS to unwalked
 * code).
 * <p>
 * No line (stock): sites folded or GVN-merged away in the child IR, hidden classes, the rep package, {@code String$*}
 * nested classes, custom graphs, model bodies ({@link JdkModels#modelBodyMethod}: their checks of a modelled value are
 * not observed), a strict exact {@code instanceof String} (a CLASS_CHECK usage in the child), and every site of a method
 * inlined anywhere in the child: {@code AnalysisMethod.isInlined()} (InlineBeforeAnalysis copies the method's parse,
 * hence its line's lowering, into every caller, whose values the own-position observations do not see), or with a
 * String check seen at a non-outermost position (an inlined copy). The exclusion is per profile key: two methods can
 * share {@code class#name(desc)ret} (same FQN in two class loaders), so the ids of every inlined candidate are excluded.
 * <p>
 * Copies only the parent makes (its InlineBeforeAnalysis policy inlines far more): for M inlined into C by the parent
 * but not the child, the child keeps {@code C→M} as an invoke, so C's values are observed at M's own positions, under
 * the same key the parent's copy in C carries; M's line covers them. Knob {@code svm.stringanalysis.typecheck.ic}: 0 =
 * no observation, no line; 1 (default) and 2 = on (2 is the parent's CHECK mode; the child is identical).
 */
final class TypeCheckSites {

    static final int MODE = TypeCheckLines.MODE;
    static final String LINE_TYPE = TypeCheckLines.LINE_TYPE;
    static final String CAST = TypeCheckLines.CAST;
    static final String INST = TypeCheckLines.INST;
    static final String STRING_DESCRIPTOR = "Ljava/lang/String;";
    /** The flat kind of the undelivered hand-offs (they are recorded for admitted SINGLE_BYTE seeds only). */
    static final String FLAT_CLOSURE_KIND = "SBS";

    private TypeCheckSites() {
    }

    /**
     * The methods whose String type check the walk saw at a non-outermost position (an inlined copy), by
     * {@link #methodId}; they get no line. Cleared per analysis run by {@link RecursiveTracking}'s constructor.
     */
    static final Set<String> NON_OUTERMOST_OBSERVED = ConcurrentHashMap.newKeySet();

    /** {@code class#name(desc)ret} of a method (the profile key without {@code @bci}). */
    static String methodId(ResolvedJavaMethod m) {
        String k = SiteKeys.profileKey(m, 0);
        int at = k.lastIndexOf('@');
        return at < 0 ? k : k.substring(0, at);
    }

    private static boolean isStringCheck(InstanceOfNode ion) {
        return ion.type() != null && ion.type().getType() != null && STRING_DESCRIPTOR.equals(ion.type().getType().getName());
    }

    /**
     * The site key of an {@code InstanceOfNode} on String at its own bytecode position, else null. A String check at a
     * non-outermost position (an inlined copy) is recorded in {@link #NON_OUTERMOST_OBSERVED}.
     */
    static String observationKey(InstanceOfNode ion, @SuppressWarnings("unused") ValueNode n) {
        if (!isStringCheck(ion)) {
            return null;
        }
        NodeSourcePosition pos = ion.getNodeSourcePosition();
        if (pos == null || pos.getBCI() < 0 || pos.getMethod() == null) {
            return null;
        }
        if (pos.getCaller() != null) {
            NON_OUTERMOST_OBSERVED.add(methodId(pos.getMethod()));
            return null;
        }
        return SiteKeys.profileKey(pos.getMethod(), pos.getBCI());
    }

    /** The outcome of one variant computation (pure data). */
    record Variant(String text, boolean flatClosureAdded) {
    }

    /**
     * The line variant (pure; JUnit-pinned): the IC receiver variant of the observed creation sites; with a KT kind set
     * ({@code ktKinds} != null) united and {@code KT:}-marked; with the flat closure ({@code flatClosure}) adding
     * {@link #FLAT_CLOSURE_KIND}. UNPROVEN stays UNPROVEN (no proof: stock), KT-marked or not.
     */
    static Variant variant(InlineCacheProfilingHeuristic.RepFacts f, Set<String> ktKinds, boolean flatClosure) {
        String base = InlineCacheProfilingHeuristic.receiverVariant(f.any(), f.truncated(), f.exact(), f.custom());
        String marker = ktKinds != null ? TerminalBodyKinds.KT_PREFIX : "";
        if (InlineCacheProfilingHeuristic.UNPROVEN.equals(base)) {
            return new Variant(marker + base, false);
        }
        Set<String> reps = new LinkedHashSet<>(f.custom());
        if (ktKinds != null) {
            reps.addAll(ktKinds);
        }
        boolean flatAdded = flatClosure && reps.add(FLAT_CLOSURE_KIND);
        if (reps.equals(f.custom())) {
            return new Variant(marker + base, false);
        }
        return new Variant(marker + "EXACT," + String.join(",", reps), flatAdded);
    }

    static List<String> repNames(String variant) {
        return TypeCheckLines.repNames(variant);
    }

    /** The flat closure is on when the profile records undelivered flat hand-offs. */
    static boolean flatClosure(List<String> undeliveredLines) {
        return undeliveredLines != null && !undeliveredLines.isEmpty();
    }

    /**
     * Why a method's String type-check sites get no line (null = classified per site; pure). After the class
     * exclusions: {@code inlined} = {@code AnalysisMethod.isInlined()}; {@code nonOutermost} = a String check seen at a
     * non-outermost position (an inlined copy that need not set isInlined, e.g. a parse-time method-handle inline); a
     * terminal body gets a line only in an argument-deflection body
     * ({@link TerminalBodyKinds#isDeflectionBody}: the KT kind set covers the receiver and the deflection arguments, not
     * other values checked in a String body).
     */
    static String exclusion(String cls, String methodId, boolean hidden, boolean customGraph, boolean modelBody, boolean inlined, boolean nonOutermost) {
        String why = exclusion(cls, hidden, customGraph, modelBody);
        if (why != null) {
            return why;
        }
        if (inlined) {
            return "inlined";
        }
        if (nonOutermost) {
            return "non-outermost";
        }
        if (TerminalBodyKinds.group(cls) != TerminalBodyKinds.Group.NONE) {
            int hash = methodId.indexOf('#');
            int paren = methodId.indexOf('(', hash + 1);
            if (hash < 0 || paren < 0 || !TerminalBodyKinds.isDeflectionBody(cls, methodId.substring(hash + 1, paren), methodId.substring(paren))) {
                return "terminal-non-deflection";
            }
        }
        return null;
    }

    /** The class-level exclusions (the census; null = not excluded by class). */
    static String exclusion(String cls, boolean hidden, boolean customGraph, boolean modelBody) {
        if (hidden) {
            return "hidden";
        }
        if (cls.startsWith("com.oracle.svm.core.stringrep.")) {
            return "rep";
        }
        if (cls.startsWith("java.lang.String$")) {
            return "string-nested";
        }
        if (customGraph) {
            return "custom-graph";
        }
        if (modelBody) {
            return "model-body";
        }
        return null;
    }

    record Emission(List<String> profileLines, List<String> logLines) {
    }

    static Emission compute(PointsToAnalysis bb, AnalysisUniverse universe, StringUtilizationGraph sug, InlineCacheProfilingHeuristic ic, List<String> undeliveredLines) {
        long start = System.nanoTime();
        List<String> log = new ArrayList<>();
        if (MODE == 0) {
            log.add("[sug-typecheck] knob=0 sites=0");
            return new Emission(List.of(), log);
        }
        boolean flatClosure = flatClosure(undeliveredLines);
        Map<String, Set<SugVertex>> obs = sug.getTypeCheckObservations();
        Map<String, String> lines = new TreeMap<>();
        Map<String, Integer> excluded = new TreeMap<>();
        int folded = 0;
        int decoded = 0;
        int repfree = 0;
        int replist = 0;
        int unproven = 0;
        int kt = 0;
        int flatAdded = 0;
        int cast = 0;
        int inst = 0;
        int observedSites = 0;
        DebugContext debug = new DebugContext.Builder(bb.getOptions(), new GraalDebugHandlersFactory(bb.getSnippetReflectionProvider())).build();
        // pass 1: decode every candidate graph; collect its own-position sites and the non-outermost String checks
        record Cand(AnalysisMethod am, String cls, String mid, Map<Integer, Integer> bc, Set<Integer> present, Set<Integer> strict) {
        }
        List<Cand> cands = new ArrayList<>();
        Set<String> nonOutermost = new java.util.HashSet<>(NON_OUTERMOST_OBSERVED);
        for (AnalysisMethod am : universe.getMethods()) {
            if (!am.isReachable() || !(am instanceof PointsToAnalysisMethod) || !am.isOriginalMethod() || am.getAnalyzedGraph() == null) {
                continue;
            }
            Map<Integer, Integer> bc = stringTypeCheckBcis(am);
            if (bc.isEmpty()) {
                continue;
            }
            String cls = am.getDeclaringClass().toJavaName(true);
            String mid = methodId(am);
            String why = exclusion(cls, ExactReceiverSites.isHidden(am.getDeclaringClass()), ExactReceiverSites.hasCustomGraph(bb, am), JdkModels.modelBodyMethod(cls, mid));
            if (why != null) {
                excluded.merge(why, bc.size(), Integer::sum);
                continue;
            }
            StructuredGraph g;
            try {
                g = am.decodeAnalyzedGraph(debug, null);
            } catch (Throwable t) {
                g = null;
            }
            if (g == null) {
                excluded.merge("no-graph", bc.size(), Integer::sum);
                continue;
            }
            decoded++;
            Set<Integer> present = new LinkedHashSet<>();
            Set<Integer> strict = new LinkedHashSet<>();
            for (InstanceOfNode ion : g.getNodes().filter(InstanceOfNode.class)) {
                if (!isStringCheck(ion)) {
                    continue;
                }
                NodeSourcePosition pos = ion.getNodeSourcePosition();
                if (pos != null && pos.getCaller() != null && pos.getMethod() != null) {
                    nonOutermost.add(methodId(pos.getMethod())); // an inlined copy of that method's check
                    continue;
                }
                if (pos == null || !am.equals(pos.getMethod()) || !bc.containsKey(pos.getBCI())) {
                    continue;
                }
                int op = bc.get(pos.getBCI());
                if (ion.type().isExact() && op == Bytecodes.INSTANCEOF) {
                    strict.add(pos.getBCI()); // LfgWalk.instanceofSourceFoldAllowed: no fold for an instanceof of String
                } else {
                    present.add(pos.getBCI());
                }
            }
            cands.add(new Cand(am, cls, mid, bc, present, strict));
        }
        // the inlined-method exclusion by key (method id), not by method: a same-key sibling of an inlined method too
        Set<String> inlined = inlinedMids(cands, Cand::mid, c -> c.am().isInlined());
        // pass 2: the method-level exclusions that need every graph (the inlined-method exclusion), the terminal-body rule, the lines
        for (Cand c : cands) {
            AnalysisMethod am = c.am();
            Map<Integer, Integer> bc = c.bc();
            String why = exclusion(c.cls(), c.mid(), false, false, false, inlined.contains(c.mid()), nonOutermost.contains(c.mid()));
            if (why != null) {
                excluded.merge(why, bc.size(), Integer::sum);
                continue;
            }
            for (Map.Entry<Integer, Integer> e : bc.entrySet()) {
                int bci = e.getKey();
                if (!c.present().contains(bci)) {
                    if (c.strict().contains(bci)) {
                        excluded.merge("strict-instanceof", 1, Integer::sum);
                    } else {
                        folded++;
                    }
                    continue;
                }
                String key = SiteKeys.profileKey(am, bci);
                Set<SugVertex> cs = obs.getOrDefault(key, Set.of());
                observedSites += cs.isEmpty() ? 0 : 1;
                Set<String> ktKinds = ic.ktKindSet(key);
                Variant v = variant(ic.repFactsOf(sug, cs), ktKinds, flatClosure);
                List<String> reps = repNames(v.text());
                if (reps == null) {
                    unproven++;
                } else if (reps.isEmpty()) {
                    repfree++;
                } else {
                    replist++;
                }
                kt += ktKinds != null ? 1 : 0;
                flatAdded += v.flatClosureAdded() ? 1 : 0;
                boolean isCast = e.getValue() == Bytecodes.CHECKCAST;
                if (isCast) {
                    cast++;
                } else {
                    inst++;
                }
                lines.put(key, key + " " + LINE_TYPE + " " + (isCast ? CAST : INST) + " " + v.text());
            }
        }
        log.add("[sug-typecheck] knob=" + MODE + " sites=" + lines.size() + " (cast=" + cast + " inst=" + inst + ") repfree=" + repfree + " replist=" + replist + " unproven=" + unproven +
                        " kt=" + kt + " flat-closure=" + (flatClosure ? 1 : 0) + " (added to " + flatAdded + ") observed=" + observedSites + " nolined(folded=" + folded + " excluded=" + excluded +
                        ") decoded=" + decoded + " non-outermost-methods=" + nonOutermost.size() + " " + ((System.nanoTime() - start) / 1_000_000) + "ms");
        return new Emission(new ArrayList<>(lines.values()), log);
    }

    /**
     * The method ids of the inlined candidates (pure). Every candidate with such an id is excluded, so no key keeps a
     * line the parent would also apply to the copies of an inlined method with the same key.
     */
    static <T> Set<String> inlinedMids(List<T> cands, java.util.function.Function<T, String> mid, java.util.function.Predicate<T> isInlined) {
        Set<String> out = new java.util.HashSet<>();
        for (T c : cands) {
            if (isInlined.test(c)) {
                out.add(mid.apply(c));
            }
        }
        return out;
    }

    /** bci -> opcode of the {@code checkcast}/{@code instanceof} bytecodes of {@code am} whose type is {@code java.lang.String}. */
    static Map<Integer, Integer> stringTypeCheckBcis(AnalysisMethod am) {
        return stringTypeCheckBcis(am.getWrapped()); // the host constant pool: no analysis-universe lookups
    }

    /** {@link #stringTypeCheckBcis(AnalysisMethod)} of a host method (also the premise pin's scan). */
    static Map<Integer, Integer> stringTypeCheckBcis(ResolvedJavaMethod raw) {
        Map<Integer, Integer> out = new TreeMap<>();
        byte[] code;
        try {
            code = raw.getCode();
        } catch (Throwable t) {
            return out;
        }
        if (code == null || code.length == 0) {
            return out;
        }
        try {
            BytecodeStream s = new BytecodeStream(code);
            while (s.currentBC() != Bytecodes.END) {
                int op = s.currentBC();
                if (op == Bytecodes.CHECKCAST || op == Bytecodes.INSTANCEOF) {
                    JavaType t = raw.getConstantPool().lookupType(s.readCPI(), op);
                    if (t != null && STRING_DESCRIPTOR.equals(t.getName())) {
                        out.put(s.currentBCI(), op);
                    }
                }
                s.next();
            }
        } catch (Throwable t) {
            return new TreeMap<>();
        }
        return out;
    }
}
