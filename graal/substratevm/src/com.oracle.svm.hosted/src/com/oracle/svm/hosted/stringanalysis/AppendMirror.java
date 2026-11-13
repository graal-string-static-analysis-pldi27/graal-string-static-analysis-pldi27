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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import com.oracle.svm.hosted.phases.StringAnalysisChildInlining;

import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.Invoke;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * The builder-append mirror. A call to a builder append/insert/replace/constructor entry point that receives a STRING
 * atom in its string slot is a terminal argument sink keyed by site, like the equals/compareTo mirror:
 * <ul>
 * <li>Child: at a mirrorable site ({@link #mirrorableSite}) the PARAMETER usage is terminal and the JDK body is not
 * entered ({@link StringAtoms#mirrorArgRow} TERMINAL); without such a site the atom is refused
 * {@code MIRROR_ARG_NO_SITE}. After the final verdicts each site some admitted value-null rep reaches as that argument
 * gets the profile line {@code <key> MIRROR <KIND> <rep,...>} ({@link #emit}).</li>
 * <li>Parent: {@link AppendMirrorNodePlugin} lowers exactly that invoke to a rep-first chain: one arm per listed rep
 * (an exact test of the argument) calling the added mirror member of the same class ({@code appendRep},
 * {@code insertRep}, {@code insertSeqRep}, {@code replaceRep}, the {@code (String, Void)} constructors); the else is
 * the original invoke.</li>
 * </ul>
 * The entry points are the members of {@code AbstractStringBuilder}/{@code StringBuilder}/{@code StringBuffer} with a
 * {@code String}/{@code CharSequence}/{@code Object} parameter whose body reaches a String read of it,
 * declared non-bridge members only: a covariant bridge is an ordinary JDK method whose internal call to the real member
 * is itself a mirrorable site. The classification of every such member (table or reasoned exclusion) is pinned by
 * {@code AppendMirrorTest}.
 * <p>
 * Knob: {@code svm.stringanalysis.mirror.append} (1 = on, the default; 0 = off).
 */
public final class AppendMirror {

    static final int KNOB = Integer.getInteger("svm.stringanalysis.mirror.append", 1);

    /** The profile line type: {@code <key> MIRROR <KIND> <rep,...>}. */
    static final String LINE_TYPE = "MIRROR";

    private AppendMirror() {
    }

    /** Whether the mirror is on (pure; pinned by JUnit): any knob value above 0. */
    static boolean on(int knob) {
        return knob > 0;
    }

    static boolean on() {
        return on(KNOB);
    }

    /** The entry kinds (the profile line's KIND token): one invented mirror member each. */
    enum Kind {
        APPEND("appendRep", "(Ljava/lang/String;)"),
        APPEND_RANGE("appendRep", "(Ljava/lang/String;II)"),
        INSERT("insertRep", "(ILjava/lang/String;)"),
        INSERT_SEQ("insertSeqRep", "(ILjava/lang/String;)"),
        INSERT_RANGE("insertRep", "(ILjava/lang/String;II)"),
        REPLACE("replaceRep", "(IILjava/lang/String;)"),
        INIT("<init>", "(Ljava/lang/String;Ljava/lang/Void;)");

        final String mirrorName;
        /** The mirror's parameter part; the return part is the owner's own type ({@code V} for INIT). */
        final String mirrorParams;

        Kind(String mirrorName, String mirrorParams) {
            this.mirrorName = mirrorName;
            this.mirrorParams = mirrorParams;
        }
    }

    static final String ASB = "java.lang.AbstractStringBuilder";
    static final String SB = "java.lang.StringBuilder";
    static final String SBUF = "java.lang.StringBuffer";
    static final List<String> OWNERS = List.of(ASB, SB, SBUF);

    /**
     * One entry point: {@code owner#name descriptor}, the string slot (in the call's argument list, receiver = 0), its
     * kind, and the mirror member ({@link #mirrorDescriptor()}) on the same owner.
     */
    record Entry(String owner, String name, String descriptor, int slot, Kind kind) {
        String mirrorDescriptor() {
            return kind.mirrorParams + (kind == Kind.INIT ? "V" : "L" + owner.replace('.', '/') + ";");
        }

        String key() {
            return owner + "#" + name + descriptor;
        }
    }

    /** The table, per owner; descriptor return parts are the owner's own type. */
    static final Map<String, Entry> TABLE;
    /** The mirror members: {@code owner#name descriptor} -> the slot of the string in the mirror call. */
    static final Map<String, Integer> MIRRORS;

    static {
        Map<String, Entry> t = new LinkedHashMap<>();
        Map<String, Integer> m = new HashMap<>();
        for (String o : OWNERS) {
            String r = "L" + o.replace('.', '/') + ";";
            List<Entry> es = List.of(
                            new Entry(o, "append", "(Ljava/lang/String;)" + r, 1, Kind.APPEND),
                            new Entry(o, "append", "(Ljava/lang/CharSequence;)" + r, 1, Kind.APPEND),
                            new Entry(o, "append", "(Ljava/lang/Object;)" + r, 1, Kind.APPEND),
                            new Entry(o, "append", "(Ljava/lang/CharSequence;II)" + r, 1, Kind.APPEND_RANGE),
                            new Entry(o, "insert", "(ILjava/lang/String;)" + r, 2, Kind.INSERT),
                            new Entry(o, "insert", "(ILjava/lang/Object;)" + r, 2, Kind.INSERT),
                            new Entry(o, "insert", "(ILjava/lang/CharSequence;)" + r, 2, Kind.INSERT_SEQ),
                            new Entry(o, "insert", "(ILjava/lang/CharSequence;II)" + r, 2, Kind.INSERT_RANGE),
                            new Entry(o, "replace", "(IILjava/lang/String;)" + r, 3, Kind.REPLACE),
                            new Entry(o, "<init>", "(Ljava/lang/String;)V", 1, Kind.INIT),
                            new Entry(o, "<init>", "(Ljava/lang/CharSequence;)V", 1, Kind.INIT));
            for (Entry e : es) {
                t.put(e.key(), e);
                m.put(o + "#" + e.kind().mirrorName + e.mirrorDescriptor(), e.slot());
            }
        }
        TABLE = Collections.unmodifiableMap(t);
        MIRRORS = Collections.unmodifiableMap(m);
    }

    static Entry lookup(String owner, String name, String descriptor) {
        return TABLE.get(owner + "#" + name + descriptor);
    }

    /** The entry of a resolved method (declared, by exact descriptor; bridges are not entries), or null. */
    static Entry lookup(ResolvedJavaMethod m) {
        if (m == null || m.isStatic() || m.getDeclaringClass() == null || m.isBridge()) {
            return null;
        }
        return lookup(m.getDeclaringClass().toJavaName(true), m.getName(), m.getSignature().toMethodDescriptor());
    }

    /** The string slot of an invented mirror member's call (the rep arm's shape), or -1. */
    static int mirrorSlot(ResolvedJavaMethod m) {
        if (m == null || m.isStatic() || m.getDeclaringClass() == null) {
            return -1;
        }
        Integer s = MIRRORS.get(m.getDeclaringClass().toJavaName(true) + "#" + m.getName() + m.getSignature().toMethodDescriptor());
        return s == null ? -1 : s;
    }

    /** The slot of the string at a resolved target (the row's input): the entry's slot, or -1 for a non-entry. */
    static int stringSlot(ResolvedJavaMethod t) {
        Entry e = lookup(t);
        return e == null ? -1 : e.slot();
    }

    // ------------------------------------------------------------------
    // CHILD: the mirrorable site rule, the terminal sites, the census
    // ------------------------------------------------------------------

    /**
     * The site rule (pure): the Phase-A vertex exists, the invoke is not from a parse-time-inlined scope (else the child
     * keys the root, the parent the inlinee), the declared (bytecode) target is an entry point, the invoke kind is not
     * interface, and the key is not in a hidden class (unstable names).
     */
    static boolean mirrorableSite(boolean hasPhaseA, boolean fromInlinedScope, boolean declaredIsEntry, boolean interfaceKind, boolean hiddenKey) {
        return hasPhaseA && !fromInlinedScope && declaredIsEntry && !interfaceKind && !hiddenKey;
    }

    /** The site rule at a walked invoke: the mirrorable Phase-A vertex, or null. */
    static SugVertex mirrorSite(SugVertex phaseA, Invoke inv) {
        if (phaseA == null || inv == null || !(inv.callTarget() instanceof jdk.graal.compiler.nodes.java.MethodCallTargetNode ct)) {
            return null;
        }
        String key = phaseA.getSourceLocation();
        if (key == null || SiteKeys.UNKNOWN_KEY.equals(key)) {
            return null; // no key, no site: the atom is refused MIRROR_ARG_NO_SITE, never a terminal row without a line
        }
        boolean ok = mirrorableSite(true, StringAnalysisChildInlining.isFromInlinedScope(inv), lookup(ct.targetMethod()) != null, ct.invokeKind() == InvokeKind.Interface,
                        ForwardFixpoint.isHiddenSinkKey(phaseA.getSourceLocation()));
        return ok ? phaseA : null;
    }

    /** The terminal (mirrored) sites of this child: key -> the declared entry. */
    private static final Map<String, Entry> SITES = new ConcurrentHashMap<>();
    /** Keys whose invokes disagreed on the entry (never expected; no line, counted). */
    private static final Set<String> CONFLICTS = ConcurrentHashMap.newKeySet();
    static final AtomicLong TERMINALS = new AtomicLong();
    static final AtomicLong REFUSED = new AtomicLong();
    private static final Map<String, AtomicLong> NOSITE_BY = new ConcurrentHashMap<>();

    /** Records a TERMINAL row at the mirrorable site {@code v} of an invoke whose declared target is {@code declared}. */
    static void recordTerminal(SugVertex v, ResolvedJavaMethod declared) {
        TERMINALS.incrementAndGet();
        Entry e = lookup(declared);
        String key = v.getSourceLocation();
        if (e == null || key == null) {
            return;
        }
        Entry prev = SITES.putIfAbsent(key, e);
        if (prev != null && !prev.equals(e)) {
            CONFLICTS.add(key);
        }
    }

    /** Records a NO_SITE (refused) row of the resolved target {@code t}. */
    static void recordNoSite(ResolvedJavaMethod t) {
        Entry e = lookup(t);
        String k = e == null ? String.valueOf(t) : e.key();
        REFUSED.incrementAndGet();
        NOSITE_BY.computeIfAbsent(k, x -> new AtomicLong()).incrementAndGet();
    }

    /**
     * Admission evidence: a PARAMETER tag at a mirrored site's string slot is terminal evidence, as the
     * equals/compareTo argument (the body is never entered for it). Keyed per site.
     */
    static boolean isTerminalMirrorArgument(UsageTag tag) {
        SugVertex v = tag.usageSite();
        if (!on() || v == null || v.getSourceLocation() == null) {
            return false;
        }
        Entry e = SITES.get(v.getSourceLocation());
        return e != null && tag.paramIndex() == e.slot();
    }

    /**
     * The rep kinds a source tag's creation site may carry: the IC rep list's walk
     * ({@code InlineCacheProfilingHeuristic.collectRepFromCreationSite}) without its depth limit, so the list is never
     * partial (the site is terminal in the child, so a missing kind would reach the stock body). {@code visitedOut[0]} =
     * the vertices visited.
     */
    static Set<String> repKindsFrom(StringUtilizationGraph graph, SugVertex root, Map<SugVertex, InstrumentationDecision> decisionByCandidate, int[] visitedOut) {
        Set<String> kinds = new TreeSet<>();
        Set<SugVertex> visited = new HashSet<>();
        ArrayDeque<SugVertex> work = new ArrayDeque<>();
        if (root != null) {
            work.add(root);
        }
        while (!work.isEmpty()) {
            SugVertex v = work.poll();
            if (!visited.add(v)) {
                continue;
            }
            InstrumentationDecision d = decisionByCandidate.get(v);
            if (d != null) {
                String rep = HeuristicOrchestrator.repTypeOf(d);
                if (rep != null) {
                    kinds.add(rep);
                }
                continue;
            }
            if (v.getNodeType() != SugNodeType.STRING_METHOD_CALL && v.getNodeType() != SugNodeType.JDK_LIBRARY_CALL) {
                continue;
            }
            BitSet up = v.getSourceTags();
            for (int i = up.nextSetBit(0); i >= 0; i = up.nextSetBit(i + 1)) {
                SourceTag t = graph.getSourceTag(i);
                if (t.role() == UsageRole.RECEIVER && t.creationSite() != null) {
                    work.add(t.creationSite());
                }
            }
        }
        visitedOut[0] = visited.size();
        return kinds;
    }

    /** The child's emission: profile lines and print-only census lines. */
    record Emission(List<String> profileLines, List<String> logLines) {
    }

    /**
     * After the final verdicts: per mirrored site, the admitted value-null rep kinds with a PARAMETER source tag at the
     * entry's string slot; flat reps run the stock body correctly and get no arm; a site with an empty list gets no line.
     */
    static Emission emit(StringUtilizationGraph graph, List<InstrumentationDecision> toDump) {
        List<String> log = new ArrayList<>();
        /* the IC rep list's decision map and walk: EM/IC decisions are not reps */
        Map<SugVertex, InstrumentationDecision> decisionByCandidate = new HashMap<>();
        for (InstrumentationDecision d : toDump) {
            if (d.getType() != OptimizationType.EQUALS_MATRIX && d.getType() != OptimizationType.INLINE_CACHE && d.getCandidate() != null) {
                decisionByCandidate.put(d.getCandidate(), d);
            }
        }
        Map<SugVertex, Set<String>> kindsOf = new HashMap<>();
        int maxVisited = 0;
        Map<String, Set<String>> reps = new TreeMap<>();
        Map<String, Entry> entries = new HashMap<>();
        int flatOnly = 0;
        int user = 0;
        int jdk = 0;
        if (on()) {
            for (SugVertex v : graph.getVertices()) {
                String key = v.getSourceLocation();
                Entry e = key == null ? null : SITES.get(key);
                if (e == null || CONFLICTS.contains(key)) {
                    continue;
                }
                Set<String> ks = new TreeSet<>();
                boolean flat = false;
                BitSet tags = v.getSourceTags();
                for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
                    SourceTag tag = graph.getSourceTag(i);
                    if (tag.role() != UsageRole.PARAMETER || tag.paramIndex() != e.slot()) {
                        continue;
                    }
                    Set<String> found = kindsOf.get(tag.creationSite());
                    if (found == null) {
                        int[] visited = new int[1];
                        found = repKindsFrom(graph, tag.creationSite(), decisionByCandidate, visited);
                        maxVisited = Math.max(maxVisited, visited[0]);
                        kindsOf.put(tag.creationSite(), found);
                    }
                    for (String k : found) {
                        if (TerminalBodyKinds.isFlat(k)) {
                            flat = true;
                        } else {
                            ks.add(k);
                        }
                    }
                }
                if (ks.isEmpty()) {
                    flatOnly += flat ? 1 : 0;
                    continue;
                }
                reps.computeIfAbsent(key, x -> new TreeSet<>()).addAll(ks);
                entries.put(key, e);
            }
        }
        List<String> lines = new ArrayList<>();
        Map<Kind, Integer> byKind = new TreeMap<>();
        for (Map.Entry<String, Set<String>> r : reps.entrySet()) {
            Entry e = entries.get(r.getKey());
            lines.add(r.getKey() + " " + LINE_TYPE + " " + e.kind().name() + " " + String.join(",", r.getValue()));
            byKind.merge(e.kind(), 1, Integer::sum);
            if (StringAnalysisPolicy.isInternalClass(SiteKeys.classOf(r.getKey()))) {
                jdk++;
            } else {
                user++;
            }
        }
        log.add("[sug-mirror-append] knob=" + KNOB + " terminalSites=" + SITES.size() + " sites=" + lines.size() + " user=" + user + " jdk=" + jdk +
                        " flatOnly=" + flatOnly + " terminals=" + TERMINALS.get() + " nosite=" + REFUSED.get() + " conflicts=" + CONFLICTS.size() +
                        " maxVisited=" + maxVisited + " byKind=" + byKind);
        new TreeMap<>(NOSITE_BY).forEach((k, n) -> log.add("[sug-mirror-append-nosite] " + k + " x" + n.get()));
        lines.forEach(l -> log.add("[sug-mirror-append-site] " + l));
        return new Emission(lines, log);
    }
}
