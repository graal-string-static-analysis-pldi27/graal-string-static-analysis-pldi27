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

import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.cap;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;

import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.MethodContext;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.AtomKind;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtom;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtomKey;

/**
 * The holder-end rule of {@link RecursiveTracking}: explained holder ends only.
 */
final class HolderEndRule {
    private final RecursiveTracking rt;

    HolderEndRule(RecursiveTracking rt) {
        this.rt = rt;
    }

    // ------------------------------------------------------------------
    // The holder-end rule: explained holder ends only.
    // ------------------------------------------------------------------

    /** How an escape's "no load" fact is proven. */
    enum EscKind {
        STATIC,
        VMTL,
        CLOSED,
        IDENTITY
    }

    /** One escape of an atom (per member / static field / VM thread-local; the holders are the identity route's receivers). */
    static final class EscRec {
        final EscKind kind;
        final String what;
        /** CLOSED only: the read index's load sites of the field. */
        final int closedLoads;
        /** CLOSED only: some escape into this field fell back to every load site. */
        final AtomicBoolean fell = new AtomicBoolean();
        final Set<Object> holders = ConcurrentHashMap.newKeySet();
        /** Some receiver delivery was skipped as the infeasible store into a length-0 array. */
        final AtomicBoolean len0Skipped = new AtomicBoolean();

        EscRec(EscKind kind, String what, int closedLoads) {
            this.kind = kind;
            this.what = what;
            this.closedLoads = closedLoads;
        }

        boolean holderFree() {
            return escHolderFree(kind, closedLoads, fell.get());
        }
    }

    /** A path-less return's wait on an entry-path list (owner OWNER(Y), or the identity caller set). */
    static final class WaitRec {
        final String kind;
        final LocalFlowGraph frame;
        final Object on;
        final AtomicBoolean delivered = new AtomicBoolean();
        final AtomicBoolean fell = new AtomicBoolean();

        WaitRec(String kind, LocalFlowGraph frame, Object on) {
            this.kind = kind;
            this.frame = frame;
            this.on = on;
        }
    }

    /** The per-atom holder facts (allocated at the first event). */
    static final class HolderLog {
        final Map<Object, EscRec> escapes = new ConcurrentHashMap<>();
        final Map<List<Object>, WaitRec> waits = new ConcurrentHashMap<>();
        /** Every silent end's label (capped, print-only). */
        final Set<String> ends = ConcurrentHashMap.newKeySet();
        /** Per cause, the number of silent ends (print-only). */
        final Map<String, AtomicInteger> endsByCause = new ConcurrentHashMap<>();
        /** The unexplained silent ends (the rule's input; capped labels, but {@link #unexplainedN} counts all). */
        final Set<String> unexplained = ConcurrentHashMap.newKeySet();
        final AtomicInteger unexplainedN = new AtomicInteger();
    }

    HolderLog hlog(RAtom a) {
        HolderLog h = a.hlog;
        if (h == null) {
            synchronized (a) {
                h = a.hlog;
                if (h == null) {
                    h = new HolderLog();
                    a.hlog = h;
                }
            }
        }
        return h;
    }

    /** The escape record of {@code atom} for {@code key}. */
    EscRec escRec(RAtom atom, Object key, EscKind kind, String what, int closedLoads) {
        return hlog(atom).escapes.computeIfAbsent(key, k -> new EscRec(kind, what, closedLoads));
    }

    /** The wait record of a path-less return of {@code atom}. */
    WaitRec waitRec(RAtom atom, String kind, LocalFlowGraph frame, Object on) {
        return hlog(atom).waits.computeIfAbsent(java.util.Arrays.asList(kind, frame, on), k -> new WaitRec(kind, frame, on));
    }

    /** A holder-free escape (pure; pinned by JUnit): static, VM thread-local, a closed field with no load site, or fallen back. */
    static boolean escHolderFree(EscKind kind, int closedLoads, boolean fell) {
        return switch (kind) {
            case STATIC, VMTL -> true;
            case CLOSED -> closedLoads == 0 || fell;
            case IDENTITY -> false;
        };
    }

    /**
     * Whether a silent end's cause ({@link RecursiveTracking#silentCause}) is a sound end of a holder walk (pure; pinned by JUnit). Each is
     * a place where the holder provably cannot be read further:
     * <ul>
     * <li>{@code dead-target}: the callee is absent from the points-to universe (not implementation-invoked, not reachable:
     * {@link RecursiveTracking#dropDeadTarget}); it is not compiled into the image, so it never runs;</li>
     * <li>{@code unread-param}: the callee has no ParameterNode for the slot (nothing can flow);</li>
     * <li>{@code monitor-obs}: the object slot of a monitor operation (identity only, no field read);</li>
     * <li>{@code no-usages}, {@code state}, {@code obs}: the node has no usage, or only frame states / identity, null,
     * type or hub observations ({@link RecursiveTracking#OBSERVATIONS}): no field is read through them;</li>
     * <li>{@code pi-arm-dead}, {@code arm-dead-usage}: an arm no member of the atom's type block can take (the arm-liveness
     * table, the same premise the STRING walks use);</li>
     * <li>{@code classname-only-getClass}: only the class name is read;</li>
     * <li>{@code infeasible-owner}: a return wait under an owner whose exact class cannot be the frame's receiver
     * ({@link #waitEndCause}).</li>
     * </ul>
     * Anything else (in particular {@code ret-no-caller}) is unexplained.
     */
    static boolean soundEndCause(String cause) {
        return switch (cause) {
            case "dead-target", "unread-param", "monitor-obs", "no-usages", "state", "pi-arm-dead", "arm-dead-usage", "classname-only-getClass", "infeasible-owner" -> true;
            default -> cause.startsWith("obs") || cause.startsWith("state+obs");
        };
    }

    /**
     * One escape's view for the pure rule. {@code len0Skipped}: some receiver delivery was the infeasible store into a
     * length-0 array (no holder recorded for it); {@code what}: the escape's label.
     */
    record EscFact(boolean holderFree, List<Object> holders, boolean len0Skipped, String what) {
        EscFact(boolean holderFree, List<Object> holders) {
            this(holderFree, holders, false, "?");
        }
    }

    /**
     * Pure; pinned by JUnit: a walk-based escape whose receiver resolution delivered no holder rests on
     * nothing (the receiver sink ended quietly), so it is an unexplained end; the one sound way to have no holder is that
     * every delivery was skipped as an infeasible store into a length-0 array.
     */
    static boolean escNoHolderUnexplained(EscFact e) {
        return !e.holderFree() && e.holders().isEmpty() && !e.len0Skipped();
    }

    /** One holder's view for the pure rule: its escapes and its unexplained ends (silent ends and undelivered waits). */
    record HolderFacts(List<EscFact> escapes, List<String> unexplained) {
    }

    /** The rule's result: holder-free (no walk-based escape), the holders the claim rests on, the unexplained ends found. */
    record HolderRuleResult(boolean holderFree, int holders, List<String> unexplained) {
        boolean admits() {
            return unexplained.isEmpty();
        }
    }

    /**
     * The "explained holder ends only" rule (pure; pinned by JUnit): the holders the claim rests on are the holders of
     * the walk-based escapes of the STRING atom, closed under the holders of their walk-based escapes; each must have no
     * unexplained end. {@code facts} returns null for an unknown holder (no facts recorded: a complete walk).
     */
    static HolderRuleResult holderRule(List<EscFact> stringEscapes, java.util.function.Function<Object, HolderFacts> facts) {
        java.util.LinkedHashSet<Object> seen = new java.util.LinkedHashSet<>();
        java.util.ArrayDeque<Object> work = new java.util.ArrayDeque<>();
        boolean holderFree = true;
        List<String> unexplained = new ArrayList<>();
        for (EscFact e : stringEscapes) {
            if (!e.holderFree()) {
                holderFree = false;
                if (escNoHolderUnexplained(e)) {
                    unexplained.add("no-holder:" + e.what());
                }
                for (Object h : e.holders()) {
                    if (seen.add(h)) {
                        work.add(h);
                    }
                }
            }
        }
        while (!work.isEmpty()) {
            Object x = work.poll();
            HolderFacts f = facts.apply(x);
            if (f == null) {
                continue;
            }
            for (String u : f.unexplained()) {
                unexplained.add(x + ": " + u);
            }
            for (EscFact e : f.escapes()) {
                if (!e.holderFree()) {
                    if (escNoHolderUnexplained(e)) {
                        unexplained.add(x + ": no-holder:" + e.what());
                    }
                    for (Object h : e.holders()) {
                        if (seen.add(h)) {
                            work.add(h);
                        }
                    }
                }
            }
        }
        return new HolderRuleResult(holderFree, seen.size(), unexplained);
    }

    private static List<EscFact> escFacts(HolderLog h) {
        if (h == null) {
            return List.of();
        }
        List<EscFact> out = new ArrayList<>(h.escapes.size());
        for (EscRec r : h.escapes.values()) {
            out.add(new EscFact(r.holderFree(), new ArrayList<>(r.holders), r.len0Skipped.get(), r.kind + ":" + r.what));
        }
        return out;
    }

    /** A holder's facts: its escapes; its unexplained silent ends; its waits that never delivered and never fell back. */
    private HolderFacts holderFacts(Object key) {
        RAtom x = key != null ? rt.atoms.get(key) : null;
        HolderLog h = x != null ? x.hlog : null;
        if (h == null) {
            return null;
        }
        List<String> un = new ArrayList<>(h.unexplained);
        if (h.unexplainedN.get() > h.unexplained.size()) {
            un.add("(+" + (h.unexplainedN.get() - h.unexplained.size()) + " more)");
        }
        for (WaitRec w : h.waits.values()) {
            String c = waitEndCause(w);
            if (c != null && !soundEndCause(c)) {
                un.add(c + ":" + rt.frameName(w.frame) + (w.on != null ? " on " + w.on : ""));
            }
        }
        java.util.Collections.sort(un);
        return new HolderFacts(escFacts(h), un);
    }

    /**
     * The end cause of a path-less return's wait at quiescence: null = it delivered or fell back; {@code infeasible-owner}
     * (sound) = an OWNER(Y) return where Y is never {@code this} of the frame ({@link #notReceiverOf}: nothing returns
     * along that owner context), or Y exists under no feasible minting context ({@link #atomInfeasible}); otherwise
     * {@code undelivered-<kind>} (unexplained).
     */
    String waitEndCause(WaitRec w) {
        if (w.delivered.get() || w.fell.get()) {
            return null;
        }
        if ("ownerret".equals(w.kind) && ownerInfeasible(w)) {
            return "infeasible-owner";
        }
        return "undelivered-" + w.kind;
    }

    private boolean ownerInfeasible(WaitRec w) {
        return ownerInfeasibleArm(w) != null;
    }

    /** Which arm proves the owner wait infeasible ({@code subtype} / {@code dispatch} / {@code trans}), or null (print: the census). */
    private String ownerInfeasibleArm(WaitRec w) {
        try {
            RAtom y = w.on instanceof RAtomKey k ? rt.atoms.get(k) : null;
            if (y == null) {
                return null;
            }
            String arm = notReceiverArm(y, w.frame);
            return arm != null ? arm : atomInfeasible(y, 0) ? "trans" : null;
        } catch (Throwable e) {
            return null; // unknown: unexplained
        }
    }

    /**
     * Y is never {@code this} of the instance frame: Y's exact class T is not a subtype of the frame method m's declaring
     * class; or T's virtual dispatch of m selects another implementation and every caller of m in the complete IR caller
     * index is an indirect (virtual / interface) invoke and m has no bridged reflective caller, so no
     * direct ({@code invokespecial}) call such as a {@code super.m()} / {@code I.super.m()} or a special accessor can run m
     * on a T. An unknown exact class, {@code java.lang.String} (never exact: custom reps), an incomplete caller index, a bridged
     * caller, or a caller that is not an indirect IR invoke: not proven (false).
     */
    private boolean notReceiverOf(RAtom y, LocalFlowGraph frame) {
        return notReceiverArm(y, frame) != null;
    }

    /** {@link #notReceiverOf} with the arm that proves it: {@code subtype}, {@code dispatch}, or null (not proven). */
    private String notReceiverArm(RAtom y, LocalFlowGraph frame) {
        AnalysisType t = rt.atomExactType(y);
        AnalysisMethod m = rt.bridge.methodOf(frame);
        if (t == null || m == null || m.isStatic() || "java.lang.String".equals(t.toJavaName(true))) {
            return null; // a String's class is never exact (custom reps; as typedStopType / atomExactTypeOf)
        }
        if (!m.getDeclaringClass().isAssignableFrom(t)) {
            return "subtype";
        }
        AnalysisMethod impl = t.resolveConcreteMethod(m, t);
        if (impl == null || impl.equals(m) || rt.containerCallersIncomplete(frame)) {
            return null;
        }
        if (!rt.reflBridge().callersOf(frame).isEmpty()) {
            // A bridged reflective caller (Method.invoke, the SVM invokeSpecial accessor, MethodHandle
            // findSpecial / unreflectSpecial not intrinsified at build time) can run m non-virtually on a T; the IR index
            // does not list it. Any bridged site at all (a site beyond the IR index, or one that the index lists as an
            // indirect pointer call): not proven.
            return null;
        }
        List<Object[]> calls = rt.irCallInvokesOf(frame);
        if (calls == null) {
            return null;
        }
        for (Object[] c : calls) {
            if (!(c[1] instanceof Invoke inv) || !(inv.callTarget() instanceof MethodCallTargetNode mct) || !mct.invokeKind().isIndirect()) {
                return null;
            }
        }
        return "dispatch";
    }

    /**
     * An atom that exists under no feasible minting context: every context it was minted under is OWNER(Z) with Z never
     * {@code this} of the birth frame ({@link #notReceiverOf}) or Z itself infeasible (recursively, depth-capped: at the
     * cap, feasible). Such an atom is never created at run time, so a return wait under it never delivers soundly.
     */
    private boolean atomInfeasible(RAtom y, int depth) {
        if (depth > 8 || y.mintMctxs.isEmpty()) {
            return false;
        }
        for (MethodContext mc : y.mintMctxs) {
            if (mc == null || !mc.isOwner()) {
                return false;
            }
            RAtom z = rt.atoms.get(rt.internKey(mc.ownerSite, mc.ownerCtx));
            if (z == null || !(notReceiverOf(z, y.birthFrame) || atomInfeasible(z, depth + 1))) {
                return false;
            }
        }
        return true;
    }

    /** A quiet escaped STRING atom: no usage, no refusal, at least one escape (with or without a delivered load). */
    private static boolean quietEscaped(RAtom a) {
        return a.kind == AtomKind.STRING && a.strUsages.isEmpty() && !a.table.refused() && a.strEscapes.get() > 0;
    }

    /** {@link #quietEscaped(RAtom)} with the census label {@code wired} (some load delivered). */
    private static boolean quietEscaped(RAtom a, boolean wired) {
        return quietEscaped(a) && a.wiredAnyLoad == wired;
    }

    /**
     * The rule at quiescence: every quiet {@code escape-no-load} STRING atom whose claim rests on a
     * holder walk with an unexplained end is refused {@link RTrackRefusal#HOLDER_END_UNEXPLAINED}. Returns whether it
     * refused anything (the caller drains again: a refusal may fire waiters).
     *
     * <p>The holder-end rule. An
     * {@code escape-no-load} "no usage" admit (a STRING atom with no usage, no refusal, no delivered load and at least
     * one escape) says "the string was stored and never read back". Every escape is one of:
     * <ul>
     * <li>holder-free (proven by an index): a static field, a VM thread-local, a closed field whose read index lists no
     * load site, or a closed field whose escape fell back to every load site of the field;</li>
     * <li>walk-based: an open field, an array element, a model member, a closed field with load sites and no fallback.
     * The "no load" fact then rests on the forward walks of the holders, and recursively on the walks of their own
     * walk-based escapes' holders.</li>
     * </ul>
     * Every recorded holder end the claim rests on must have a sound cause ({@link #soundEndCause}). An unexplained end (a
     * holder's path-less return whose caller set never delivered and never fell back, a return with no analysed caller and
     * no refusal) refuses the STRING atom {@link RTrackRefusal#HOLDER_END_UNEXPLAINED} (REJECT); so does a walk-based
     * escape whose receiver resolution delivered no holder, unless every delivery was the infeasible store into a length-0
     * array. Every quiet escaped STRING atom is judged, with or without a delivered load (one delivered load says nothing
     * about the other escapes). Scope: only the recorded ends; a drop that leaves no record (the visited-key class, the
     * caller-index site drop, the points-to receiver narrowing, typed stops, global drops) is out of scope. Runs only at
     * quiescence (this method).
     */
    boolean holderEndRule() {
        boolean any = false;
        int refusedNow = 0;
        for (RAtom a : new ArrayList<>(rt.atoms.values())) {
            if (!quietEscaped(a)) { // wired atoms too (the rule never uses wiredAnyLoad)
                continue;
            }
            HolderRuleResult r = holderRule(escFacts(a.hlog), this::holderFacts);
            if (!r.admits()) {
                rt.holderEndRefused.add("[sug-fwd-holder-end] " + a.key + (a.wiredAnyLoad ? " wired=true" : "") + " proof=walk holders=" + r.holders() + " verdict=REFUSED unexplained=" +
                                cap(String.valueOf(r.unexplained())));
                rt.refuse(a.table, RTrackRefusal.HOLDER_END_UNEXPLAINED);
                any = true;
                refusedNow++;
            }
        }
        // print-only: when the rule ran and what it refused (the items count is schedule-dependent)
        System.err.println("[sug-fwd-holder-end] rule-round items=" + rt.containerItems.get() + " tripped=" + rt.guardTripped + " refused=" + refusedNow);
        return any;
    }

    /** Print-only: one {@code [sug-fwd-holder-end]} line per quiet escaped (or refused) STRING atom, then a census line. */
    void holderEndCensus() {
        List<String> lines = new ArrayList<>(rt.holderEndRefused);
        for (RAtom a : rt.atoms.values()) {
            for (boolean wired : new boolean[]{false, true}) {
                if (quietEscaped(a, wired)) {
                    HolderRuleResult r = holderRule(escFacts(a.hlog), this::holderFacts);
                    List<String> esc = new ArrayList<>();
                    if (a.hlog != null) {
                        for (EscRec e : a.hlog.escapes.values()) {
                            esc.add(e.kind + ":" + e.what + (e.kind == EscKind.CLOSED ? "(loads=" + e.closedLoads + (e.fell.get() ? ",fell" : "") + ")" : "") +
                                            (e.holderFree() ? "" : "/holders=" + e.holders.size()));
                        }
                    }
                    java.util.Collections.sort(esc);
                    lines.add("[sug-fwd-holder-end] " + a.key + (wired ? " wired=true" : "") + " proof=" + (r.holderFree() ? "idx" : "walk") + " holders=" + r.holders() +
                                    " verdict=" + (r.admits() ? "ok" : "REFUSED") + " escapes=" + esc +
                                    (r.unexplained().isEmpty() ? "" : " unexplained=" + cap(String.valueOf(r.unexplained()))));
                }
            }
        }
        java.util.Collections.sort(lines);
        for (String l : lines) {
            System.out.println(l);
        }
        TreeMap<String, Integer> byCause = new TreeMap<>();
        TreeMap<String, Integer> infeasibleArms = new TreeMap<>();
        int holderAtoms = 0;
        int unexplainedAtoms = 0;
        int undeliveredWaits = 0;
        for (RAtom a : rt.atoms.values()) {
            HolderLog h = a.hlog;
            if (a.kind == AtomKind.STRING || h == null) {
                continue;
            }
            boolean anyEnd = !h.endsByCause.isEmpty();
            for (Map.Entry<String, AtomicInteger> e : h.endsByCause.entrySet()) {
                byCause.merge(e.getKey() + (soundEndCause(e.getKey()) ? "" : "(UNEXPLAINED)"), e.getValue().get(), Integer::sum);
            }
            boolean un = h.unexplainedN.get() > 0;
            for (WaitRec w : h.waits.values()) {
                String c = waitEndCause(w);
                if (c == null) {
                    continue;
                }
                anyEnd = true;
                if ("infeasible-owner".equals(c)) {
                    infeasibleArms.merge(String.valueOf(ownerInfeasibleArm(w)), 1, Integer::sum);
                }
                boolean sound = soundEndCause(c);
                byCause.merge(c + (sound ? "" : "(UNEXPLAINED)"), 1, Integer::sum);
                if (!sound) {
                    if (undeliveredWaits < 8) {
                        System.out.println("[sug-fwd-holder-end] undelivered " + cap(a.key + " " + c + ":" + rt.frameName(w.frame) + (w.on != null ? " on " + w.on : "")));
                    }
                    undeliveredWaits++;
                    un = true;
                }
            }
            holderAtoms += anyEnd ? 1 : 0;
            unexplainedAtoms += un ? 1 : 0;
        }
        System.out.println("[sug-fwd-holder-end] census holderAtomsWithEnds=" + holderAtoms + " unexplainedAtoms=" + unexplainedAtoms +
                        " unexplainedWaits=" + undeliveredWaits + " refusedByRule=" + rt.holderEndRefused.size() + " byCause=" + byCause + " infeasibleArms=" + infeasibleArms);
    }
}
