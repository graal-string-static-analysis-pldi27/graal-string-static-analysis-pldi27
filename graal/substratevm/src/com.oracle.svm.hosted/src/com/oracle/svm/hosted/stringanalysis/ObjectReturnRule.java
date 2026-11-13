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

import static com.oracle.svm.hosted.stringanalysis.ClosedFieldEscape.closedWorldGuard;
import static com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.isIdQuery;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.NAV_OR_UNFRAMED;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.OBJRET;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.OBJRET_CENSUS;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.OBJRET_DELIVER;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.OBJRET_ON;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RETURN_FAN_CAP;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.ROOT_FAN_CAP;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.bump;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.cap;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.restored;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.top;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

import com.oracle.graal.pointsto.heap.ImageHeapConstant;
import com.oracle.graal.pointsto.heap.ImageHeapInstance;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.svm.hosted.stringanalysis.ContainerAtoms.HeapContext;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.EntryList;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Sink;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.CallPath;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.MethodContext;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.WaitRec;
import com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.IdBirthIndex;
import com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.IdPremise;
import com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.IdQuery;
import com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.IdSite;
import com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.PendingSlot;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.AtomKind;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.Counter;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtom;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtomKey;

/**
 * The uniform object-return rule (rule U) of {@link RecursiveTracking} for named classes: the census, the delivery, the
 * nest-navigation census, the self-slot and INLINED_ONLY exceptions and premise G1-N (the pure decisions are in
 * {@link ObjRetRules}).
 */
final class ObjectReturnRule {
    private final RecursiveTracking rt;

    ObjectReturnRule(RecursiveTracking rt) {
        this.rt = rt;
    }

    static boolean isNamedQuery(RAtom a) {
        return a != null && a.key.site instanceof IdSite s && s.named;
    }

    /** The constant (ConstantData) of a CONSTANT atom: its key's site, unwrapped for a heap-birth query atom. */
    static Object constantSiteOf(RAtom a) {
        return a.key.site instanceof IdSite s ? s.site : a.key.site;
    }

    RAtom heapBirthTwin(Object constantData) {
        return rt.heapTwins.get(constantData);
    }

    /** Per class: the named qualification / guard verdict, the cone facts and (when usable) the query atoms. */
    final class NamedQuery {
        final AnalysisType type;
        ObjRetRules.NoQualifyN noq;
        ObjRetRules.GuardFailN fail;
        int cone;
        int exposed;
        int framed;
        int heap;
        String detail = "";
        /** The cone and the exposed set (sorted), kept for the print-only would-be guards. */
        List<AnalysisType> coneL = List.of();
        List<AnalysisType> exposedL = List.of();
        final List<RAtom> atoms = new ArrayList<>();
        /** Nesting depth: 1 + the least depth of a requester (a non-query atom or a parameter sink = 0). */
        final AtomicInteger depth = new AtomicInteger(Integer.MAX_VALUE);
        /** The classes of the trigger frames its own atoms' returns reached (the nesting edges), with their usability. */
        final Map<AnalysisType, Boolean> nested = new ConcurrentHashMap<>();
        final AtomicBoolean started = new AtomicBoolean();
        volatile String first;

        NamedQuery(AnalysisType type) {
            this.type = type;
        }

        boolean usable() {
            return noq == null && fail == null && !atoms.isEmpty();
        }

        String status() {
            return noq != null ? noq.name() : fail != null ? fail.name() : atoms.isEmpty() ? "NO_ATOMS" : "USABLE";
        }
    }

    /** One trigger frame and direction (census). */
    static final class TriggerRec {
        final LocalFlowGraph frame;
        final boolean param;
        /** False: an untriggered STRING return (the ordinary fan does not refuse there), recorded for the census only. */
        final boolean triggered;
        final int callers;
        final boolean outside;
        final String frameNoq;
        final NamedQuery q;
        final AtomicLong strReq = new AtomicLong();
        final AtomicLong otherReq = new AtomicLong();
        final AtomicLong queryReq = new AtomicLong();
        final AtomicLong sinkReq = new AtomicLong();
        /** Why the frame triggers ("fan", "outside", "lookahead F=<witness>"); null = untriggered. */
        volatile String via;
        /** objret=1: the hook events this frame delivered by rule U (census {@code delivered=}). */
        final AtomicLong delivered = new AtomicLong();

        TriggerRec(LocalFlowGraph frame, boolean param, boolean triggered, int callers, boolean outside, String frameNoq, NamedQuery q) {
            this.frame = frame;
            this.param = param;
            this.triggered = triggered;
            this.callers = callers;
            this.outside = outside;
            this.frameNoq = frameNoq;
            this.q = q;
        }
    }

    /**
     * The census event of one path-less return ({@code atom}) or parameter ({@code sink}) out of {@code frame}: rule U's
     * trigger test and, on a trigger, the class query. Print-only.
     */
    private TriggerRec objretCensusEvent(RAtom atom, Sink sink, LocalFlowGraph frame, boolean param) {
        AnalysisMethod m = rt.bridge.methodOf(frame);
        if (m == null || m.isStatic()) {
            return null;
        }
        AnalysisType c = m.getDeclaringClass();
        boolean hidden;
        try {
            Class<?> jc = c.getJavaClass();
            hidden = jc != null && jc.isHidden();
        } catch (Throwable t) {
            return null;
        }
        if (hidden) {
            // The lambda identity rule's domain. Under U a query atom would nest here; counted when that rule already has a usable query
            IdQuery hq = atom != null && isIdQuery(atom) ? rt.idQueries.get(c) : null;
            if (hq != null && hq.usable()) {
                rt.objretHiddenNest.incrementAndGet();
            }
            return null;
        }
        if (rt.containerCallersIncomplete(frame)) {
            return null; // the ordinary MISSING_IR (not a trigger)
        }
        List<ForwardFixpoint.CallerSite> callers = rt.worldTop.fanCallersOf(frame);
        int n = callers == null ? 0 : callers.size();
        boolean outside = rt.worldTop.outsideCaller(frame);
        boolean triggered = n > (param ? ROOT_FAN_CAP : RETURN_FAN_CAP) || outside;
        String via = triggered ? (outside && n <= (param ? ROOT_FAN_CAP : RETURN_FAN_CAP) ? "outside" : "fan") : null;
        if (!triggered && !param) {
            // The lookahead: a certain refusal one pure-forwarder hop below this frame's fan
            String la = lookahead(frame, ObjRetRules.LOOKAHEAD_DEPTH);
            if (la != null) {
                triggered = true;
                via = "lookahead F=" + la;
            }
        }
        if (!triggered && (param || atom == null || atom.kind != AtomKind.STRING || !OBJRET_CENSUS)) {
            return null; // the ordinary rule does not refuse: U does not fire (it only replaces a refusal)
        }
        // (an untriggered return of a STRING atom is recorded too, print-only: what U would give there;
        // census=1 only, so objret=1 alone starts no query for it and spends no budget on it)
        rt.objretEvents.incrementAndGet();
        List<Object> key = List.of(frame, param, triggered);
        TriggerRec r = rt.objretTriggers.get(key);
        if (r == null) {
            boolean nativeOrAddress;
            try {
                nativeOrAddress = m.isNativeEntryPoint() || rt.worldTop.addressTaken().contains(m);
            } catch (Throwable t) {
                nativeOrAddress = true;
            }
            ObjRetRules.FrameNoQualify fnq = ObjRetRules.frameQualifies(false, nativeOrAddress);
            NamedQuery q = fnq == null ? namedQueryOf(c) : null;
            TriggerRec fresh = new TriggerRec(frame, param, triggered, n, outside, fnq == null ? null : fnq.name(), q);
            fresh.via = via;
            r = rt.objretTriggers.putIfAbsent(key, fresh);
            if (r == null) {
                r = fresh;
            }
        }
        if (atom == null) {
            r.sinkReq.incrementAndGet();
        } else if (isIdQuery(atom)) {
            r.queryReq.incrementAndGet();
        } else if (atom.kind == AtomKind.STRING) {
            r.strReq.incrementAndGet();
        } else {
            r.otherReq.incrementAndGet();
        }
        NamedQuery q = r.q;
        int reqDepth = 0;
        if (atom != null && isNamedQuery(atom)) {
            reqDepth = Integer.MAX_VALUE;
            for (NamedQuery o : rt.namedAtomOwners.getOrDefault(atom.key, Set.of())) {
                reqDepth = Math.min(reqDepth, o.depth.get());
                o.nested.merge(c, q != null && q.usable(), Boolean::logicalOr);
            }
            if (reqDepth == Integer.MAX_VALUE) {
                reqDepth = 1;
            }
        } else if (atom != null && isIdQuery(atom)) {
            reqDepth = 1; // a lambda (hidden-class) query atom
        }
        if (q == null || !q.usable()) {
            return r;
        }
        int d = reqDepth + 1;
        q.depth.accumulateAndGet(d, Math::min);
        if (q.started.compareAndSet(false, true)) {
            // the first refusal of any of the cone's query tables (census: the fallback's reason under delivery)
            ObjIdRules.wireUnion(entryListsOfAtoms(q.atoms, frame), l -> List.of("objret-first", q.type, l.table.owner), rt.objectIdentity.registerFeeding(ContainerTables.NO_READER), (list, idx) -> {
            }, (list, ref) -> q.first = ref.name() + "@" + list.table.owner);
            for (RAtom a : q.atoms) {
                rt.schedule(a);
            }
        }
        return r;
    }

    // ------------------------------------------------------------------
    // The delivery of rule U under objret=1. At a triggered frame (fan over the cap, an outside caller, or the lookahead
    // for a return) of a non-hidden class whose named query is usable, the walk continues at the union of the cone
    // births' entry lists (return: returnAtEntry; parameter: the idParameter scheme). The first refusal of any query
    // table, or an empty union at the fixpoint (PRECISE(empty), fail closed), adds the ordinary rule once
    // (returnAllCallers / parameterFan, including its outside-caller refusal); otherwise the ordinary fan does not run.
    // ------------------------------------------------------------------
    /** One delivered hook (the PRECISE(empty) rule reads it at the fixpoint). */
    record ObjretHook(LocalFlowGraph frame, List<EntryList<CallPath>> lists, AtomicBoolean fell, Runnable fallback) {
    }

    private static boolean deliverable(TriggerRec r) {
        return r != null && r.triggered && r.q != null && r.q.usable();
    }

    /** The RETURN hook under objret=1: true = handled by rule U. */
    boolean objretReturn(RAtom atom, LocalFlowGraph frame) {
        TriggerRec r = objretCensusEvent(atom, null, frame, false);
        if (!OBJRET_DELIVER || !deliverable(r) || (isIdQuery(atom) && !isNamedQuery(atom))) {
            return false; // census only, not triggered / unusable, or a lambda (hidden-class) query atom: the ordinary rule
        }
        NamedQuery q = r.q;
        if (rt.containerCallersIncomplete(frame)) {
            rt.refuse(atom.table, RTrackRefusal.MISSING_IR); // as the ordinary rule (the census event already excludes it)
            return true;
        }
        r.delivered.incrementAndGet();
        rt.objretDelivered.incrementAndGet();
        WaitRec wr = rt.holderEnd.waitRec(atom, "objretret", frame, null); // holder-end rule: as the lambda identity return
        List<EntryList<CallPath>> lists = entryListsOfAtoms(q.atoms, frame);
        AtomicBoolean fell = new AtomicBoolean();
        Runnable fallback = () -> {
            if (wr != null) {
                wr.fell.set(true);
            }
            rt.objretFallbacks.incrementAndGet();
            rt.returnAllCallers(atom, frame); // the ordinary rule, once (incl. WORLD_TOP_EXIT for an outside caller)
        };
        ObjIdRules.wireUnion(fell, lists, l -> List.of("objret-ret", atom.key, frame, l.table.owner), rt.objectIdentity.registerFeeding(atom.table), (list, idx) -> {
            if (wr != null) {
                wr.delivered.set(true);
            }
            rt.objretDeliveries.incrementAndGet();
            ContainerTables.markIdDep(atom.table); // T(atom) now reads a rule-U delivery (before the continuation)
            CallPath p = list.get(idx);
            if (p == null) {
                rt.refuse(atom.table, RTrackRefusal.MISSING_IR);
                return;
            }
            rt.objectIdentity.returnAtEntry(atom, frame, p);
        }, (list, ref) -> fallback.run());
        synchronized (rt.objretHooks) {
            rt.objretHooks.add(new ObjretHook(frame, lists, fell, fallback));
        }
        return true;
    }

    /** The PARAMETER hook under objret=1 (no lookahead: fan over the cap or an outside caller): true = handled by rule U. */
    boolean objretParameter(LocalFlowGraph frame, int pidx, MethodContext mctx, Sink sink) {
        TriggerRec r = objretCensusEvent(null, sink, frame, true);
        if (!OBJRET_DELIVER || !deliverable(r)) {
            return false;
        }
        NamedQuery q = r.q;
        if (rt.containerCallersIncomplete(frame)) {
            rt.refuse(sink, RTrackRefusal.MISSING_IR);
            return true;
        }
        r.delivered.incrementAndGet();
        rt.objretDelivered.incrementAndGet();
        if (pidx == 0) {
            ContainerTables.markIdDep(sink); // the receiver's atoms come from rule U
            for (RAtom o : q.atoms) {
                rt.addAtomTo(sink, o.key); // the receiver is a cone object born at one of the births: the query atom itself
            }
        }
        List<EntryList<CallPath>> lists = entryListsOfAtoms(q.atoms, frame);
        AtomicBoolean fell = new AtomicBoolean();
        Runnable fallback = () -> {
            rt.objretFallbacks.incrementAndGet();
            rt.parameterFan(frame, pidx, mctx, sink); // the ordinary rule, once (incl. WORLD_TOP_ENTRY)
        };
        Runnable foldFan = () -> {
            if (fell.compareAndSet(false, true)) {
                fallback.run(); // backward under a recursion fold is path-less = the fan (as idParameter)
            }
        };
        ObjIdRules.wireUnion(fell, lists, l -> List.of("objret-par", sink, frame, pidx, l.table.owner), rt.objectIdentity.registerFeeding(sink), (list, idx) -> {
            if (pidx == 0) {
                return; // the receiver is the query atom itself (added above)
            }
            rt.objretDeliveries.incrementAndGet();
            ContainerTables.markIdDep(sink); // the sink now reads a rule-U delivery
            CallPath p = list.get(idx);
            if (p == null) {
                rt.refuse(sink, RTrackRefusal.MISSING_IR);
                return;
            }
            if (p.isFold()) {
                foldFan.run();
                return;
            }
            if (!rt.beltOk(p, frame)) {
                rt.refuse(sink, RTrackRefusal.BELT);
                return;
            }
            if (rt.models.parameterCase(p, pidx, sink)) {
                return;
            }
            List<ValueNode> args = rt.argumentsAt(p, pidx);
            if (args.isEmpty()) {
                rt.refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
                return;
            }
            for (ValueNode arg : args) {
                rt.backward(p.callerFrame, arg, restored(p.callerMctx), p.next, sink);
            }
        }, (list, ref) -> fallback.run());
        synchronized (rt.objretHooks) {
            rt.objretHooks.add(new ObjretHook(frame, lists, fell, fallback));
        }
        return true;
    }

    /**
     * PRECISE(empty) fails closed: at the fixpoint (a round boundary that decided nothing), every delivered hook whose
     * births' entry lists are all still empty and that has not fallen back runs its fallback (the ordinary rule) once.
     * Returns whether any did. Deterministic: read at quiescence, one-shot per hook.
     */
    boolean objretEmptyRule() {
        if (!OBJRET_DELIVER) {
            return false;
        }
        List<ObjretHook> snap;
        synchronized (rt.objretHooks) {
            snap = new ArrayList<>(rt.objretHooks);
        }
        return ObjIdRules.emptyRule(snap, ObjretHook::fell, h -> {
            int n = 0;
            for (EntryList<CallPath> l : h.lists()) {
                n += l.size();
            }
            return n;
        }, h -> {
            rt.objretEmptyFallbacks.incrementAndGet();
            h.fallback().run();
        });
    }

    /**
     * The lookahead trigger {@code R(M)}: a witness {@code F@bci<reason>} when some site of M's caller fan lies in a frame
     * F where (i) the invoke's result only forwards to F's Returns ({@link ObjRetRules#pureForwarder}) and (ii) F's
     * path-less UNKNOWN-context return refuses for sure ({@link #certainRefusalOf}); null = no such site. The smallest
     * witness by name is answered (schedule-free).
     */
    String lookahead(LocalFlowGraph frame, int depth) {
        if (depth <= 0 || frame == null) {
            return null;
        }
        List<Object> key = List.of(frame, depth);
        String memo = rt.lookaheadMemo.get(key);
        if (memo == null) {
            String r = computeLookahead(frame, depth);
            memo = r == null ? "" : r;
            String prev = rt.lookaheadMemo.putIfAbsent(key, memo);
            if (prev != null) {
                memo = prev;
            } else if (r != null && depth == ObjRetRules.LOOKAHEAD_DEPTH) {
                rt.objretLookaheadFrames.incrementAndGet();
            }
        }
        return memo.isEmpty() ? null : memo;
    }

    private String computeLookahead(LocalFlowGraph frame, int depth) {
        if (rt.containerCallersIncomplete(frame)) {
            return null; // the ordinary rule refuses MISSING_IR at M itself (not a lookahead question)
        }
        List<ForwardFixpoint.CallerSite> callers = rt.worldTop.fanCallersOf(frame);
        if (callers == null || callers.isEmpty() || callers.size() > RETURN_FAN_CAP) {
            return null;
        }
        String best = null;
        for (ForwardFixpoint.CallerSite c : callers) {
            LocalFlowGraph f = c.call() != null ? c.call().owner : null;
            if (f == null) {
                continue;
            }
            boolean fwd = false;
            for (ValueNode inv : rt.invokesOfVertex(f, c.call())) {
                if (ObjRetRules.pureForwarder(inv)) {
                    fwd = true;
                    break;
                }
            }
            if (!fwd) {
                continue;
            }
            String below = certainRefusalOf(f, depth - 1);
            if (below != null) {
                String w = rt.frameName(f) + "@" + c.call().bci + below;
                if (best == null || w.compareTo(best) < 0) {
                    best = w;
                }
            }
        }
        return best;
    }

    /**
     * Lookahead condition (ii): whether a path-less, UNKNOWN-context return of {@code f} refuses under the ordinary rule for every atom:
     * {@code returnCase} reaches {@code idReturn} (false unless f's class is hidden) and then {@code returnAllCallers},
     * which refuses MISSING_IR (callers incomplete), RETURN_FAN_CAP (fan over the cap) or WORLD_TOP_EXIT (outside
     * caller); or recursively the lookahead below f holds. Answers the reason, null = not certain.
     */
    private String certainRefusalOf(LocalFlowGraph f, int depth) {
        AnalysisMethod fm = rt.bridge.methodOf(f);
        if (fm == null) {
            return null;
        }
        boolean hidden;
        try {
            Class<?> jc = fm.isStatic() ? null : fm.getDeclaringClass().getJavaClass();
            hidden = !fm.isStatic() && (jc == null || jc.isHidden());
        } catch (Throwable t) {
            hidden = true; // unreadable: not certain
        }
        boolean incomplete = rt.containerCallersIncomplete(f);
        List<ForwardFixpoint.CallerSite> fc = incomplete ? null : rt.worldTop.fanCallersOf(f);
        int fan = fc == null ? 0 : fc.size();
        boolean outside = rt.worldTop.outsideCaller(f);
        if (ObjRetRules.certainRefusal(hidden, incomplete, fan, RETURN_FAN_CAP, outside, false)) {
            return "(" + (incomplete ? "MISSING_IR" : fan > RETURN_FAN_CAP ? "RETURN_FAN_CAP callers=" + fan : "WORLD_TOP_EXIT") + ")";
        }
        if (hidden || depth <= 0) {
            return null;
        }
        String below = lookahead(f, depth);
        return below != null ? " > " + below : null;
    }

    private static List<EntryList<CallPath>> entryListsOfAtoms(List<RAtom> as, LocalFlowGraph frame) {
        List<EntryList<CallPath>> out = new ArrayList<>(as.size());
        for (RAtom o : as) {
            out.add(o.table.entryPaths(frame));
        }
        return out;
    }

    NamedQuery namedQueryOf(AnalysisType c) {
        NamedQuery q = rt.namedQueries.get(c);
        if (q == null) {
            NamedQuery fresh = computeNamedQuery(c);
            q = rt.namedQueries.putIfAbsent(c, fresh);
            if (q == null) {
                q = fresh;
            }
        }
        return q;
    }

    private static List<AnalysisType> sortedTypes(java.util.Collection<AnalysisType> ts) {
        List<AnalysisType> out = new ArrayList<>(ts);
        out.sort(java.util.Comparator.comparing(t -> t.toJavaName(true)));
        return out;
    }

    private NamedQuery computeNamedQuery(AnalysisType c) {
        NamedQuery q = new NamedQuery(c);
        try {
            AnalysisType str = rt.bridge.lookupJavaType(String.class);
            if (str == null) {
                q.noq = ObjRetRules.NoQualifyN.UNREADABLE;
                return q;
            }
            boolean stringCone = ObjRetRules.stringCone(c, str);
            Set<AnalysisType> subs = new java.util.LinkedHashSet<>(c.getAllSubtypes());
            subs.add(c);
            Set<AnalysisType> cone = new java.util.HashSet<>();
            for (AnalysisType t : subs) {
                if (t.isInstantiated() && !t.isInterface() && !t.isAbstract() && !t.isArray()) {
                    cone.add(t);
                }
            }
            q.noq = ObjRetRules.qualifies(stringCone, cone.isEmpty());
            q.cone = cone.size();
            if (q.noq != null) {
                return q;
            }
            List<AnalysisType> coneSorted = sortedTypes(cone);
            Set<AnalysisType> exposedSet = new java.util.HashSet<>();
            for (AnalysisType t : subs) {
                boolean above = false;
                for (AnalysisType s = t.getSuperclass(); s != null; s = s.getSuperclass()) {
                    above |= cone.contains(s);
                }
                Class<?> jc = t.getJavaClass();
                if (ObjRetRules.exposed(cone.contains(t), jc != null && jc.isSealed(), t.isInterface(), above)) {
                    exposedSet.add(t);
                }
            }
            List<AnalysisType> exposed = sortedTypes(exposedSet);
            q.exposed = exposed.size();
            StringBuilder det = new StringBuilder();
            q.coneL = coneSorted;
            q.exposedL = exposed;
            q.fail = namedGuard(q, coneSorted, exposed, det, false);
            q.detail = det.toString();
            if (q.fail == null) {
                IdBirthIndex x = rt.objectIdentity.idBirthIndex();
                Map<AnalysisType, Set<ImageHeapConstant>> heapObjs = rt.bridge.heapObjects();
                for (AnalysisType t : coneSorted) {
                    for (Object[] b : x.births.getOrDefault(t, List.of())) {
                        LocalFlowGraph bf = (LocalFlowGraph) b[0];
                        ValueNode bn = (ValueNode) b[1];
                        IdSite site = rt.namedSites.computeIfAbsent(rt.siteOf(bf, bn), s -> new IdSite(s, true));
                        RAtomKey key = rt.internKey(site, HeapContext.MERGED);
                        RAtom atom = rt.atoms.computeIfAbsent(key, k -> rt.new RAtom(k, AtomKind.ALLOCATION, bf, bn, MethodContext.UNKNOWN, null, null, false));
                        q.atoms.add(atom);
                    }
                    Set<ImageHeapConstant> hs = heapObjs == null ? null : heapObjs.get(t);
                    if (hs != null) {
                        for (ImageHeapConstant ihc : hs) {
                            Object data = ihc.getConstantData();
                            IdSite site = rt.namedSites.computeIfAbsent(data, s -> new IdSite(s, true));
                            RAtomKey key = rt.internKey(site, HeapContext.EMPTY);
                            RAtom atom = rt.atoms.computeIfAbsent(key, k -> rt.new RAtom(k, AtomKind.CONSTANT, null, null, MethodContext.UNKNOWN, null, ihc, false));
                            rt.heapTwins.putIfAbsent(data, atom);
                            q.atoms.add(atom);
                        }
                    }
                }
                for (RAtom a : q.atoms) {
                    rt.namedAtomOwners.computeIfAbsent(a.key, k -> ConcurrentHashMap.newKeySet()).add(q);
                }
            }
        } catch (Throwable t) {
            q.noq = ObjRetRules.NoQualifyN.UNREADABLE;
            q.detail = "error=" + t.getClass().getSimpleName();
        }
        return q;
    }

    /**
     * The guard of one cone (see {@link ObjRetRules}), computed in the guard's order and stopping at the first failure.
     * {@code useNest} (a print-only would-be variant; false = the plain guard) applies the use-based nest rule and the
     * hub-internal holders it covers.
     */
    private ObjRetRules.GuardFailN namedGuard(NamedQuery q, List<AnalysisType> cone, List<AnalysisType> exposed, StringBuilder det, boolean useNest) {
        if (namedPremise().fails()) {
            return ObjRetRules.GuardFailN.PREMISE;
        }
        boolean vm = false;
        for (Class<?> k : new Class<?>[]{java.lang.ref.Reference.class, Thread.class, Throwable.class}) {
            AnalysisType kt = rt.bridge.lookupJavaType(k);
            for (AnalysisType t : cone) {
                if (kt == null || kt.isAssignableFrom(t)) {
                    vm = true;
                    det.append(" vm=").append(t.toJavaName(true));
                    break;
                }
            }
        }
        if (vm) {
            return ObjRetRules.GuardFailN.VM_REENTRY;
        }
        IdBirthIndex x = rt.objectIdentity.idBirthIndex();
        if (x.failReason != null) {
            det.append(" index=").append(x.failReason);
            return ObjRetRules.GuardFailN.INDEX_FAILED;
        }
        Map<AnalysisType, Set<ImageHeapConstant>> heapObjs = rt.bridge.heapObjects();
        if (heapObjs == null) {
            det.append(" heap=unavailable");
            return ObjRetRules.GuardFailN.INDEX_FAILED;
        }
        String noBirth = null;
        for (AnalysisType t : cone) {
            int f = x.births.getOrDefault(t, List.of()).size();
            q.framed += f;
            Set<ImageHeapConstant> hs = heapObjs.get(t);
            int h = hs == null ? 0 : hs.size();
            q.heap += h;
            if (f + h == 0 && noBirth == null) {
                noBirth = t.toJavaName(true); // a member instantiated through a channel the index cannot see
            }
        }
        det.append(" births=").append(q.framed).append('+').append(q.heap);
        int births = q.framed + q.heap;
        if (births == 0 || births > ObjRetRules.MAX_BIRTHS || noBirth != null) {
            if (noBirth != null && births > 0 && births <= ObjRetRules.MAX_BIRTHS) {
                det.append(" noMemberBirth=").append(noBirth);
            }
            return ObjRetRules.guard(false, false, false, births, noBirth != null, 0, false, false, false, false, false, 0, 0, false, false, 0);
        }
        int unframedMethods = 0;
        boolean unframedBirth = false;
        for (AnalysisType t : exposed) {
            if (x.unframedDeclaring.contains(t)) {
                // A type whose unframed methods are all INLINED_ONLY with every inlining caller
                // framed (inlinedOnlyOk) is discounted; any other cause keeps the guard
                boolean exc = allInlinedOnlyOk(x.unframedMethodsOf.get(t));
                if (!exc) {
                    unframedMethods++;
                }
                det.append(" unframedIn=").append(t.toJavaName(true));
                det.append(x.unframedWhy.getOrDefault(t, List.of()));
                if (exc) {
                    det.append("(inlinedOnly-ok)");
                }
            }
            if (x.unframedBirths.contains(t)) {
                boolean exc = allInlinedOnlyOk(x.unframedBirthMethodsOf.get(t));
                unframedBirth |= !exc;
                det.append(" unframedBirthOf=").append(t.toJavaName(true)).append(x.unframedBirthBy.getOrDefault(t, List.of()));
                if (exc) {
                    det.append("(inlinedOnly-ok)");
                }
            }
        }
        boolean unwalkable = false;
        for (AnalysisType t : cone) {
            unwalkable |= x.unwalkableBirths.contains(t);
        }
        if (unframedMethods > 0 || unframedBirth || unwalkable) {
            return ObjRetRules.guard(false, false, false, births, false, unframedMethods, unframedBirth, unwalkable, false, false, false, 0, 0, false, false, 0);
        }
        if (useNest) {
            // Print-only would-be: the use-based nest rule replaces NEST_EXPOSED and CONE_ARRAY
            String nav = navReach(exposed);
            if (nav != null) {
                det.append(" navUse=").append(nav);
                return ObjRetRules.GuardFailN.NEST_EXPOSED;
            }
        } else {
            String nest = nestExposure(exposed);
            if (nest != null) {
                det.append(" nest=").append(nest);
                return ObjRetRules.GuardFailN.NEST_EXPOSED;
            }
            String arr = coneArray(exposed);
            if (arr != null) {
                det.append(" array=").append(arr);
                return ObjRetRules.GuardFailN.CONE_ARRAY;
            }
        }
        String csm = coneCsm(exposed);
        if (csm != null) {
            det.append(" csm=").append(csm);
            return ObjRetRules.GuardFailN.CONE_CSM;
        }
        int consts = 0;
        for (AnalysisType t : exposed) {
            consts += x.harmfulClassConstants.getOrDefault(t, 0);
        }
        if (consts > 0) {
            det.append(" consts=").append(consts);
            if (OBJRET_ON) {
                for (AnalysisType t : exposed) {
                    List<String> cs = x.harmfulClassConstantSites.get(t);
                    if (cs != null) {
                        det.append(" constsOf(").append(t.toJavaName(true)).append(")=").append(cs);
                    }
                }
            }
            return ObjRetRules.GuardFailN.CLASS_CONSTANT;
        }
        int holders = 0;
        for (AnalysisType t : exposed) {
            String[] hd = new String[1];
            int h = useNest ? classHoldersUseBased(t, hd, false) : classHoldersSelfSlot(t, hd); // the self-slot exception
            if (h > 0) {
                holders += h;
                det.append(" holders(").append(t.toJavaName(true)).append(")=").append(h).append(hd[0] != null ? hd[0] : "");
            }
        }
        if (holders > 0) {
            return ObjRetRules.GuardFailN.CLASS_HOLDER;
        }
        String reg = null;
        for (AnalysisType t : exposed) {
            String why = rt.objectIdentity.namedRegistryReason(t);
            if (why != null) {
                reg = t.toJavaName(true) + ":" + why;
                break;
            }
        }
        if (reg == null) {
            reg = linkedRegistration(exposed);
        }
        if (reg != null) {
            det.append(" reg=").append(reg);
            return ObjRetRules.GuardFailN.REGISTERED;
        }
        Set<Class<?>> meta = metadataClasses();
        for (AnalysisType t : exposed) {
            Class<?> jc = t.getJavaClass();
            if (meta == null || jc == null || meta.contains(jc)) {
                det.append(" metadata=").append(meta == null ? "unavailable(" + rt.metadataProblem + ")" : t.toJavaName(true));
                return ObjRetRules.GuardFailN.METADATA_TYPE;
            }
        }
        int pending = 0;
        for (AnalysisType t : cone) {
            StringBuilder pd = new StringBuilder();
            pending += rt.objectIdentity.pendingCheck(t, pd);
            if (pd.length() > 0 && pending > 0) {
                det.append(" pending=").append(pd);
                break;
            }
        }
        if (pending > 0) {
            return ObjRetRules.GuardFailN.PENDING_SLOT;
        }
        return null;
    }

    /**
     * NEST_EXPOSED (fail closed): some exposed type T has an incoming hub-data link ({@link ObjRetRules#hubNavLink}:
     * N.getNestHost(), getDeclaringClass(), getEnclosingClass() == T) from a type N != T in the reverse index
     * ({@link #navIndex}), so any Class object of N leads to T. Null = none; an unreadable index or class answers a reason.
     */
    private String nestExposure(List<AnalysisType> exposed) {
        NavIndex ix = navIndex();
        if (ix.problem != null) {
            return "unreadable:" + ix.problem;
        }
        for (AnalysisType t : exposed) {
            Class<?> tc = t.getJavaClass();
            if (tc == null) {
                return "noClass:" + t.toJavaName(true);
            }
            for (NavLinkRec l : ix.links.getOrDefault(tc, List.of())) {
                if (ObjRetRules.hubNavLink(l.kind()) && !l.n().equals(t)) {
                    return l.n().toJavaName(true) + "." + l.kind() + "->" + t.toJavaName(true);
                }
            }
        }
        return null;
    }

    // ------------------------------------------------------------------
    // Print-only, census mode: the nest-navigation use census (every reachable call of a Class navigation API,
    // ObjRetRules.NAV_APIS, with its receiver's source and its result's uses, plus the reflective / method-handle routes).
    // Nothing here is a verdict input.
    // ------------------------------------------------------------------
    /** One link: a Class object of {@code n} leads to the target type through {@code kind}. */
    record NavLinkRec(AnalysisType n, ObjRetRules.NavLink kind) {
    }

    /** One navigation call site (or an unreadable position). */
    static final class NavSite {
        String pos;
        String api;
        /** CONST / GETCLASS / UNKNOWN(kind). */
        String recv;
        AnalysisType recvType;
        boolean harmless;
        boolean exempt;
        String why;

        String line() {
            return "[objret-navsite] pos=" + pos + " api=" + api + " recv=" + recv + (recvType != null ? "(" + recvType.toJavaName(true) + ")" : "") + " uses=" +
                            (exempt ? "exempt(family:" + (harmless ? "harmless" : why) + ")" : harmless ? "harmless" : "HARMFUL(" + why + ")");
        }
    }

    static final class NavCensus {
        String problem;
        final List<NavSite> sites = new ArrayList<>();
        final Set<String> reflective = new java.util.TreeSet<>();
        final Map<Class<?>, List<NavLinkRec>> links = new java.util.HashMap<>();
        int types;
        long ms;
    }

    /**
     * The reverse navigation index over every type with a hub in the snapshot plus every declaring class of a reachable
     * method (hidden and pre-11 classes included): per target class, the links that lead to it
     * ({@link ObjRetRules#navLinksOf}). Any reflection failure sets {@code problem} (every class then fails NEST_EXPOSED /
     * CONE_ARRAY: fail closed).
     */
    static final class NavIndex {
        String problem;
        final Map<Class<?>, List<NavLinkRec>> links = new java.util.HashMap<>();
        final Set<AnalysisType> types = new java.util.HashSet<>();
        final List<AnalysisMethod> reachable = new ArrayList<>();
        long ms;
    }

    private NavIndex navIndex() {
        NavIndex x = rt.navIndex;
        if (x == null) {
            synchronized (rt.idSites) {
                x = rt.navIndex;
                if (x == null) {
                    x = buildNavIndex();
                    rt.navIndex = x;
                }
            }
        }
        return x;
    }

    private NavIndex buildNavIndex() {
        long t0 = System.nanoTime();
        NavIndex ix = new NavIndex();
        AnalysisType cur = null;
        try {
            jdk.vm.ci.meta.MetaAccessProvider host = com.oracle.graal.pointsto.util.GraalAccess.getOriginalProviders().getMetaAccess();
            rt.objectIdentity.hubConstantData(rt.bridge.lookupJavaType(Object.class));
            if (rt.hubConstantsFailed || rt.hubConstants == null) {
                ix.problem = "hubs-unavailable";
                return ix;
            }
            ix.types.addAll(rt.hubConstants.keySet());
            for (AnalysisMethod m : rt.bridge.universeMethods()) {
                if (m.isReachable() || m.isImplementationInvoked()) {
                    ix.reachable.add(m);
                    ix.types.add(m.getDeclaringClass());
                }
            }
            java.util.function.Function<Class<?>, AnalysisType> lookup = k -> rt.bridge.optionalAnalysisType(host.lookupJavaType(k));
            for (AnalysisType n : sortedTypes(ix.types)) {
                cur = n;
                ObjRetRules.navLinksOf(n.getJavaClass(), n, lookup, (target, from, kind) -> ix.links.computeIfAbsent(target, k -> new ArrayList<>()).add(new NavLinkRec(from, kind)));
            }
        } catch (Throwable t) {
            ix.problem = "error:" + t.getClass().getSimpleName() + (cur != null ? "@" + cur.toJavaName(true) : "");
        } finally {
            ix.ms = (System.nanoTime() - t0) / 1_000_000;
        }
        return ix;
    }

    private static boolean isNavApi(ResolvedJavaMethod t) {
        return t != null && !t.isStatic() && ObjRetRules.NAV_APIS.contains(t.getName()) && ObjRetRules.classHolder(t.getDeclaringClass().toJavaName(true));
    }

    private NavCensus navCensus() {
        NavCensus c = rt.navCensus;
        if (c == null) {
            synchronized (rt.idSites) {
                c = rt.navCensus;
                if (c == null) {
                    c = buildNavCensus();
                    rt.navCensus = c;
                }
            }
        }
        return c;
    }

    private NavCensus buildNavCensus() {
        long t0 = System.nanoTime();
        NavCensus nc = new NavCensus();
        try {
            // (1) the reverse link index (the production index, navIndex)
            NavIndex ix = navIndex();
            if (ix.problem != null) {
                nc.problem = ix.problem;
                return nc;
            }
            List<AnalysisMethod> reachable = ix.reachable;
            nc.types = ix.types.size();
            nc.links.putAll(ix.links);
            // (2) the reflective and method-handle routes: a registered navigation executable, a root, a heap MemberName
            if (org.graalvm.nativeimage.ImageSingletons.contains(com.oracle.svm.hosted.reflect.ReflectionHostedSupport.class)) {
                var rs = org.graalvm.nativeimage.ImageSingletons.lookup(com.oracle.svm.hosted.reflect.ReflectionHostedSupport.class);
                for (var e : rs.getReflectionExecutables().entrySet()) {
                    for (AnalysisMethod am : e.getValue().keySet()) {
                        if (isNavApi(am.getWrapped()) || isNavApi(am)) {
                            nc.reflective.add("registered:" + am.getName());
                        }
                    }
                }
            } else {
                nc.reflective.add("reflection-registry-unavailable");
            }
            for (AnalysisMethod m : reachable) {
                if (isNavApi(m.getWrapped()) && (m.isDirectRootMethod() || m.isVirtualRootMethod())) {
                    nc.reflective.add("root:" + m.getName());
                }
            }
            Map<AnalysisType, Set<ImageHeapConstant>> objs = rt.bridge.heapObjects();
            Class<?> mnClass = Class.forName("java.lang.invoke.MemberName");
            AnalysisType mnType = rt.bridge.lookupJavaType(mnClass);
            if (objs == null) {
                nc.reflective.add("heap-unavailable");
            } else if (mnType != null && objs.get(mnType) != null) {
                for (ImageHeapConstant k : objs.get(mnType)) {
                    JavaConstant hc = k.getHostedObject();
                    Object mn = hc != null ? com.oracle.graal.pointsto.util.GraalAccess.getOriginalSnippetReflection().asObject(Object.class, hc) : null;
                    try {
                        Object name = com.oracle.svm.util.ReflectionUtil.readField(mnClass, "name", mn);
                        Object clazz = com.oracle.svm.util.ReflectionUtil.readField(mnClass, "clazz", mn);
                        if (clazz == Class.class && ObjRetRules.NAV_APIS.contains(String.valueOf(name))) {
                            nc.reflective.add("heapMemberName:" + name);
                        }
                    } catch (Throwable e) {
                        nc.reflective.add("heapMemberName:unreadable");
                    }
                }
            }
            // (3) the call sites (positions from the analysis invokes, keyed by the method, never by name)
            Map<AnalysisMethod, Boolean> positions = new java.util.LinkedHashMap<>();
            for (AnalysisMethod m : reachable) {
                List<Object[]> sites = rt.bridge.invokeSites(m);
                if (sites == null) {
                    continue;
                }
                for (Object[] site : sites) {
                    ResolvedJavaMethod tgt = hostOf(site[0]);
                    if (!isNavApi(tgt)) {
                        continue;
                    }
                    if (!(site[1] instanceof AnalysisMethod pm)) {
                        NavSite ns = new NavSite();
                        ns.pos = "unpositioned@" + site[2];
                        ns.api = tgt.getName();
                        ns.recv = "UNKNOWN(unpositioned)";
                        ns.why = "unpositioned";
                        nc.sites.add(ns);
                        continue;
                    }
                    positions.putIfAbsent(pm, Boolean.TRUE);
                }
            }
            for (AnalysisMethod pm : positions.keySet()) {
                String pn = pm.format("%H.%n(%p)");
                boolean exempt = isNavApi(pm.getWrapped());
                LocalFlowGraph fr = rt.bridge.frameOf(pm);
                StructuredGraph g = fr != null ? rt.graphOf(fr) : null;
                if (g == null) {
                    NavSite ns = new NavSite();
                    ns.pos = pn;
                    ns.api = "?";
                    ns.recv = "UNKNOWN(no-ir)";
                    ns.why = "no-ir";
                    ns.exempt = exempt;
                    nc.sites.add(ns);
                    continue;
                }
                int matched = 0;
                for (Invoke inv : g.getInvokes()) {
                    ResolvedJavaMethod tgt = hostOf(inv.getTargetMethod());
                    if (!isNavApi(tgt)) {
                        continue;
                    }
                    matched++;
                    NavSite ns = new NavSite();
                    ns.pos = pn + "@" + inv.bci();
                    ns.api = tgt.getName();
                    ns.exempt = exempt;
                    ValueNode r = inv.callTarget() instanceof MethodCallTargetNode mct && !mct.arguments().isEmpty() ? mct.arguments().get(0) : null;
                    navReceiver(ns, r);
                    String[] why = new String[1];
                    ns.harmless = "isNestmateOf".equals(ns.api) || harmlessClassUses(inv.asNode(), why);
                    ns.why = why[0];
                    nc.sites.add(ns);
                }
                if (matched == 0) {
                    NavSite ns = new NavSite();
                    ns.pos = pn;
                    ns.api = "?";
                    ns.recv = "UNKNOWN(not-in-ir)";
                    ns.why = "not-in-ir";
                    ns.exempt = exempt;
                    nc.sites.add(ns);
                }
            }
            nc.sites.sort(java.util.Comparator.comparing(NavSite::line));
        } catch (Throwable t) {
            StackTraceElement[] st = t.getStackTrace();
            nc.problem = "error:" + t.getClass().getSimpleName() + (st.length > 0 ? "@" + st[0] + (st.length > 1 ? "<" + st[1] : "") : "");
        } finally {
            nc.ms = (System.nanoTime() - t0) / 1_000_000;
        }
        return nc;
    }

    /** The receiver's source: a Class constant, the getClass()/hub of a value with a stamp, or unknown (any class). */
    private void navReceiver(NavSite ns, ValueNode r0) {
        ValueNode r = r0;
        while (r instanceof PiNode pi) {
            r = pi.getOriginalNode();
        }
        try {
            if (r instanceof ConstantNode cn && cn.getValue() instanceof JavaConstant jc) {
                AnalysisType t = rt.bridge.classConstantType(jc);
                if (t != null) {
                    ns.recv = "CONST";
                    ns.recvType = t;
                    return;
                }
            }
            ValueNode obj = r instanceof jdk.graal.compiler.nodes.extended.GetClassNode gc ? gc.getObject() : r instanceof jdk.graal.compiler.nodes.extended.LoadHubNode lh ? lh.getValue() : null;
            if (obj != null) {
                ResolvedJavaType st = jdk.graal.compiler.nodes.type.StampTool.typeOrNull(obj);
                ns.recv = "GETCLASS";
                ns.recvType = st == null ? null : st instanceof AnalysisType at ? at : rt.bridge.optionalAnalysisType(st);
                if (st != null && ns.recvType == null) {
                    ns.recv = "UNKNOWN(stamp-unresolved)";
                }
                return;
            }
        } catch (Throwable t) {
            // fall through: unknown
        }
        ns.recv = "UNKNOWN(" + (r == null ? "null" : r.getClass().getSimpleName()) + ")";
    }

    /** Whether a navigation site may receive a Class object of {@code n}. */
    private static boolean navCanReceive(NavSite s, AnalysisType n) {
        if ("CONST".equals(s.recv)) {
            return s.recvType != null && s.recvType.equals(n);
        }
        if ("GETCLASS".equals(s.recv)) {
            return s.recvType == null || s.recvType.isAssignableFrom(n);
        }
        return true;
    }

    /**
     * The use-based nest rule (print-only would-be): a harmful navigation site whose API follows a link of an exposed type
     * and whose receiver may be that link's class, or a reflective / method-handle route to such an API; null = none.
     */
    private String navReach(List<AnalysisType> exposed) {
        NavCensus nc = navCensus();
        if (nc.problem != null) {
            return "unreadable:" + nc.problem;
        }
        for (AnalysisType t : exposed) {
            Class<?> tc = t.getJavaClass();
            if (tc == null) {
                return "noClass:" + t.toJavaName(true);
            }
            for (NavLinkRec l : nc.links.getOrDefault(tc, List.of())) {
                Set<String> apis = ObjRetRules.navApis(l.kind());
                for (String r : nc.reflective) {
                    if (r.contains("unavailable") || r.contains("unreadable") || apis.contains(r.substring(r.indexOf(':') + 1))) {
                        return "reflective:" + r + " link=" + l.n().toJavaName(true) + "." + l.kind() + "->" + t.toJavaName(true);
                    }
                }
                for (NavSite s : nc.sites) {
                    if (s.exempt || s.harmless) {
                        continue;
                    }
                    if (("?".equals(s.api) || apis.contains(s.api)) && navCanReceive(s, l.n())) {
                        return s.pos + "#" + s.api + " recv=" + s.recv + (s.recvType != null ? "(" + s.recvType.toJavaName(true) + ")" : "") + " link=" + l.n().toJavaName(true) + "." +
                                        l.kind() + "->" + t.toJavaName(true);
                    }
                }
            }
        }
        return null;
    }

    /** The number of distinct harmful sites (and reflective routes) that reach some link of an exposed type (print-only). */
    private int navReachCount(List<AnalysisType> exposed) {
        NavCensus nc = navCensus();
        if (nc.problem != null) {
            return -1;
        }
        Set<Object> hit = new java.util.HashSet<>();
        for (AnalysisType t : exposed) {
            Class<?> tc = t.getJavaClass();
            for (NavLinkRec l : tc == null ? List.<NavLinkRec> of() : nc.links.getOrDefault(tc, List.of())) {
                Set<String> apis = ObjRetRules.navApis(l.kind());
                for (String r : nc.reflective) {
                    if (r.contains("unavailable") || r.contains("unreadable") || apis.contains(r.substring(r.indexOf(':') + 1))) {
                        hit.add(r);
                    }
                }
                for (NavSite s : nc.sites) {
                    if (!s.exempt && !s.harmless && ("?".equals(s.api) || apis.contains(s.api)) && navCanReceive(s, l.n())) {
                        hit.add(s);
                    }
                }
            }
        }
        return hit.size();
    }

    /** The links of the exposed types, counted per kind (print-only). */
    private String navLinkSummary(List<AnalysisType> exposed) {
        NavCensus nc = navCensus();
        Map<String, Counter> by = new TreeMap<>();
        for (AnalysisType t : exposed) {
            Class<?> tc = t.getJavaClass();
            for (NavLinkRec l : tc == null ? List.<NavLinkRec> of() : nc.links.getOrDefault(tc, List.of())) {
                bump(by, l.kind().name());
            }
        }
        return top(by);
    }

    /** The hub type owning a DynamicHubCompanion (hosted identity), built once over the snapshot's hubs; null = unavailable. */
    private Map<Object, AnalysisType> companionOwners() {
        Map<Object, AnalysisType> m = rt.companionOwners;
        if (m == null) {
            synchronized (rt.idSites) {
                m = rt.companionOwners;
                if (m == null) {
                    m = new java.util.IdentityHashMap<>();
                    try {
                        Map<AnalysisType, Set<ImageHeapConstant>> objs = rt.bridge.heapObjects();
                        AnalysisType classType = rt.bridge.lookupJavaType(Class.class);
                        for (ImageHeapConstant k : objs.get(classType)) {
                            AnalysisType t = rt.bridge.classConstantType(k);
                            JavaConstant hc = k.getHostedObject();
                            Object hub = hc != null ? com.oracle.graal.pointsto.util.GraalAccess.getOriginalSnippetReflection().asObject(Object.class, hc) : null;
                            if (t != null && hub instanceof com.oracle.svm.core.hub.DynamicHub dh) {
                                m.put(dh.getCompanion(), t);
                            }
                        }
                    } catch (Throwable t) {
                        m = null;
                    }
                    rt.companionOwners = m == null ? java.util.Collections.emptyMap() : m;
                    if (m == null) {
                        return null;
                    }
                }
            }
        }
        return m.isEmpty() ? null : m;
    }

    /**
     * CLASS_HOLDER under the use-based nest rule (print-only would-be; after {@link #navReach} found no harmful route): a
     * hub-internal navigation slot ({@link ObjRetRules#navHolderSlot}) is discounted when its owner is T itself or its
     * owner's link to T is in the reverse index. Every other holder counts, as in {@link ObjectIdentityRule#classHolders}.
     */
    private int classHoldersUseBased(AnalysisType c, String[] detail, boolean selfOnly) {
        int all = rt.objectIdentity.classHolders(c, detail);
        Object hub = rt.objectIdentity.hubConstantData(c);
        Map<Object, List<Object[]>> idx = hub == null ? null : rt.holderIndex();
        if (all == 0 || hub == null || idx == null || rt.holderIndexProblem != null) {
            return all;
        }
        Map<Object, AnalysisType> owners = companionOwners();
        Class<?> tc = c.getJavaClass();
        List<NavLinkRec> links = tc == null || selfOnly ? List.of() : navCensus().links.getOrDefault(tc, List.of());
        int kept = 0;
        int discounted = 0;
        StringBuilder sb = new StringBuilder();
        for (Object[] h : idx.getOrDefault(hub, List.of())) {
            String ht = h[0] instanceof ImageHeapConstant ihc && ihc.getType() instanceof AnalysisType t ? t.toJavaName(true) : "?";
            String fn = h[1] instanceof AnalysisField f ? f.getName() : String.valueOf(h[1]);
            AnalysisType owner = null;
            if (h[0] instanceof ImageHeapConstant ihc && ihc.getHostedObject() != null) {
                Object o = com.oracle.graal.pointsto.util.GraalAccess.getOriginalSnippetReflection().asObject(Object.class, ihc.getHostedObject());
                owner = o instanceof com.oracle.svm.core.hub.DynamicHub ? rt.bridge.classConstantType(ihc) : owners != null ? owners.get(o) : null;
            }
            boolean ok = false;
            if (ObjRetRules.navHolderSlot(ht, fn) && owner != null) {
                ObjRetRules.NavLink want = "nestHost".equals(fn) ? ObjRetRules.NavLink.NEST_HOST : "declaringClass".equals(fn) ? ObjRetRules.NavLink.DECLARING : ObjRetRules.NavLink.COMPONENT;
                ok = owner.equals(c);
                for (NavLinkRec l : links) {
                    ok |= l.n().equals(owner) && l.kind() == want;
                }
            }
            if (ok) {
                discounted++;
            } else {
                kept++;
                if (kept <= 4) {
                    sb.append(kept == 1 ? "" : ",").append(ht.substring(ht.lastIndexOf('.') + 1)).append('.').append(fn).append(owner != null ? "@" + owner.toJavaName(true) : "");
                }
            }
        }
        detail[0] = (selfOnly ? " selfHolders=" : " navHolders=") + discounted + " otherHolders=[" + sb + "]";
        return kept;
    }

    // ------------------------------------------------------------------
    // The self-slot CLASS_HOLDER exception.
    // ------------------------------------------------------------------
    /** The image-level facts of the self-slot check (computed once). */
    static final class SelfSlotImage {
        AnalysisField companionField;
        AnalysisField nestHostField;
        AnalysisType companionType;
        boolean pendingOk;
        boolean readersOk;
        boolean buildOk;
        String why = "";
    }

    private SelfSlotImage selfSlotImage() {
        SelfSlotImage si = rt.selfSlotImage;
        if (si != null) {
            return si;
        }
        // built outside the idSites monitor (holderIndex() takes this engine's monitor: no nested lock order)
        Map<Object, List<Object[]>> hidx = rt.holderIndex();
        IdBirthIndex x = rt.objectIdentity.idBirthIndex();
        synchronized (rt.idSites) {
            if (rt.selfSlotImage != null) {
                return rt.selfSlotImage;
            }
            si = new SelfSlotImage();
            try {
                AnalysisType hubType = rt.bridge.lookupJavaType(com.oracle.svm.core.hub.DynamicHub.class);
                si.companionType = rt.bridge.lookupJavaType(com.oracle.svm.core.hub.DynamicHubCompanion.class);
                si.companionField = instanceField(hubType, "companion");
                si.nestHostField = instanceField(si.companionType, ObjRetRules.NEST_HOST_FIELD);
                si.buildOk = closedWorldGuard() == null && si.companionField != null && si.nestHostField != null;
                if (!si.buildOk) {
                    si.why += "mode:" + closedWorldGuard() + (si.companionField == null || si.nestHostField == null ? "/fields" : "") + ";";
                }
                // Every pending READ slot kind that may hold a companion must be on the allow-list
                si.pendingOk = hidx != null && rt.holderIndexProblem == null && si.companionType != null;
                for (PendingSlot ps : new ArrayList<>(rt.pendingSlots.values())) {
                    if (ObjIdRules.mayHold(rt.objectIdentity.closureOf(ps), si.companionType) && ObjIdRules.pendingAllow(ps.where) == null) {
                        si.pendingOk = false;
                        si.why += "pending:" + ps.where + ";";
                    }
                }
                // The run-time readers (the birth index scan)
                si.readersOk = x.failReason == null && x.companionReaders.isEmpty();
                if (!si.readersOk) {
                    List<String> rl = new ArrayList<>(x.companionReaders);
                    si.why += "readers:" + (x.failReason != null ? x.failReason : rl.size() + String.valueOf(rl.subList(0, Math.min(6, rl.size())))) + ";";
                }
            } catch (Throwable t) {
                si.buildOk = false;
                si.why += "error:" + t.getClass().getSimpleName() + ";";
            }
            rt.selfSlotImage = si;
            return si;
        }
    }

    private AnalysisField instanceField(AnalysisType t, String name) {
        if (t == null) {
            return null;
        }
        for (ResolvedJavaField rf : t.getInstanceFields(true)) {
            if (name.equals(rf.getName())) {
                return rt.bridge.resolveField(rf);
            }
        }
        return null;
    }

    /** T's hub object in the snapshot (the Class constant whose type is T), or null. */
    private ImageHeapConstant hubObjectOf(AnalysisType c) {
        Map<AnalysisType, ImageHeapConstant> m = rt.hubObjects;
        if (m == null) {
            synchronized (rt.idSites) {
                m = rt.hubObjects;
                if (m == null) {
                    m = new java.util.HashMap<>();
                    Map<AnalysisType, Set<ImageHeapConstant>> objs = rt.bridge.heapObjects();
                    AnalysisType classType = rt.bridge.lookupJavaType(Class.class);
                    try {
                        if (objs != null && classType != null && objs.get(classType) != null) {
                            for (ImageHeapConstant k : objs.get(classType)) {
                                AnalysisType t = rt.bridge.classConstantType(k);
                                if (t != null) {
                                    m.put(t, k);
                                }
                            }
                        }
                    } catch (Throwable t) {
                        m.clear(); // no hub object: no discount (fail closed)
                    }
                    rt.hubObjects = m;
                }
            }
        }
        return m.get(c);
    }

    /**
     * CLASS_HOLDER with the self-slot exception: {@link ObjectIdentityRule#classHolders} minus the holder records that
     * {@link ObjRetRules#selfSlotDiscount} accepts: the record is {@code (T's own companion, DynamicHubCompanion.nestHost)},
     * where T's own companion is the non-pending value of T's hub field {@code DynamicHub.companion}, T's hub is its only
     * holder in the snapshot index, and the image-level checks hold (pending kinds, run-time readers, build mode). Every
     * other holder (another class's nestHost / declaringClass, arrayHub, componentType, ...) counts.
     */
    private int classHoldersSelfSlot(AnalysisType c, String[] detail) {
        int all = rt.objectIdentity.classHolders(c, detail);
        Object hubCD = rt.objectIdentity.hubConstantData(c);
        Map<Object, List<Object[]>> idx = hubCD == null ? null : rt.holderIndex();
        if (all == 0 || hubCD == null || idx == null || rt.holderIndexProblem != null) {
            return all;
        }
        SelfSlotImage si = selfSlotImage();
        ImageHeapConstant hub = hubObjectOf(c);
        Object compCD = null;
        if (hub instanceof ImageHeapInstance hi && si.companionField != null) {
            try {
                Object v = hi.getFieldValue(si.companionField);
                if (v instanceof ImageHeapConstant ic) {
                    compCD = ic.getConstantData(); // a non-pending constant only
                }
            } catch (Throwable t) {
                compCD = null;
            }
        }
        boolean sole = false;
        if (compCD != null) {
            List<Object[]> hs = idx.get(compCD);
            sole = hs != null && hs.size() == 1 && hs.get(0)[0] instanceof ImageHeapConstant h0 && hubCD.equals(h0.getConstantData()) && hs.get(0)[1] == si.companionField;
        }
        int kept = 0;
        int disc = 0;
        String refused = null;
        for (Object[] h : idx.getOrDefault(hubCD, List.of())) {
            String ht = h[0] instanceof ImageHeapConstant ihc && ihc.getType() instanceof AnalysisType t ? t.toJavaName(true) : "?";
            String fn = h[1] instanceof AnalysisField f ? f.getName() : String.valueOf(h[1]);
            boolean isTs = compCD != null && h[0] instanceof ImageHeapInstance hi2 && compCD.equals(hi2.getConstantData()) && h[1] == si.nestHostField;
            if (ObjRetRules.selfSlotDiscount(ht, fn, isTs, sole, si.pendingOk, si.readersOk, si.buildOk)) {
                disc++;
            } else {
                kept++;
                if (isTs && refused == null) {
                    refused = !sole ? "sole" : !si.pendingOk ? "pending" : !si.readersOk ? "reader" : "mode";
                }
            }
        }
        rt.selfSlotOutcome.put(c, disc > 0 ? "discounted" : refused != null ? refused : "none");
        detail[0] = (detail[0] == null ? "" : detail[0]) + " selfSlot=" + disc + (refused != null ? "(refused:" + refused + ")" : "");
        return kept;
    }

    /** The census token {@code selfSlot{classes={discounted|sole|pending|reader|mode|none=n} …}} (per class with a holder). */
    private String selfSlotCensus() {
        Map<String, Counter> by = new TreeMap<>();
        for (String o : rt.selfSlotOutcome.values()) {
            bump(by, o);
        }
        SelfSlotImage si = rt.selfSlotImage;
        return " selfSlot{classes=" + top(by) + " pendingOk=" + (si != null && si.pendingOk) + " readersOk=" + (si != null && si.readersOk) + " buildOk=" + (si != null && si.buildOk) +
                        " why=" + (si != null ? cap(si.why) : "unbuilt") + " companionReads=" + (rt.idBirthIndex != null ? rt.idBirthIndex.companionReads : -1) + "}";
    }

    // ------------------------------------------------------------------
    // The INLINED_ONLY exception, from a bytecode caller index.
    // ------------------------------------------------------------------
    /** One invoke site of the bytecode caller index. */
    record ByteSite(AnalysisMethod caller, ResolvedJavaType holder, int opcode) {
    }

    static final class InlinedIndex {
        /** name + descriptor -> the invoke sites. */
        final Map<String, List<ByteSite>> sites = new java.util.HashMap<>();
        /**
         * The methods holding an {@code invokedynamic} or a signature-polymorphic MethodHandle invoke
         * ({@link ObjRetRules#methodHandleInvoker}): a constant MethodHandle / call site can be intrinsified there into a
         * direct call of any method without a bytecode invoke naming it, so each is a caller of every INLINED_ONLY method.
         */
        final Set<AnalysisMethod> wildcard = new java.util.LinkedHashSet<>();
        /** The CLINIT exception: the dead class initializers scanned although unreachable. */
        long deadClinits;
        String failed;
        long methods;
        long ms;
    }

    private InlinedIndex inlinedIndex() {
        InlinedIndex ix = rt.inlinedIndex;
        if (ix == null) {
            synchronized (rt.idSites) {
                ix = rt.inlinedIndex;
                if (ix == null) {
                    ix = buildInlinedIndex();
                    rt.inlinedIndex = ix;
                }
            }
        }
        return ix;
    }

    /**
     * A method reference of a constant pool. HotSpot's pool casts the caller to its own method class, which a wrapped
     * method is not, so the lookup is retried without the caller (it only scopes the access check).
     */
    static jdk.vm.ci.meta.JavaMethod lookupMethodIn(jdk.vm.ci.meta.ConstantPool cp, int cpi, int bc, ResolvedJavaMethod caller) {
        try {
            return cp.lookupMethod(cpi, bc, caller);
        } catch (ClassCastException e) {
            return cp.lookupMethod(cpi, bc, null);
        }
    }

    private static String nameDesc(jdk.vm.ci.meta.JavaMethod m) {
        return m.getName() + m.getSignature().toMethodDescriptor();
    }

    /**
     * Every invoke* of the bytecode of every universe method that is reachable, implementation-invoked or
     * inlined, indexed by name + descriptor with its referenced holder (an over-approximation of the callers). A framed
     * method without bytecode is skipped (an inlined body there is inside a decoded graph); an unframed method without
     * readable bytecode, or any exception, fails the whole index (every exception refused).
     */
    private InlinedIndex buildInlinedIndex() {
        long t0 = System.nanoTime();
        InlinedIndex ix = new InlinedIndex();
        AnalysisMethod cur = null;
        try {
            for (AnalysisMethod m : rt.bridge.universeMethods()) {
                if (!m.isReachable() && !m.isImplementationInvoked() && !m.isInlined()) {
                    // The CLINIT exception: a dead class initializer is scanned too (its
                    // inlined callees count it as a caller; inlinedOnlyOk then skips it as dead)
                    if (!m.isClassInitializer() || !deadClinit(m)) {
                        continue;
                    }
                    ix.deadClinits++;
                }
                cur = m;
                ResolvedJavaMethod w = m.getWrapped();
                if (w.isAbstract() || w.isNative()) {
                    continue;
                }
                ix.methods++;
                byte[] code;
                try {
                    code = w.getCode();
                } catch (Throwable t) {
                    code = null;
                }
                if (code == null) {
                    LocalFlowGraph fr = rt.bridge.frameOf(m);
                    if (fr != null && rt.graphOf(fr) != null) {
                        continue;
                    }
                    ix.failed = "no-code:" + m.format("%H.%n(%p)");
                    return ix;
                }
                jdk.graal.compiler.bytecode.BytecodeStream bs = new jdk.graal.compiler.bytecode.BytecodeStream(code);
                jdk.vm.ci.meta.ConstantPool cp = w.getConstantPool();
                while (bs.currentBC() != jdk.graal.compiler.bytecode.Bytecodes.END) {
                    int bc = bs.currentBC();
                    if (bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKEVIRTUAL || bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKESPECIAL ||
                                    bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKESTATIC || bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKEINTERFACE) {
                        jdk.vm.ci.meta.JavaMethod jm = lookupMethodIn(cp, bs.readCPI(), bc, w);
                        ResolvedJavaType holder = jm.getDeclaringClass() instanceof ResolvedJavaType rt ? rt : null;
                        ix.sites.computeIfAbsent(nameDesc(jm), k -> new ArrayList<>()).add(new ByteSite(m, holder, bc));
                        if (ObjRetRules.methodHandleInvoker(jm.getDeclaringClass().toJavaName(true), jm.getName())) {
                            ix.wildcard.add(m); // a constant MethodHandle may be intrinsified here
                        }
                    } else if (bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKEDYNAMIC) {
                        ix.wildcard.add(m); // a constant call site may be intrinsified here
                    }
                    bs.next();
                }
            }
        } catch (Throwable t) {
            ix.failed = "error:" + t.getClass().getSimpleName() + (cur != null ? "@" + cur.format("%H.%n(%p)") : "");
        } finally {
            ix.ms = (System.nanoTime() - t0) / 1_000_000;
        }
        return ix;
    }

    /** The INLINED_ONLY check over the index ({@link ObjRetRules#inlinedOnlyOk}), memoised per method. */
    private boolean inlinedOnlyOk(AnalysisMethod x) {
        Boolean memo = rt.inlinedOk.get(x);
        if (memo != null) {
            return memo;
        }
        InlinedIndex ix = inlinedIndex();
        ObjRetRules.InlinedFacts<AnalysisMethod> facts = new ObjRetRules.InlinedFacts<>() {
            @Override
            public ObjRetRules.UnframedCause causeOf(AnalysisMethod m) {
                LocalFlowGraph fr = rt.bridge.frameOf(m);
                if (fr != null && rt.graphOf(fr) != null) {
                    return null;
                }
                return rt.objectIdentity.unframedCauseOf(m, fr);
            }

            @Override
            public boolean excluded(AnalysisMethod m) {
                return inlinedExcluded(m);
            }

            @Override
            public java.util.Collection<AnalysisMethod> callers(AnalysisMethod m) {
                return ix.failed != null ? null : bytecodeCallers(ix, m);
            }

            @Override
            public boolean deadClinit(AnalysisMethod m) {
                return ObjectReturnRule.this.deadClinit(m);
            }

            @Override
            public boolean wildcardsOk() {
                return inlinedWildcardsOk(ix, this);
            }
        };
        boolean ok = ObjRetRules.inlinedOnlyOk(x, facts);
        rt.inlinedOk.putIfAbsent(x, ok);
        java.util.Collection<AnalysisMethod> cs = ix.failed != null ? null : bytecodeCallers(ix, x);
        StringBuilder why = new StringBuilder();
        if (!ok && cs != null) {
            int k = 0;
            for (AnalysisMethod c : cs) {
                ObjRetRules.UnframedCause cc = facts.causeOf(c);
                if (cc != null && k++ < 3) {
                    why.append(k == 1 ? "(" : ",").append(c.format("%h.%n")).append(':').append(cc).append(deadClinit(c) ? "/dead" : "");
                }
            }
            if (k > 0) {
                why.append(')');
            }
            why.append(" self=").append(facts.causeOf(x)).append(facts.excluded(x) ? "/excluded:" + inlinedExcludedWhy(x) : "").append(rt.wildcardsOk == null ? ""
                            : rt.wildcardsOk ? "" : "/wildcards");
        }
        rt.inlinedOnlyLines.putIfAbsent(x.format("%H.%n(%p)"), "callers=" + (cs == null ? "index-failed" : String.valueOf(cs.size())) + (ok ? " ok" : " FAIL" + why));
        return ok;
    }

    private boolean inlinedWildcardsOk(InlinedIndex ix, ObjRetRules.InlinedFacts<AnalysisMethod> facts) {
        Boolean w = rt.wildcardsOk;
        if (w == null) {
            boolean all = ix.failed == null;
            String fail = ix.failed != null ? "index-failed" : null;
            // The wildcard set closed upward along inlining (an inlined wildcard's hosts are wildcards too)
            Set<AnalysisMethod> closed = all ? ObjRetRules.wildcardClosure(ix.wildcard, AnalysisMethod::isInlined, m -> bytecodeCallers(ix, m), ObjRetRules.INLINED_ONLY_DEPTH) : null;
            if (all && closed == null) {
                all = false;
                fail = "closure-failed"; // an inlining chain above the bound, or an inlined wildcard without bytecode callers
            }
            rt.wildcardsClosed = closed == null ? -1 : closed.size();
            if (all) {
                List<AnalysisMethod> ws = new ArrayList<>(closed);
                ws.sort(java.util.Comparator.comparing(m -> m.format("%H.%n(%p)")));
                for (AnalysisMethod m : ws) {
                    if (!ObjRetRules.wildcardOk(m, facts)) {
                        all = false;
                        fail = m.format("%H.%n(%p)") + ":" + facts.causeOf(m);
                        break;
                    }
                }
            }
            rt.wildcardFail = fail;
            rt.wildcardsOk = w = all;
        }
        return w;
    }

    /** Whether every method of the (non-empty) list passes {@link #inlinedOnlyOk}; a null / empty list = false. */
    private boolean allInlinedOnlyOk(java.util.Collection<AnalysisMethod> ms) {
        if (ms == null || ms.isEmpty()) {
            return false;
        }
        boolean all = true;
        for (AnalysisMethod m : ms) {
            all &= inlinedOnlyOk(m); // every method is asked (census lines), the answer is the conjunction
        }
        return all;
    }

    /**
     * The callers of {@code x} from the index (an over-approximation): a site with x's name + descriptor whose referenced
     * holder h can resolve or dispatch to x: a constructor ({@code invokespecial <init>}) only from h == x's class;
     * {@code invokestatic} / {@code invokespecial} resolve upward from h (x's class is h or a superclass of h);
     * {@code invokevirtual} / {@code invokeinterface} also dispatch downward (h is a supertype of x's class). An
     * unresolved holder matches.
     */
    private static java.util.Collection<AnalysisMethod> bytecodeCallers(InlinedIndex ix, AnalysisMethod x) {
        Set<AnalysisMethod> out = new java.util.LinkedHashSet<>();
        ResolvedJavaType xd = x.getDeclaringClass().getWrapped();
        for (ByteSite site : ix.sites.getOrDefault(nameDesc(x), List.of())) {
            ResolvedJavaType h = site.holder();
            boolean ss = site.opcode() == jdk.graal.compiler.bytecode.Bytecodes.INVOKESTATIC || site.opcode() == jdk.graal.compiler.bytecode.Bytecodes.INVOKESPECIAL;
            if (ObjRetRules.bytecodeCallerMatch(h == null, x.isConstructor(), ss, h != null && h.equals(xd), h != null && xd.isAssignableFrom(h), h != null && h.isAssignableFrom(xd))) {
                out.add(site.caller());
            }
        }
        return out; // (the MethodHandle / invokedynamic wildcard callers: InlinedFacts.wildcardsOk, image-level)
    }

    boolean deadClinit(AnalysisMethod c) {
        return rt.deadClinitMemo.computeIfAbsent(c, this::computeDeadClinit);
    }

    private boolean computeDeadClinit(AnalysisMethod c) {
        try {
            if (!c.isClassInitializer() || c.isImplementationInvoked() || c.isDirectRootMethod() || c.isVirtualRootMethod()) {
                return false;
            }
            if (closedWorldGuard() != null) {
                return false;
            }
            if (c.getMultiMethodKey() != com.oracle.svm.common.meta.MultiMethod.ORIGINAL_METHOD || c.getAllMultiMethods().size() > 1) {
                return false;
            }
            AnalysisType t = c.getDeclaringClass();
            if (!(t.getUniverse().hostVM() instanceof com.oracle.svm.hosted.SVMHost host)) {
                return false;
            }
            com.oracle.svm.core.hub.DynamicHub hub = host.dynamicHub(t);
            com.oracle.svm.core.classinitialization.ClassInitializationInfo info = hub == null ? null : hub.getClassInitializationInfo();
            if (info == null || !info.isInitialized() || info.getClassInitializer() != null) {
                return false;
            }
            return t.isInitialized() || rt.bridge.classInitSimulated(t);
        } catch (Throwable e) {
            return false;
        }
    }

    /** Excluded from INLINED_ONLY: native, intrinsic, a root, reflection / JNI registered (its class), or a non-ORIGINAL multi-method variant. */
    private boolean inlinedExcluded(AnalysisMethod m) {
        return inlinedExcludedWhy(m) != null;
    }

    /** {@link #inlinedExcluded}'s reason (census), null = not excluded. */
    private String inlinedExcludedWhy(AnalysisMethod m) {
        try {
            if (m.isNative() || m.isIntrinsicMethod() || m.isDirectRootMethod() || m.isVirtualRootMethod()) {
                return "native/intrinsic/root";
            }
            if (m.getMultiMethodKey() != com.oracle.svm.common.meta.MultiMethod.ORIGINAL_METHOD || m.getAllMultiMethods().size() > 1) {
                return "multi-method";
            }
            if (!org.graalvm.nativeimage.ImageSingletons.contains(com.oracle.svm.hosted.reflect.ReflectionHostedSupport.class)) {
                return "no-reflection-support";
            }
            var rs = org.graalvm.nativeimage.ImageSingletons.lookup(com.oracle.svm.hosted.reflect.ReflectionHostedSupport.class);
            var ex = rs.getReflectionExecutables().get(m.getDeclaringClass());
            if (ex != null && ex.containsKey(m)) {
                return "reflection";
            }
            if (rs.getHeapReflectionExecutables().containsKey(m)) {
                return "heap-reflection"; // a Method / Constructor object of m in the heap
            }
            String reg = rt.objectIdentity.registryReason(m.getDeclaringClass());
            return reg != null && (reg.equals("jni") || reg.startsWith("unreadable")) ? "registry:" + reg : null;
        } catch (Throwable t) {
            return "error:" + t.getClass().getSimpleName();
        }
    }

    /** The census token {@code inlinedOnly{index=… X:callers=n ok|FAIL, …}}. */
    private String inlinedOnlyCensus() {
        InlinedIndex ix = rt.inlinedIndex;
        List<String> ls = new ArrayList<>();
        for (Map.Entry<String, String> e : new TreeMap<>(rt.inlinedOnlyLines).entrySet()) {
            ls.add(e.getKey() + ":" + e.getValue());
        }
        return " inlinedOnly{index=" + (ix == null ? "unbuilt"
                        : (ix.failed != null ? "FAILED(" + ix.failed + ")" : "ok") + " methods=" + ix.methods + " ms=" + ix.ms + " deadClinits=" + ix.deadClinits +
                                        " wildcards=" + ix.wildcard.size() + (rt.wildcardsOk == null ? "" : " closed=" + rt.wildcardsClosed) + (rt.wildcardsOk == null ? ""
                                                        : rt.wildcardsOk ? " wildcardsOk" : " wildcardFAIL=" + rt.wildcardFail)) + " " + cap(String.valueOf(ls)) + "}";
    }

    /**
     * CONE_ARRAY (fail closed): an array type of an exposed type T (any dimension) is in the reverse index (a COMPONENT
     * link into T) or reachable. The dimensions are walked until the array type is not in the universe.
     */
    private String coneArray(List<AnalysisType> exposed) {
        NavIndex ix = navIndex();
        if (ix.problem != null) {
            return "unreadable:" + ix.problem;
        }
        for (AnalysisType t : exposed) {
            try {
                Class<?> tc = t.getJavaClass();
                if (tc == null) {
                    return "noClass:" + t.toJavaName(true);
                }
                for (NavLinkRec l : ix.links.getOrDefault(tc, List.of())) {
                    if (l.kind() == ObjRetRules.NavLink.COMPONENT) {
                        return l.n().toJavaName(true);
                    }
                }
                ResolvedJavaType w = t.getWrapped();
                while (true) {
                    w = w.getArrayClass();
                    AnalysisType at = rt.bridge.optionalAnalysisType(w);
                    if (at == null) {
                        break;
                    }
                    if (at.isReachable()) {
                        return at.toJavaName(true);
                    }
                }
            } catch (Throwable e) {
                return "error:" + e.getClass().getSimpleName() + "@" + t.toJavaName(true);
            }
        }
        return null;
    }

    /** G5-N: a reachable method declared by an exposed type invokes a {@code @CallerSensitive} method directly (or is unreadable). */
    private String coneCsm(List<AnalysisType> exposed) {
        Map<AnalysisType, List<AnalysisMethod>> idx = rt.reachableByType;
        if (idx == null) {
            synchronized (rt.idSites) {
                idx = rt.reachableByType;
                if (idx == null) {
                    idx = new java.util.HashMap<>();
                    for (AnalysisMethod m : rt.bridge.universeMethods()) {
                        if (m.isReachable() || m.isImplementationInvoked()) {
                            idx.computeIfAbsent(m.getDeclaringClass(), k -> new ArrayList<>()).add(m);
                        }
                    }
                    rt.reachableByType = idx;
                }
            }
        }
        jdk.vm.ci.meta.MetaAccessProvider host = com.oracle.graal.pointsto.util.GraalAccess.getOriginalProviders().getMetaAccess();
        ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(host);
        for (AnalysisType t : exposed) {
            for (AnalysisMethod m : idx.getOrDefault(t, List.of())) {
                ObjIdRules.BytecodeUses u = ObjIdRules.bytecodeUses(m.getWrapped(), apis);
                if (u.unreadable && "no-bytecode".equals(u.why)) {
                    u = rt.objectIdentity.irUses(m, apis, u);
                }
                if (u.callerSensitive || u.unreadable) {
                    return m.format("%H.%n") + (u.unreadable ? "(" + u.why + ")" : "");
                }
            }
        }
        return null;
    }

    /**
     * REGISTERED's second half: a class whose registered reflection queries navigate to an exposed type T: T's nest host
     * with {@code getNestMembers} enabled, T's declaring / enclosing class (or a subtype of it, for the inherited public
     * member classes) with {@code getDeclaredClasses} / {@code getClasses} enabled, a sealed supertype of T with
     * {@code getPermittedSubclasses} enabled. Null = none; an unreadable registry answers a reason (fail closed).
     */
    private String linkedRegistration(List<AnalysisType> exposed) {
        try {
            if (!org.graalvm.nativeimage.ImageSingletons.contains(org.graalvm.nativeimage.impl.RuntimeReflectionSupport.class) ||
                            !(org.graalvm.nativeimage.ImageSingletons.lookup(
                                            org.graalvm.nativeimage.impl.RuntimeReflectionSupport.class) instanceof com.oracle.svm.hosted.reflect.ReflectionDataBuilder rdb)) {
                return "unreadable:no-reflection-data";
            }
            int nestQ = com.oracle.svm.core.code.RuntimeMetadataDecoderImpl.ALL_NEST_MEMBERS_FLAG;
            int classesQ = com.oracle.svm.core.code.RuntimeMetadataDecoderImpl.ALL_DECLARED_CLASSES_FLAG | com.oracle.svm.core.code.RuntimeMetadataDecoderImpl.ALL_CLASSES_FLAG;
            int sealedQ = com.oracle.svm.core.code.RuntimeMetadataDecoderImpl.ALL_PERMITTED_SUBCLASSES_FLAG;
            jdk.vm.ci.meta.MetaAccessProvider host = com.oracle.graal.pointsto.util.GraalAccess.getOriginalProviders().getMetaAccess();
            NavIndex ix = navIndex();
            if (ix.problem != null) {
                return "unreadable:" + ix.problem;
            }
            for (AnalysisType t : exposed) {
                Class<?> tc = t.getJavaClass();
                if (tc == null) {
                    return "noClass:" + t.toJavaName(true);
                }
                Class<?> nh = tc.getNestHost();
                if (nh != tc && (rdb.getEnabledReflectionQueries(nh) & nestQ) != 0) {
                    return nh.getName() + ":nestMembers";
                }
                // The metadata-gated links of the reverse index, the flag checked on the link's
                // source class (getNestMembers of any member of T's nest lists the whole nest, RuntimeMetadataEncoderImpl
                // getNestMembers; getDeclaredClasses / getClasses of T's declaring class; getPermittedSubclasses)
                for (NavLinkRec l : ix.links.getOrDefault(tc, List.of())) {
                    if (!ObjRetRules.metadataNavLink(l.kind()) || l.n().equals(t)) {
                        continue;
                    }
                    Class<?> nc = l.n().getJavaClass();
                    if (nc == null) {
                        return "noClass:" + l.n().toJavaName(true);
                    }
                    int q = l.kind() == ObjRetRules.NavLink.NEST_MEMBER ? nestQ : l.kind() == ObjRetRules.NavLink.PERMITTED ? sealedQ : classesQ;
                    if ((rdb.getEnabledReflectionQueries(nc) & q) != 0) {
                        return nc.getName() + ":" + l.kind();
                    }
                }
                // getDeclaredClasses lists every member class; getClasses only the public ones (inherited included)
                boolean pub = java.lang.reflect.Modifier.isPublic(tc.getModifiers());
                for (Class<?> d : new Class<?>[]{tc.getDeclaringClass(), tc.getEnclosingClass()}) {
                    if (d == null) {
                        continue;
                    }
                    if ((rdb.getEnabledReflectionQueries(d) & (pub ? classesQ : com.oracle.svm.core.code.RuntimeMetadataDecoderImpl.ALL_DECLARED_CLASSES_FLAG)) != 0) {
                        return d.getName() + ":classes";
                    }
                    AnalysisType dt = pub ? rt.bridge.optionalAnalysisType(host.lookupJavaType(d)) : null;
                    if (dt != null) {
                        for (AnalysisType s : dt.getAllSubtypes()) {
                            Class<?> sc = s.getJavaClass();
                            if (sc != null && (rdb.getEnabledReflectionQueries(sc) & com.oracle.svm.core.code.RuntimeMetadataDecoderImpl.ALL_CLASSES_FLAG) != 0) {
                                return sc.getName() + ":classes(inherited)";
                            }
                        }
                    }
                }
                java.util.ArrayDeque<AnalysisType> up = new java.util.ArrayDeque<>();
                up.add(t);
                Set<AnalysisType> seen = new java.util.HashSet<>();
                while (!up.isEmpty()) {
                    AnalysisType u = up.poll();
                    if (u == null || !seen.add(u)) {
                        continue;
                    }
                    Class<?> uc = u.getJavaClass();
                    if (uc != null && uc.isSealed() && (rdb.getEnabledReflectionQueries(uc) & sealedQ) != 0) {
                        return uc.getName() + ":permittedSubclasses";
                    }
                    if (u.getSuperclass() != null) {
                        up.add(u.getSuperclass());
                    }
                    up.addAll(java.util.Arrays.asList(u.getInterfaces()));
                }
            }
            return null;
        } catch (Throwable e) {
            return "unreadable:" + e.getClass().getSimpleName();
        }
    }

    /**
     * METADATA_TYPE: every class named by the reflection metadata of a registered element: parameter, return,
     * exception and field types (generic trees included), record components, annotation {@code Class} values, and the
     * enclosing / declaring / nest-host / permitted-subclass lists of the registered classes. The
     * class-level metadata is scanned for every type whose hub is in the snapshot (SVM's {@code addClassMetadata} scope
     * in NativeImageCodeCache, not only the registered keys): the class annotations recursively (nested
     * annotations, annotation arrays, Class[] members), the type annotations, the enclosing-method info and the record
     * components; the registered executables and fields add their parameter and type annotations. Null = unreadable
     * (every class fails closed; an unreadable annotation value is never treated as an {@code Object.class} marker).
     */
    private Set<Class<?>> metadataClasses() {
        if (rt.metadataDone) {
            return rt.metadataClasses;
        }
        synchronized (rt.idSites) {
            if (rt.metadataDone) {
                return rt.metadataClasses;
            }
            Set<Class<?>> out = new java.util.HashSet<>();
            try {
                if (!org.graalvm.nativeimage.ImageSingletons.contains(com.oracle.svm.hosted.reflect.ReflectionHostedSupport.class)) {
                    throw new IllegalStateException("no-reflection-support");
                }
                var rs = org.graalvm.nativeimage.ImageSingletons.lookup(com.oracle.svm.hosted.reflect.ReflectionHostedSupport.class);
                Set<Class<?>> registeredClasses = new java.util.HashSet<>();
                for (var e : rs.getReflectionExecutables().entrySet()) {
                    registeredClasses.add(e.getKey().getJavaClass());
                    for (var v : e.getValue().values()) {
                        metaExecutable(v.getValueUnconditionally(), out);
                    }
                }
                for (var e : rs.getReflectionFields().entrySet()) {
                    registeredClasses.add(e.getKey().getJavaClass());
                    for (var v : e.getValue().values()) {
                        metaField(v.getValueUnconditionally(), out);
                    }
                }
                for (var ex : rs.getHeapReflectionExecutables().values()) {
                    metaExecutable(ex, out);
                }
                for (var f : rs.getHeapReflectionFields().values()) {
                    metaField(f, out);
                }
                for (var e : rs.getReflectionInnerClasses().entrySet()) {
                    registeredClasses.add(e.getKey());
                    out.addAll(e.getValue());
                }
                for (Class<?> k : registeredClasses) {
                    if (k == null) {
                        continue;
                    }
                    for (Class<?> l : new Class<?>[]{k.getDeclaringClass(), k.getEnclosingClass(), k.getNestHost()}) {
                        if (l != null) {
                            out.add(l);
                        }
                    }
                    if (k.isSealed()) {
                        out.addAll(java.util.Arrays.asList(k.getPermittedSubclasses()));
                    }
                }
                // the class metadata scope: every hub of the snapshot (plus the registered classes)
                rt.objectIdentity.hubConstantData(rt.bridge.lookupJavaType(Object.class));
                if (rt.hubConstantsFailed || rt.hubConstants == null) {
                    throw new IllegalStateException("hubs-unavailable");
                }
                Set<Class<?>> scope = new java.util.HashSet<>(registeredClasses);
                for (AnalysisType t : rt.hubConstants.keySet()) {
                    Class<?> jc = t.getJavaClass();
                    if (jc != null) {
                        scope.add(jc);
                    }
                }
                scope.remove(null);
                java.lang.reflect.Method em0 = com.oracle.svm.util.ReflectionUtil.lookupMethod(Class.class, "getEnclosingMethod0");
                for (Class<?> k : scope) {
                    if (k.isPrimitive() || k.isArray()) {
                        continue;
                    }
                    ObjRetRules.classMetadataClasses(k, out);
                    try {
                        Object[] em = (Object[]) em0.invoke(k);
                        if (em != null && em[0] instanceof Class<?> ec) {
                            out.add(ec);
                        }
                    } catch (java.lang.reflect.InvocationTargetException e) {
                        if (!(e.getCause() instanceof LinkageError)) {
                            throw e; // a LinkageError is stored and rethrown at run time (RuntimeMetadataEncoderImpl): no Class
                        }
                    }
                    java.lang.reflect.RecordComponent[] rcs = k.isRecord() ? rs.getRecordComponents(k) : null;
                    if (rcs != null) {
                        for (java.lang.reflect.RecordComponent rc : rcs) {
                            out.add(rc.getType());
                            metaType(rc.getGenericType(), out, new java.util.HashSet<>());
                            for (java.lang.annotation.Annotation an : rc.getDeclaredAnnotations()) {
                                ObjRetRules.annotationClasses(an, out);
                            }
                            ObjRetRules.annotatedTypeClasses(rc.getAnnotatedType(), out, new java.util.HashSet<>());
                        }
                    }
                }
                Set<Class<?>> el = new java.util.HashSet<>();
                for (Class<?> k : out) {
                    Class<?> e = k;
                    while (e.isArray()) {
                        e = e.getComponentType();
                    }
                    el.add(e);
                }
                out.addAll(el);
                rt.metadataClasses = out;
            } catch (Throwable t) {
                rt.metadataClasses = null;
                rt.metadataProblem = t.getClass().getSimpleName() + ":" + t.getMessage();
            }
            rt.metadataDone = true;
            return rt.metadataClasses;
        }
    }

    private static void metaExecutable(java.lang.reflect.Executable ex, Set<Class<?>> out) {
        if (ex == null) {
            return;
        }
        Set<Object> seen = new java.util.HashSet<>();
        out.add(ex.getDeclaringClass());
        for (java.lang.reflect.Type t : ex.getGenericParameterTypes()) {
            metaType(t, out, seen);
        }
        for (java.lang.reflect.Type t : ex.getGenericExceptionTypes()) {
            metaType(t, out, seen);
        }
        out.addAll(java.util.Arrays.asList(ex.getParameterTypes()));
        out.addAll(java.util.Arrays.asList(ex.getExceptionTypes()));
        if (ex instanceof java.lang.reflect.Method m) {
            metaType(m.getGenericReturnType(), out, seen);
            out.add(m.getReturnType());
        }
        ObjRetRules.executableMetadataClasses(ex, out); // recursive, with parameter and type annotations
    }

    private static void metaField(java.lang.reflect.Field f, Set<Class<?>> out) {
        if (f == null) {
            return;
        }
        out.add(f.getDeclaringClass());
        out.add(f.getType());
        metaType(f.getGenericType(), out, new java.util.HashSet<>());
        for (java.lang.annotation.Annotation a : f.getDeclaredAnnotations()) {
            ObjRetRules.annotationClasses(a, out); // recursive
        }
        ObjRetRules.annotatedTypeClasses(f.getAnnotatedType(), out, new java.util.HashSet<>());
    }

    private static void metaType(java.lang.reflect.Type t, Set<Class<?>> out, Set<Object> seen) {
        if (t == null || !seen.add(t)) {
            return;
        }
        if (t instanceof Class<?> k) {
            out.add(k);
        } else if (t instanceof java.lang.reflect.ParameterizedType p) {
            metaType(p.getRawType(), out, seen);
            metaType(p.getOwnerType(), out, seen);
            for (java.lang.reflect.Type a : p.getActualTypeArguments()) {
                metaType(a, out, seen);
            }
        } else if (t instanceof java.lang.reflect.GenericArrayType g) {
            metaType(g.getGenericComponentType(), out, seen);
        } else if (t instanceof java.lang.reflect.WildcardType w) {
            for (java.lang.reflect.Type b : w.getUpperBounds()) {
                metaType(b, out, seen);
            }
            for (java.lang.reflect.Type b : w.getLowerBounds()) {
                metaType(b, out, seen);
            }
        } else if (t instanceof java.lang.reflect.TypeVariable<?> v) {
            for (java.lang.reflect.Type b : v.getBounds()) {
                metaType(b, out, seen);
            }
        }
    }

    /**
     * Whether every use of the Class value {@code v} (same method, through Pis / hub reads) is an observation on the
     * harmless list ({@link ObjRetRules#HARMLESS_NODES}, {@link ObjRetRules#harmlessCall}); shared by the query walk, the
     * cone Class constants and premise G1-N. Frame states are not uses. {@code why} (optional) receives the first harmful
     * use.
     */
    boolean harmlessClassUses(ValueNode v0, String[] why) {
        return ObjRetRules.harmlessClassUses(v0, why); // in ObjRetRules for the JUnit
    }

    // ------------------------------------------------------------------
    // Premise G1-N (use-based), with its own premise line `objret.premise` (objid.w2.premise is separate). G1-N holds
    // iff no class read (StackFrame.getDeclaringClass, StackWalker.getCallerClass) is reachable, or every class read's
    // result has only harmless uses (use-based), or no walker can carry RETAIN_CLASS_REFERENCE (construction: the plain
    // G1 passes with every construction checked and no reachable non-walker method reads RETAIN_CLASS_REFERENCE; no
    // image-heap walker retains class references). G2-G4 are shared with the lambda identity premise.
    // ------------------------------------------------------------------
    static final class NamedPremise {
        int readApis;
        int readSites;
        int harmless;
        final List<String> harmful = new ArrayList<>();
        final List<String> lines = new ArrayList<>();
        final List<String> retainReads = new ArrayList<>();
        String construction = "n/a";
        String g1n = "?";
        int classCtx;
        int gccNonJdk;
        int instr;
        long ms;

        boolean g1nFails() {
            return g1n.startsWith("FAIL");
        }

        boolean fails() {
            return g1nFails() || classCtx != 0 || gccNonJdk != 0 || instr != 0;
        }

        String line() {
            StringBuilder sb = new StringBuilder("objret.premise: G1N=").append(g1n).append(" readApis=").append(readApis).append(" readSites=").append(readSites).append(" harmless=")
                            .append(harmless).append(" harmful=").append(harmful.size()).append(" construction=").append(construction).append(" retainReads=").append(retainReads.size())
                            .append(" CLASSCTX=").append(classCtx).append(" GCC_NONJDK=").append(gccNonJdk).append(" INSTR=").append(instr).append(" => ").append(fails() ? "FAIL" : "PASS");
            if (!harmful.isEmpty()) {
                sb.append(" firstHarmful=").append(harmful.get(0));
            }
            if (!retainReads.isEmpty()) {
                sb.append(" firstRetain=").append(retainReads.get(0));
            }
            return sb.append(" ms=").append(ms).toString();
        }
    }

    private NamedPremise namedPremise() {
        NamedPremise p = rt.namedPremise;
        if (p == null) {
            IdPremise base = rt.objectIdentity.idPremise(); // outside the lock below (idPremise takes the same monitor)
            synchronized (rt.idSites) {
                p = rt.namedPremise;
                if (p == null) {
                    p = buildNamedPremise(base);
                    rt.namedPremise = p;
                }
            }
        }
        return p;
    }

    private static boolean isClassReadApi(ResolvedJavaMethod t, ObjIdRules.PremiseApis apis) {
        if (t == null || t.isStatic()) {
            return false;
        }
        ResolvedJavaType d = t.getDeclaringClass();
        if ("getDeclaringClass".equals(t.getName()) && t.getSignature().getParameterCount(false) == 0 && apis.stackFrame.isAssignableFrom(d)) {
            return true;
        }
        return "getCallerClass".equals(t.getName()) && d.equals(apis.stackWalker);
    }

    private static ResolvedJavaMethod hostOf(Object o) {
        return o instanceof AnalysisMethod am ? am.getWrapped() : o instanceof ResolvedJavaMethod r ? r : null;
    }

    private NamedPremise buildNamedPremise(IdPremise base) {
        long t0 = System.nanoTime();
        NamedPremise np = new NamedPremise();
        np.classCtx = base.classCtx;
        np.gccNonJdk = base.gccNonJdk;
        np.instr = base.instr;
        try {
            jdk.vm.ci.meta.MetaAccessProvider host = com.oracle.graal.pointsto.util.GraalAccess.getOriginalProviders().getMetaAccess();
            ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(host);
            List<AnalysisMethod> reachable = new ArrayList<>();
            boolean declaringReachable = false;
            for (AnalysisMethod m : rt.bridge.universeMethods()) {
                if (!m.isReachable() && !m.isImplementationInvoked()) {
                    continue;
                }
                reachable.add(m);
                if (isClassReadApi(m.getWrapped(), apis)) {
                    np.readApis++;
                    declaringReachable |= "getDeclaringClass".equals(m.getName());
                    if (m.isDirectRootMethod() || m.isVirtualRootMethod()) {
                        np.harmful.add("root:" + m.format("%H.%n"));
                    }
                }
            }
            // the positions of the class reads (the analysis invokes); a read inside the walker itself or inside another
            // class-read implementation flows to that implementation's result, which is checked at its own callers
            // keyed by the AnalysisMethod (two methods with the same formatted name stay apart)
            Set<AnalysisMethod> positionSet = new java.util.HashSet<>();
            for (AnalysisMethod m : reachable) {
                List<Object[]> sites = rt.bridge.invokeSites(m);
                if (sites == null) {
                    continue;
                }
                for (Object[] site : sites) {
                    if (!isClassReadApi(hostOf(site[0]), apis)) {
                        continue;
                    }
                    if (!(site[1] instanceof AnalysisMethod pm)) {
                        np.harmful.add("unpositioned@" + site[2]);
                        continue;
                    }
                    Class<?> pc = pm.getDeclaringClass().getJavaClass();
                    if (ObjIdRules.isWalkerFamily(pc) || isClassReadApi(pm.getWrapped(), apis)) {
                        continue;
                    }
                    positionSet.add(pm);
                }
            }
            List<Map.Entry<String, AnalysisMethod>> positions = new ArrayList<>();
            for (AnalysisMethod pm : positionSet) {
                positions.add(Map.entry(pm.format("%H.%n(%p)"), pm));
            }
            positions.sort(Map.Entry.comparingByKey()); // by name for printing only
            for (Map.Entry<String, AnalysisMethod> e : positions) {
                LocalFlowGraph fr = rt.bridge.frameOf(e.getValue());
                StructuredGraph g = fr != null ? rt.graphOf(fr) : null;
                if (g == null) {
                    np.harmful.add(e.getKey() + "(no-ir)");
                    np.lines.add("[objret-g1n] read=" + e.getKey() + " uses=HARMFUL(no-ir)");
                    continue;
                }
                int matched = 0;
                for (Invoke inv : g.getInvokes()) {
                    if (!isClassReadApi(hostOf(inv.getTargetMethod()), apis)) {
                        continue;
                    }
                    matched++;
                    np.readSites++;
                    String[] why = new String[1];
                    boolean ok = harmlessClassUses(inv.asNode(), why);
                    if (ok) {
                        np.harmless++;
                    } else {
                        np.harmful.add(e.getKey() + "@" + inv.bci() + "(" + why[0] + ")");
                    }
                    np.lines.add("[objret-g1n] read=" + e.getKey() + "@" + inv.bci() + " target=" + inv.getTargetMethod().format("%H.%n") + " uses=" + (ok ? "harmless" : "HARMFUL(" + why[0] + ")"));
                }
                if (matched == 0) {
                    np.harmful.add(e.getKey() + "(not-in-ir)");
                    np.lines.add("[objret-g1n] read=" + e.getKey() + " uses=HARMFUL(not-in-ir)");
                }
            }
            // the construction half
            String cons;
            if (!declaringReachable && np.readApis > 0) {
                cons = "FAIL(no-g1-scan)"; // only getCallerClass is reachable: the plain G1 scan did not run
            } else if (base.swHidden != 0) {
                cons = "FAIL(g1)";
            } else {
                for (AnalysisMethod m : reachable) {
                    Class<?> jc = m.getDeclaringClass().getJavaClass();
                    if (ObjIdRules.isWalkerFamily(jc)) {
                        continue;
                    }
                    if (ObjRetRules.readsStatic(m.getWrapped(), apis.option, "RETAIN_CLASS_REFERENCE")) {
                        np.retainReads.add(m.format("%H.%n"));
                    }
                }
                java.util.Collections.sort(np.retainReads);
                boolean heapRetain = false;
                AnalysisType walkerType = rt.bridge.optionalAnalysisType(apis.stackWalker);
                Map<AnalysisType, Set<ImageHeapConstant>> objs = rt.bridge.heapObjects();
                if (objs == null) {
                    heapRetain = true;
                } else if (walkerType != null && objs.get(walkerType) != null) {
                    for (ImageHeapConstant k : objs.get(walkerType)) {
                        JavaConstant hc = k.getHostedObject();
                        Object w = hc != null ? com.oracle.graal.pointsto.util.GraalAccess.getOriginalSnippetReflection().asObject(Object.class, hc) : null;
                        if (!(w instanceof StackWalker sw) || retainsClassReference(sw)) {
                            heapRetain = true;
                        }
                    }
                }
                cons = !np.retainReads.isEmpty() ? "FAIL(retain-read)" : heapRetain ? "FAIL(heap-walker)" : "PASS";
            }
            np.construction = cons;
            if (np.readApis == 0 && positions.isEmpty() && np.harmful.isEmpty()) {
                np.g1n = "PASS(no-read)";
            } else if (np.harmful.isEmpty()) {
                np.g1n = "PASS(use)";
            } else if ("PASS".equals(cons)) {
                np.g1n = "PASS(construction)";
            } else {
                np.g1n = "FAIL";
            }
        } catch (Throwable t) {
            np.g1n = "FAIL(error:" + t.getClass().getSimpleName() + ")";
        }
        np.ms = (System.nanoTime() - t0) / 1_000_000;
        return np;
    }

    /** Whether a build-time walker retains class references (an unreadable walker answers true: fail closed). */
    private static boolean retainsClassReference(StackWalker w) {
        try {
            Set<?> opts = com.oracle.svm.util.ReflectionUtil.readField(StackWalker.class, "options", w);
            return opts == null || opts.contains(StackWalker.Option.RETAIN_CLASS_REFERENCE);
        } catch (Throwable t) {
            return true;
        }
    }

    /**
     * After the drain, a run with rule U active (objret!=0, named premise PASS, >= 1 usable named query) that tripped
     * EVALUATION_GUARD asks the fork driver for the objret=0 rerun ({@link StringAnalysisForkSupport#objretRerunDecision}).
     */
    boolean objretRerunCheck() {
        if (!OBJRET_DELIVER || !rt.guardTripped) {
            return false;
        }
        int usable = 0;
        for (NamedQuery q : rt.namedQueries.values()) {
            usable += q.usable() ? 1 : 0;
        }
        boolean premisePass;
        try {
            premisePass = !namedPremise().fails();
        } catch (Throwable t) {
            premisePass = true; // unreadable: rerun (the objret=0 run is the safe side)
        }
        boolean rerun = StringAnalysisForkSupport.objretRerunDecision(OBJRET_DELIVER, premisePass, usable, rt.guardTripped);
        System.out.println("[objret-rerun] reason=EVALUATION_GUARD decision=" + rerun + " premise=" + (premisePass ? "PASS" : "FAIL") + " usable=" + usable);
        if (rerun) {
            StringAnalysisForkSupport.requestObjretRerun();
        }
        return rerun;
    }

    /** The census part {@code objret{…}} and its lines (print-only; empty unless the census knob is on). */
    String objretCensus() {
        if (!OBJRET_ON) {
            return "";
        }
        NamedPremise np = namedPremise();
        System.out.println(np.line());
        int cap = 0;
        for (String l : np.lines) {
            if (cap++ == 200) {
                System.out.println("[objret-g1n] ... " + (np.lines.size() - 200) + " more");
                break;
            }
            System.out.println(l);
        }
        // per class: refusals at quiescence (any = the one-shot fallback under delivery)
        Map<NamedQuery, Set<String>> refsOf = new java.util.HashMap<>();
        for (NamedQuery q : rt.namedQueries.values()) {
            if (!q.usable() || !q.started.get()) {
                continue;
            }
            Set<String> rs = new java.util.TreeSet<>();
            for (RAtom a : q.atoms) {
                for (RTrackRefusal r : a.table.refusalsSnapshot()) {
                    rs.add(r.name());
                }
            }
            refsOf.put(q, rs);
        }
        // the nesting estimate: a class fell back only on trigger refusals and every nested class it reached is usable
        // and (recursively) precise or estimated precise: the greatest fixpoint
        Set<NamedQuery> est = new java.util.HashSet<>();
        for (Map.Entry<NamedQuery, Set<String>> e : refsOf.entrySet()) {
            if (!e.getValue().isEmpty() && ObjRetRules.NESTABLE.containsAll(e.getValue()) && !e.getKey().nested.isEmpty()) {
                est.add(e.getKey());
            }
        }
        boolean changed = true;
        while (changed) {
            changed = false;
            for (NamedQuery q : new ArrayList<>(est)) {
                for (Map.Entry<AnalysisType, Boolean> ne : q.nested.entrySet()) {
                    NamedQuery nq = rt.namedQueries.get(ne.getKey());
                    boolean good = ne.getValue() && nq != null && refsOf.containsKey(nq) && (refsOf.get(nq).isEmpty() || est.contains(nq));
                    if (!good) {
                        est.remove(q);
                        changed = true;
                        break;
                    }
                }
            }
        }
        List<String> tl = new ArrayList<>();
        int ret = 0;
        int par = 0;
        Map<String, Counter> tStatus = new TreeMap<>();
        int tPrecise = 0;
        int untrig = 0;
        int untrigPrecise = 0;
        int retPrecise = 0;
        int lookaheadN = 0;
        int lookaheadPrecise = 0;
        for (TriggerRec r : rt.objretTriggers.values()) {
            boolean viaLa = r.via != null && r.via.startsWith("lookahead");
            lookaheadN += viaLa ? 1 : 0;
            if (!r.triggered) {
                untrig++;
            } else if (r.param) {
                par++;
            } else {
                ret++;
            }
            String st = r.frameNoq != null ? r.frameNoq : r.q.status();
            Set<String> refs = r.q != null ? refsOf.get(r.q) : null;
            Set<String> labels = new java.util.TreeSet<>();
            if (refs != null) {
                for (RAtom a : r.q.atoms) {
                    EntryList<CallPath> l = a.table.entryPaths.get(r.frame);
                    if (l != null) {
                        for (int i = 0; i < l.size(); i++) {
                            labels.add(rt.objectIdentity.entryLabel(l.get(i)));
                        }
                    }
                }
            }
            // PRECISE(empty): no refusal and no entry at this frame (under delivery the return would continue nowhere)
            String outcome = refs == null ? st : refs.isEmpty() ? (labels.isEmpty() ? "PRECISE(empty)" : "PRECISE") : est.contains(r.q) ? "FELLBACK(est-nested)" : "FELLBACK";
            if (!r.triggered) {
                untrigPrecise += "PRECISE".equals(outcome) ? 1 : 0;
            } else {
                bump(tStatus, outcome);
                if ("PRECISE".equals(outcome)) {
                    lookaheadPrecise += viaLa ? 1 : 0;
                    tPrecise++;
                    retPrecise += r.param ? 0 : 1;
                }
            }
            StringBuilder sb = new StringBuilder(r.triggered ? "[objret-trigger] dir=" : "[objret-untriggered] dir=").append(r.param ? "PAR" : "RET").append(" frame=").append(rt.frameName(r.frame))
                            .append(" callers=").append(r.callers)
                            .append(" outside=").append(r.outside).append(" class=").append(r.q != null ? r.q.type.toJavaName(true) : rt.bridge.methodOf(r.frame).getDeclaringClass().toJavaName(true))
                            .append(" q=").append(outcome).append(" req{str=").append(r.strReq.get()).append(" other=").append(r.otherReq.get()).append(" query=")
                            .append(r.queryReq.get()).append(" sink=").append(r.sinkReq.get()).append('}');
            if (r.via != null) {
                sb.append(" via=").append(r.via);
            }
            if (OBJRET_DELIVER) {
                sb.append(" delivered=").append(r.delivered.get());
            }
            if (refs != null) {
                sb.append(" entries=").append(labels.size()).append(labels.size() <= 12 ? labels.toString() : "[...]").append(" refused=").append(refs);
            }
            tl.add(sb.toString());
        }
        java.util.Collections.sort(tl);
        for (String l : tl) {
            System.out.println(l);
        }
        Map<String, Counter> noq = new TreeMap<>();
        Map<String, Counter> guard = new TreeMap<>();
        Map<String, Counter> refusedBy = new TreeMap<>();
        int usable = 0;
        int started = 0;
        int precise = 0;
        int fellBack = 0;
        int maxDepth = 0;
        List<String> cl = new ArrayList<>();
        for (NamedQuery q : rt.namedQueries.values()) {
            if (q.noq != null) {
                bump(noq, q.noq.name());
            } else {
                bump(guard, q.fail == null ? "pass" : q.fail.name());
            }
            if (q.usable()) {
                usable++;
            }
            Set<String> refs = refsOf.get(q);
            if (refs != null) {
                started++;
                maxDepth = Math.max(maxDepth, q.depth.get());
                if (refs.isEmpty()) {
                    precise++;
                } else {
                    fellBack++;
                    for (String r : refs) {
                        bump(refusedBy, r);
                    }
                }
            }
            if (q.noq == ObjRetRules.NoQualifyN.STRING_CONE || q.noq == ObjRetRules.NoQualifyN.EMPTY_CONE) {
                continue; // counted only (the trigger lines name them)
            }
            StringBuilder sb = new StringBuilder("[objret-class] class=").append(q.type.toJavaName(true)).append(" status=").append(q.status()).append(" cone=").append(q.cone)
                            .append(" exposed=").append(q.exposed).append(q.detail);
            if (refs != null) {
                List<String> nest = new ArrayList<>();
                for (Map.Entry<AnalysisType, Boolean> ne : q.nested.entrySet()) {
                    nest.add(ne.getKey().toJavaName(true) + (ne.getValue() ? "" : "(unusable)"));
                }
                java.util.Collections.sort(nest);
                List<String> bs = new ArrayList<>();
                for (RAtom a : q.atoms) {
                    bs.add(a.kind == AtomKind.CONSTANT ? "heap:" + a.constant.getType().toJavaName(false) : rt.frameName(a.birthFrame));
                }
                java.util.Collections.sort(bs);
                sb.append(" depth=").append(q.depth.get()).append(" precise=").append(refs.isEmpty()).append(" refused=").append(refs).append(" first=").append(q.first)
                                .append(" estNested=").append(est.contains(q)).append(" nested=").append(nest).append(" birthIn=").append(bs);
            }
            cl.add(sb.toString());
        }
        java.util.Collections.sort(cl);
        for (String l : cl) {
            System.out.println(l);
        }
        String navPart = objretNavUseCensus();
        String dl = OBJRET_DELIVER ? " delivered=" + rt.objretDelivered.get() + " deliveries=" + rt.objretDeliveries.get() + " fallbacks=" + rt.objretFallbacks.get() + " emptyFallbacks=" +
                        rt.objretEmptyFallbacks.get() : "";
        return navPart + " objret{census=" + (OBJRET_CENSUS ? 1 : 0) + " objret=" + OBJRET + dl + " premise=" + (np.fails() ? "FAIL" : "PASS") + " g1n=" + np.g1n + " events=" + rt.objretEvents.get() +
                        " triggers=ret:" + ret + "/par:" + par +
                        " triggerOutcome=" + top(tStatus) + " triggerPrecise=" + tPrecise + " retPrecise=" + retPrecise + " untriggered=" + untrig + "/precise:" + untrigPrecise + " lookahead=" +
                        lookaheadN + "/precise:" + lookaheadPrecise + " classes=" + rt.namedQueries.size() + " noq=" + top(noq) + " guard=" + top(guard) +
                        " usable=" + usable + " started=" + started + " precise=" + precise + " fellBack=" + fellBack + " estNested=" + est.size() + " refusedBy=" + top(refusedBy) +
                        " maxDepth=" + maxDepth + " np5Harmless=" + rt.objretNp5Harmless.get() + " classEscapes=" + rt.objretClassEscapes.get() + " hiddenNest=" + rt.objretHiddenNest.get() +
                        " heapTwins=" + rt.heapTwins.size() + " premiseMs=" + np.ms + "}";
    }

    /** Print-only: a class's guard outcome under the use-based nest rule (the exceptions are in the guard). */
    private String wouldBe(NamedQuery q, boolean useNest) {
        NamedQuery w = new NamedQuery(q.type);
        StringBuilder d = new StringBuilder();
        ObjRetRules.GuardFailN f = namedGuard(w, q.coneL, q.exposedL, d, useNest);
        String det = d.toString().trim();
        if (det.length() > 1200) {
            det = det.substring(0, 1200) + "...";
        }
        return (f == null ? "USABLE" : f.name()) + "{" + det + "}";
    }

    /** The nest-navigation use census lines and the per-class would-be lines; answers the summary token. */
    private String objretNavUseCensus() {
        if (!OBJRET_CENSUS) {
            return selfSlotCensus() + inlinedOnlyCensus(); // the nav-use census and the would-be guards are census=1 only
        }
        NavCensus nc = navCensus();
        int harmful = 0;
        int exempt = 0;
        Map<String, Counter> byApi = new TreeMap<>();
        Map<String, Counter> byRecv = new TreeMap<>();
        for (NavSite s : nc.sites) {
            exempt += s.exempt ? 1 : 0;
            harmful += !s.exempt && !s.harmless ? 1 : 0;
            bump(byApi, s.api);
            bump(byRecv, s.recv.startsWith("UNKNOWN") ? "UNKNOWN" : s.recv);
        }
        System.out.println("objret.navuse: types=" + nc.types + " sites=" + nc.sites.size() + " harmful=" + harmful + " exempt=" + exempt + " byApi=" + top(byApi) + " byRecv=" + top(byRecv) +
                        " reflective=" + nc.reflective + " problem=" + nc.problem + " ms=" + nc.ms);
        int cap = 0;
        for (NavSite s : nc.sites) {
            if (cap++ == 400) {
                System.out.println("[objret-navsite] ... " + (nc.sites.size() - 400) + " more");
                break;
            }
            System.out.println(s.line());
        }
        List<String> lines = new ArrayList<>();
        Map<String, Counter> moves = new TreeMap<>();
        for (NamedQuery q : rt.namedQueries.values()) {
            if (q.noq != null || q.fail == null || !NAV_OR_UNFRAMED.contains(q.fail)) {
                continue;
            }
            String reach = navReach(q.exposedL);
            String wNest = wouldBe(q, true);
            bump(moves, q.fail.name() + "->" + wNest.substring(0, wNest.indexOf('{')));
            lines.add("[objret-nestuse] class=" + q.type.toJavaName(true) + " status=" + q.fail.name() + " links=" + navLinkSummary(q.exposedL) + " reach=" + (reach == null ? "none" : reach) +
                            " reachN=" + navReachCount(q.exposedL) +
                            " wouldBe(nest)=" + wNest);
        }
        java.util.Collections.sort(lines);
        for (String l : lines) {
            System.out.println(l);
        }
        return " objretNav{sites=" + nc.sites.size() + " harmful=" + harmful + " reflective=" + nc.reflective.size() + " blocked=" + lines.size() + " moves=" + top(moves) + "}" + selfSlotCensus() +
                        inlinedOnlyCensus();
    }
}
