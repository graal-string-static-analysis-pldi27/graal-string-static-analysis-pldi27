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
import static com.oracle.svm.hosted.stringanalysis.ClosedFieldEscape.indexFailure;
import static com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.isNamedQuery;
import static com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.lookupMethodIn;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.DUMP;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.OBJRET_DELIVER;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.OBJRET_ON;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.bump;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.exactTypeOf;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.focused;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.memberName;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.restored;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.top;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.unwalkableInstances;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicBoolean;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.VirtualState;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.NewInstanceNode;
import jdk.graal.compiler.nodes.java.NewInstanceWithExceptionNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.virtual.AllocatedObjectNode;
import jdk.graal.compiler.nodes.virtual.CommitAllocationNode;
import jdk.graal.compiler.nodes.virtual.VirtualInstanceNode;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

import com.oracle.graal.pointsto.heap.ImageHeapConstant;
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
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.AtomKind;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.Counter;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.DesugaredCall;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtom;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtomKey;

/**
 * Lambda object-identity tracking of {@link RecursiveTracking}: the identity queries, the pending-slot allow-list and the
 * conditional (foreign-birth) premise (the pure decisions are in {@link ObjIdRules}).
 */
final class ObjectIdentityRule {
    private final RecursiveTracking rt;

    ObjectIdentityRule(RecursiveTracking rt) {
        this.rt = rt;
    }

    // ------------------------------------------------------------------
    // Lambda object-identity tracking. The premise: the birth set of the class is complete
    // unless its Class object escapes (a foreign birth; the query then falls back); the closed-field escape is widened
    // to the query atoms. A path-less return out of an instance frame M of a qualifying class C (ObjIdRules.qualifies)
    // whose birth set passes ObjIdRules.guard continues at the union of T(o).entryPaths[M] over C's framed allocation
    // births o, each a MERGED query atom in its own key space (IdSite); the first refusal of any query table adds the
    // ordinary caller fan once (a pure union).
    // ------------------------------------------------------------------
    /**
     * The site of a query atom: wraps the birth's ordinary site object (an allocation vertex), so the query atom lives in
     * its own key space (no existing atom's key, table or walk is shared with it). Interned per wrapped site.
     */
    static final class IdSite {
        final Object site;
        /**
         * A named-class query's site (its own key space, apart from the hidden-class (lambda) queries: a lambda birth in a
         * named interface cone is a different atom from the same birth's lambda query; the harmless-Class-use exemption
         * applies to named sites only).
         */
        final boolean named;

        IdSite(Object site) {
            this(site, false);
        }

        IdSite(Object site, boolean named) {
            this.site = site;
            this.named = named;
        }

        @Override
        public String toString() {
            return (named ? "objret:" : "objid:") + ContextPolicy.siteKey(site);
        }
    }

    static boolean isIdQuery(RAtom a) {
        return a != null && a.key.site instanceof IdSite;
    }

    /** Per class: the qualification / guard verdict, the births and (when usable) the query atoms. */
    final class IdQuery {
        final AnalysisType type;
        final ObjIdRules.NoQualify noq;
        final ObjIdRules.GuardFail fail;
        final List<Object[]> births;
        final List<RAtom> atoms = new ArrayList<>();
        final String detail;

        IdQuery(AnalysisType type, ObjIdRules.NoQualify noq, ObjIdRules.GuardFail fail, List<Object[]> births, String detail) {
            this.type = type;
            this.noq = noq;
            this.fail = fail;
            this.births = births;
            this.detail = detail;
        }

        boolean usable() {
            return noq == null && fail == null && !atoms.isEmpty();
        }
    }

    /** The query of {@code frame}'s declaring class, or null (a static frame). Memoised per class. */
    IdQuery idQueryOf(LocalFlowGraph frame) {
        AnalysisMethod m = rt.bridge.methodOf(frame);
        if (m == null || m.isStatic()) {
            return null;
        }
        AnalysisType c = m.getDeclaringClass();
        IdQuery q = rt.idQueries.get(c);
        if (q == null) {
            IdQuery fresh = computeIdQuery(c);
            q = rt.idQueries.putIfAbsent(c, fresh);
            if (q == null) {
                q = fresh;
            }
        }
        return q;
    }

    private IdQuery computeIdQuery(AnalysisType c) {
        ObjIdRules.NoQualify noq = ObjIdRules.qualifies(false, c);
        if (noq != null) {
            return new IdQuery(c, noq, null, List.of(), null);
        }
        IdBirthIndex x = idBirthIndex();
        List<Object[]> births = x.births.getOrDefault(c, List.of());
        int heap = 0;
        Map<AnalysisType, Set<ImageHeapConstant>> heapObjs = rt.bridge.heapObjects();
        if (heapObjs == null) {
            heap = 1; // unavailable: fail closed
        } else if (heapObjs.get(c) != null) {
            heap = heapObjs.get(c).size();
        }
        boolean hostIndy;
        try {
            // Both sides are nest hosts (LMF defines C as a nestmate of the capturing class, so C's nest
            // host is the capturing class's nest host, not the declaring class of an indy in a nested class's method)
            Class<?> jc = c.getJavaClass();
            Class<?> host = jc != null ? jc.getNestHost() : null;
            hostIndy = host == null || x.unframedIndyHosts.contains(host) || x.unframedBirths.contains(c);
        } catch (Throwable t) {
            hostIndy = true; // fail closed
        }
        int consts = x.classConstants.getOrDefault(c, 0);
        String[] holderDetail = new String[1];
        int holders = classHolders(c, holderDetail);
        String reg = registryReason(c);
        StringBuilder pdetail = new StringBuilder();
        int pendingNotAllowed = pendingCheck(c, pdetail);
        IdPremise premise = idPremise();
        boolean csm = premise.lambdaCsm.contains(c);
        boolean unwalkable = x.unwalkableBirths.contains(c);
        ObjIdRules.GuardFail fail = ObjIdRules.guard(premise.imageFails(), csm, x.failReason != null, x.unframedDeclaring.contains(c) ? 1 : 0, hostIndy, unwalkable, heap, births.size(), consts,
                        holders, reg != null, pendingNotAllowed);
        String detail = "births=" + births.size() + " heap=" + heap + " consts=" + consts + " holders=" + holders + (holderDetail[0] != null ? holderDetail[0] : "") +
                        (reg != null ? " reg=" + reg : "") + (hostIndy ? " hostIndy" : "") + (unwalkable ? " unwalkableBirth" : "") + (csm ? " csm" : "") + (pdetail.length() > 0 ? " pending=" +
                                        pdetail : "");
        IdQuery q = new IdQuery(c, null, fail, births, detail);
        if (fail == null) {
            for (Object[] b : births) {
                LocalFlowGraph bf = (LocalFlowGraph) b[0];
                ValueNode bn = (ValueNode) b[1];
                IdSite site = rt.idSites.computeIfAbsent(rt.siteOf(bf, bn), IdSite::new);
                RAtomKey key = rt.internKey(site, HeapContext.MERGED);
                RAtom atom = rt.atoms.computeIfAbsent(key, k -> rt.new RAtom(k, AtomKind.ALLOCATION, bf, bn, MethodContext.UNKNOWN, null, null, false));
                q.atoms.add(atom);
            }
        }
        if (DUMP && focused(c.toJavaName(true))) {
            System.out.println("[rtrack-dump] OBJID class=" + c.toJavaName(true) + " fail=" + fail + " " + detail);
        }
        return q;
    }

    /** Schedules the query atoms (idempotent: {@link RecursiveTracking#schedule} builds a table exactly once). */
    private void startIdQuery(IdQuery q) {
        for (RAtom a : q.atoms) {
            rt.schedule(a);
        }
    }

    /**
     * The RETURN hook (before {@link RecursiveTracking#returnAllCallers}): true = handled by the identity caller set. Never for a query
     * atom's own return (no nested queries).
     */
    boolean idReturn(RAtom atom, LocalFlowGraph frame) {
        if (isIdQuery(atom) && !(OBJRET_DELIVER && isNamedQuery(atom))) {
            // Under objret=1 a named query atom may use the lambda identity caller set;
            // the lambda (hidden-class) query atoms keep the no-nesting bound
            return false;
        }
        rt.objidFrames.incrementAndGet();
        IdQuery q = idQueryOf(frame);
        if (q == null || !q.usable()) {
            return false;
        }
        if (rt.containerCallersIncomplete(frame)) {
            rt.refuse(atom.table, RTrackRefusal.MISSING_IR); // the same fail-closed check as the fan
            return true;
        }
        if (rt.worldTop.outsideCaller(frame)) {
            // As the OWNER(Y) branch: the entry lists name only the analysed calls; an outside caller is refused
            rt.worldTop.e2Note("WTX-objid", frame);
            rt.refuse(atom.table, RTrackRefusal.WORLD_TOP_EXIT);
        }
        rt.objidReturns.incrementAndGet();
        rt.objidHookedFrames.add(frame);
        startIdQuery(q);
        WaitRec wr = rt.holderEnd.waitRec(atom, "objidret", frame, null); // holder-end rule: as the owner return's wait
        ObjIdRules.wireUnion(entryListsOf(q, frame), l -> List.of("objid-ret", atom.key, frame, l.table.owner), registerFeeding(atom.table), (list, idx) -> {
            if (wr != null) {
                wr.delivered.set(true);
            }
            rt.objidDeliveries.incrementAndGet();
            CallPath p = list.get(idx);
            idContraCheck(frame, p);
            if (p == null) {
                rt.refuse(atom.table, RTrackRefusal.MISSING_IR);
                return;
            }
            returnAtEntry(atom, frame, p);
        }, (list, r) -> {
            if (wr != null) {
                wr.fell.set(true);
            }
            rt.objidFallbacks.incrementAndGet();
            bump(rt.objidFellBy, r.name());
            if (DUMP && focused(rt.frameName(frame))) {
                System.out.println("[rtrack-dump] OBJID fallback atom=" + atom.key + " frame=" + rt.frameName(frame) + " on " + r + " from " + list.table.owner);
            }
            rt.returnAllCallers(atom, frame); // the one-shot caller fan (the precise deliveries stay registered)
        });
        return true;
    }

    /** The births' entry lists of {@code frame} (one per query atom, in birth order). */
    private static List<EntryList<CallPath>> entryListsOf(IdQuery q, LocalFlowGraph frame) {
        List<EntryList<CallPath>> out = new ArrayList<>(q.atoms.size());
        for (RAtom o : q.atoms) {
            out.add(o.table.entryPaths(frame));
        }
        return out;
    }

    /**
     * {@link ObjIdRules.Registrar} over the census-counting {@link RecursiveTracking#register}: the registrar of {@link ObjIdRules#wireUnion} (no refusal target: the refusal runs the hook's fallback).
     * Its continuation feeds {@code dep} (ID-DEP travels to it).
     */
    ObjIdRules.Registrar registerFeeding(ContainerTables.Refusable dep) {
        return (list, key, onEntry, onRefusal) -> rt.register(list, key, onEntry, null, onRefusal, null, dep);
    }

    /**
     * Self-check (print-only): a precise entry site that is not one of the frame's callers kept by the caller-index site
     * filter prints {@code OBJID-CONTRA} (expected: walk imprecision, not a filter drop of a real caller). Model,
     * desugared and fold links are not caller-index sites (counted unchecked).
     */
    private void idContraCheck(LocalFlowGraph frame, CallPath p) {
        if (p == null || !(p.call instanceof LocalFlowGraph.LocalVertex cv)) {
            rt.objidContraUnchecked.incrementAndGet();
            return;
        }
        String label = rt.frameName(p.callerFrame) + "@" + cv.bci;
        List<ForwardFixpoint.CallerSite> kept = rt.worldTop.fanCallersOf(frame);
        if (kept != null) {
            for (ForwardFixpoint.CallerSite s : kept) {
                LocalFlowGraph.LocalVertex rc = s.call();
                if (rc != null && rc.owner == p.callerFrame && (rc == cv || (cv.irNode != null && rc.irNode == cv.irNode) || rc.bci == cv.bci)) {
                    return;
                }
            }
        }
        if (rt.objidContraSeen.add(rt.frameName(frame) + " <- " + label)) { // counted once per (frame, entry site)
            rt.objidContra.incrementAndGet();
            System.out.println("[sug-fwd-rtrack-b] OBJID-CONTRA frame=" + rt.frameName(frame) + " entry=" + label);
        }
    }

    /**
     * The continuation of a return at one entry {@code p} of a receiver's entry list: shared by the OWNER(Y) rule
     * and the identity rule.
     */
    void returnAtEntry(RAtom atom, LocalFlowGraph frame, CallPath p) {
        if (p != null && p.call instanceof DesugaredCall dc) {
            rt.concatOperandArrival(atom, dc); // the implicit toString()'s result
            return;
        }
        if (rt.models.returnArrival(atom, p)) {
            return; // a model callback's result
        }
        if (p != null && p.isFold()) {
            rt.returnAlongFold(atom, frame, p); // the recursion fold: a receiver crossing whose push folded
            return;
        }
        List<ValueNode> invs = rt.invokesOf(p);
        if (invs.isEmpty()) {
            rt.refuse(atom.table, RTrackRefusal.MISSING_IR);
            return;
        }
        for (ValueNode inv : invs) {
            rt.enqueueWalk(atom, p.callerFrame, inv, p.next, restored(p.callerMctx));
        }
    }

    /**
     * The PARAMETER hook (the path-less branch of {@link RecursiveTracking#parameterIndexCase}, before the fan): true = handled by the
     * identity caller set. Slot 0 resolves to the query atoms themselves (every receiver of a qualifying frame is a C
     * instance born at a birth); slot k > 0 resolves at every entry of the births' entry lists by the path-ful branch's
     * rules. The first refusal of any query table adds the ordinary caller fan once (a pure union). Unlike
     * {@link #idReturn} there is no {@code isIdQuery} exclusion: a query atom's own parameter may wait on another class's
     * query, a monotone union over a finite set of query atoms, so it stays sound and terminates.
     */
    boolean idParameter(LocalFlowGraph frame, int pidx, MethodContext mctx, Sink sink) {
        IdQuery q = idQueryOf(frame);
        if (q == null || !q.usable()) {
            return false;
        }
        if (rt.containerCallersIncomplete(frame)) {
            rt.refuse(sink, RTrackRefusal.MISSING_IR);
            return true;
        }
        if (rt.worldTop.outsideCaller(frame)) {
            rt.worldTop.e2Note("WTE-objid", frame);
            rt.refuse(sink, RTrackRefusal.WORLD_TOP_ENTRY); // as the fan: an outside caller passes an unseen argument
        }
        rt.objidParams.incrementAndGet();
        rt.objidHookedFrames.add(frame);
        startIdQuery(q);
        if (pidx == 0) {
            for (RAtom o : q.atoms) {
                rt.addAtomTo(sink, o.key); // the receiver is the query atom itself
            }
        }
        AtomicBoolean fell = new AtomicBoolean();
        Runnable foldFan = () -> {
            if (fell.compareAndSet(false, true)) {
                rt.objidParamFallbacks.incrementAndGet();
                bump(rt.objidFellBy, "param:fold");
                rt.parameterFan(frame, pidx, mctx, sink);
            }
        };
        ObjIdRules.wireUnion(fell, entryListsOf(q, frame), l -> List.of("objid-par", sink, frame, pidx, l.table.owner), registerFeeding(sink), (list, idx) -> {
            if (pidx == 0) {
                return; // the receiver is the query atom itself (added above)
            }
            rt.objidDeliveries.incrementAndGet();
            CallPath p = list.get(idx);
            idContraCheck(frame, p);
            if (p == null) {
                rt.refuse(sink, RTrackRefusal.MISSING_IR);
                return;
            }
            if (p.isFold()) {
                foldFan.run(); // backward under a recursion fold is path-less = the fan (as parameterIndexCase)
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
        }, (list, r) -> {
            rt.objidParamFallbacks.incrementAndGet();
            bump(rt.objidFellBy, "param:" + r.name());
            rt.parameterFan(frame, pidx, mctx, sink); // the one-shot caller fan (the precise deliveries stay registered)
        });
        return true;
    }

    // ------------------------------------------------------------------
    // Pending slots (a narrow, audited allow-list). A READ heap slot whose value is still a pending
    // future is never scanned, so "no heap slot holds C's Class / a C instance" (CLASS_HOLDER, HEAP_INSTANCE) is proven
    // only for the indexed slots. Per pending slot kind the sound declared-type closure decides whether it may hold C's
    // Class or a C instance (ObjIdRules.slotClosure / mayHold); a kind that may must be on ObjIdRules.PENDING_ALLOW (each
    // audited: A = contents indexed or membership-only readers, B = the raw-memory residual); any other kind fails the
    // guard closed (PENDING_SLOT).
    // ------------------------------------------------------------------
    /** One still-pending READ slot kind: where (the census key) and its declared types (null: unknown). */
    static final class PendingSlot {
        final String where;
        final List<AnalysisType> types;
        private volatile boolean closureDone;
        private volatile Set<AnalysisType> closure;

        PendingSlot(String where, List<AnalysisType> types) {
            this.where = where;
            this.types = types;
        }
    }

    void notePendingSlot(String where, List<AnalysisType> types) {
        rt.pendingSlots.computeIfAbsent(where, k -> new PendingSlot(k, types));
    }

    /**
     * A field slot's declared types: an {@code @UnknownObjectField}'s annotation types (the types SVM's own analysis
     * assumes the computed value has: {@code FieldValueInterceptionSupport}), else the field's declared type; null =
     * unknown (fail closed).
     */
    List<AnalysisType> declaredSlotTypes(AnalysisField f) {
        try {
            com.oracle.svm.core.heap.UnknownObjectField u = f.getAnnotation(com.oracle.svm.core.heap.UnknownObjectField.class);
            if (u == null) {
                return List.of(f.getType());
            }
            List<AnalysisType> out = new ArrayList<>();
            for (Class<?> k : u.types()) {
                AnalysisType t = rt.bridge.lookupJavaType(k);
                if (t == null) {
                    return null;
                }
                out.add(t);
            }
            for (String n : u.fullyQualifiedTypes()) {
                AnalysisType t = rt.bridge.lookupJavaType(Class.forName(n));
                if (t == null) {
                    return null;
                }
                out.add(t);
            }
            if (out.isEmpty()) {
                out.add(f.getType());
            }
            return out;
        } catch (Throwable t) {
            return null;
        }
    }

    Set<AnalysisType> closureOf(PendingSlot ps) {
        if (!ps.closureDone) {
            synchronized (ps) {
                if (!ps.closureDone) {
                    Set<AnalysisType> cl;
                    try {
                        cl = ps.types == null ? null : ObjIdRules.slotClosure(ps.types);
                    } catch (Throwable t) {
                        cl = null;
                    }
                    ps.closure = cl;
                    ps.closureDone = true;
                }
            }
        }
        return ps.closure;
    }

    /**
     * The pending slot kinds that may hold C's Class object or a C instance and are not on the allow-list (the guard's
     * PENDING_SLOT count). A missing holder index fails closed.
     */
    int pendingCheck(AnalysisType c, StringBuilder detail) {
        if (rt.holderIndex() == null) {
            detail.append("[index-unavailable]");
            return 1;
        }
        AnalysisType hub = rt.bridge.lookupJavaType(Class.class);
        List<PendingSlot> slots = new ArrayList<>(rt.pendingSlots.values());
        slots.sort(java.util.Comparator.comparing(ps -> ps.where));
        int bad = 0;
        List<String> ws = new ArrayList<>();
        for (PendingSlot ps : slots) {
            Set<AnalysisType> cl = closureOf(ps);
            boolean holdsHub = hub == null || ObjIdRules.mayHold(cl, hub);
            boolean holdsInst = ObjIdRules.mayHold(cl, c);
            if (ObjIdRules.pendingSlotBlocks(holdsHub, holdsInst, ps.where)) {
                bad++;
                ws.add(ps.where + ":" + (holdsHub ? "C" : "") + (holdsInst ? "I" : "") + ":NOT_ALLOWED");
            }
        }
        if (!ws.isEmpty()) {
            detail.append(ws);
        }
        return bad;
    }

    /**
     * The pending slot kinds of this image that may hold a Class object or a hidden (lambda) class instance and are not on
     * {@link ObjIdRules#PENDING_ALLOW}. Non-empty = a new kind appeared: every lambda class then fails PENDING_SLOT
     * (closed) until it is audited.
     */
    private List<String> pendingNotAllowed() {
        AnalysisType hub = rt.bridge.lookupJavaType(Class.class);
        List<String> out = new ArrayList<>();
        for (PendingSlot ps : rt.pendingSlots.values()) {
            Set<AnalysisType> cl = closureOf(ps);
            // a hidden lambda class's only supertypes are Object and its interfaces: a closure that reaches an interface
            // or Object may hold one (slotClosure answers null for Object)
            boolean lambda = cl == null;
            if (cl != null) {
                for (AnalysisType t : cl) {
                    lambda |= t.isInterface() || t.isJavaLangObject();
                }
            }
            if (ObjIdRules.pendingSlotBlocks(hub == null || ObjIdRules.mayHold(cl, hub), lambda, ps.where)) {
                out.add(ps.where);
            }
        }
        java.util.Collections.sort(out);
        return out;
    }

    // ------------------------------------------------------------------
    // The conditional premise. The foreign-birth premise says a lambda class's Class object reaches user code only
    // through getClass() of an instance (the walk refuses it), a class constant, a heap slot or a registry (all checked
    // per class). The raw-memory producers that hand a lambda's Class to Java code are checked once per image after the
    // analysis: G1 SW_HIDDEN (a stack walker that shows hidden frames and StackFrame.getDeclaringClass), G2 CLASSCTX
    // (SecurityManager.getClassContext), G3 GCC_NONJDK (Reflection / StackTraceUtils.getCallerClass called directly by
    // application code), G4 INSTR (an instantiated Instrumentation: getAllLoadedClasses). Any of them = no lambda
    // qualifies in this image. G5 LAMBDA_CSM (per class): a lambda whose own bytecode invokes a @CallerSensitive method
    // directly (its caller class is the lambda class) does not qualify. No unsafe-allocation registry check is used
    // (compat builds register every instantiated type, so such a check would disqualify all).
    // ------------------------------------------------------------------
    /** The per-image premise facts (computed once; {@link #idPremise}). */
    static final class IdPremise {
        int swHidden;
        int classCtx;
        int gccNonJdk;
        int instr;
        int lambdas;
        final Set<AnalysisType> lambdaCsm = new java.util.HashSet<>();
        final Map<String, String> first = new TreeMap<>();
        /** Print-only: every G1 event of the image in detection order (the verdict uses the first). */
        final List<String> g1all = new ArrayList<>();
        /** The pending walker constructions, each {@code {host method, bci}}; their census lines. */
        final List<Object[]> pending = new ArrayList<>();
        final List<String> g1fwdLines = new ArrayList<>();
        int g1fwdProven;
        int g1fwdFailed;
        int g1fwdMaxDepth;
        long ms;

        /** A G1 event: recorded in {@link #g1all}; the first one fails G1 and names the census reason. */
        void g1Event(String what) {
            g1all.add(what);
            if (swHidden == 0) {
                swHidden = 1;
                first.put("SW_HIDDEN", what);
            }
        }

        String g1FwdLine() {
            return "objid.w2.g1fwd: pending=" + pending.size() + " proven=" + g1fwdProven + " failed=" + g1fwdFailed + " maxDepth=" + g1fwdMaxDepth;
        }

        String g1AllLine() {
            StringBuilder sb = new StringBuilder("objid.w2.g1all: events=").append(g1all.size());
            int n = 0;
            for (String e : g1all) {
                if (n++ == 64) {
                    sb.append(" ...");
                    break;
                }
                sb.append(' ').append(e);
            }
            return sb.toString();
        }

        boolean imageFails() {
            return ObjIdRules.premiseFails(swHidden, classCtx, gccNonJdk, instr);
        }

        String line() {
            StringBuilder sb = new StringBuilder("objid.w2.premise: SW_HIDDEN=").append(swHidden).append(" CLASSCTX=").append(classCtx).append(" GCC_NONJDK=").append(gccNonJdk)
                            .append(" INSTR=").append(instr).append(" LAMBDA_CSM=").append(lambdaCsm.size()).append('/').append(lambdas).append(" => ")
                            .append(ObjIdRules.premiseVerdict(swHidden, classCtx, gccNonJdk, instr, lambdaCsm.size()));
            for (Map.Entry<String, String> e : first.entrySet()) {
                sb.append(' ').append(e.getKey()).append(':').append(e.getValue());
            }
            return sb.append(" ms=").append(ms).toString();
        }
    }

    IdPremise idPremise() {
        IdPremise p = rt.idPremise;
        if (p == null) {
            synchronized (rt.idSites) {
                p = rt.idPremise;
                if (p == null) {
                    p = buildIdPremise();
                    rt.idPremise = p;
                }
            }
        }
        return p;
    }

    /**
     * The premise facts of a method without bytecode from its analysis IR (every invoke the analysis saw; the graph a
     * synthetic method or a body that fails to link is parsed into). No frame = unreadable (fail closed).
     */
    ObjIdRules.BytecodeUses irUses(AnalysisMethod m, ObjIdRules.PremiseApis apis, ObjIdRules.BytecodeUses fallback) {
        LocalFlowGraph fr = rt.bridge.frameOf(m);
        StructuredGraph g = fr != null ? rt.graphOf(fr) : null;
        if (g == null) {
            return fallback;
        }
        ObjIdRules.BytecodeUses u = new ObjIdRules.BytecodeUses();
        for (Invoke inv : g.getInvokes()) {
            ResolvedJavaMethod t = inv.getTargetMethod();
            if (t == null) {
                u.unreadable = true;
                u.why = "ir-unresolved";
                continue;
            }
            ResolvedJavaMethod w = t instanceof AnalysisMethod am ? am.getWrapped() : t;
            Class<?> d = t instanceof AnalysisMethod am ? am.getDeclaringClass().getJavaClass() : null;
            u.callerClass |= "getCallerClass".equals(t.getName()) && (d == jdk.internal.reflect.Reflection.class || d == com.oracle.svm.core.jdk.StackTraceUtils.class ||
                            apis.isCallerClass(w.getDeclaringClass(), w.getName()));
            u.callerSensitive |= ObjIdRules.isCallerSensitive(w);
        }
        return u;
    }

    private IdPremise buildIdPremise() {
        long t0 = System.nanoTime();
        IdPremise p = new IdPremise();
        try {
            jdk.vm.ci.meta.MetaAccessProvider host = com.oracle.graal.pointsto.util.GraalAccess.getOriginalProviders().getMetaAccess();
            ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(host);
            AnalysisType frameType = rt.bridge.optionalAnalysisType(apis.stackFrame);
            List<AnalysisMethod> reachable = new ArrayList<>();
            boolean declaringClassReachable = false;
            String rootWalker = null;
            Map<ResolvedJavaMethod, AnalysisMethod> analysisOf = new java.util.HashMap<>(); // host -> analysis (roots)
            for (AnalysisMethod m : rt.bridge.universeMethods()) {
                analysisOf.putIfAbsent(m.getWrapped(), m);
                if (!m.isReachable() && !m.isImplementationInvoked()) {
                    continue;
                }
                reachable.add(m);
                AnalysisType d = m.getDeclaringClass();
                // G1 (first half): an implementation of StackFrame.getDeclaringClass is reachable
                if (frameType != null && !d.isInterface() && frameType.isAssignableFrom(d) && "getDeclaringClass".equals(m.getName()) && m.getSignature().getParameterCount(false) == 0) {
                    declaringClassReachable = true;
                    p.first.putIfAbsent("SW_DECL", m.format("%H.%n"));
                }
                // G1 (d): a walker factory that is a reflection / JNI / method-handle root (its options come from the
                // caller at run time; the no-arg form is exempt)
                if (rootWalker == null && (m.isDirectRootMethod() || m.isVirtualRootMethod()) && apis.isWalkerFactory(m.getWrapped()) && !"".equals(apis.getInstanceShape(m.getWrapped()))) {
                    rootWalker = "root:" + m.format("%H.%n(%p)");
                }
                // A StackWalker constructor that is a root (reflection / JNI registration)
                if (rootWalker == null && (m.isDirectRootMethod() || m.isVirtualRootMethod()) && apis.isWalkerConstructor(m.getWrapped())) {
                    rootWalker = "root:" + m.format("%H.%n(%p)");
                }
                // G3: getCallerClass registered for reflection / JNI (a root): callable from application code
                if ((m.isDirectRootMethod() || m.isVirtualRootMethod()) && apis.isCallerClass(m.getWrapped().getDeclaringClass(), m.getName())) {
                    p.gccNonJdk++;
                    p.first.putIfAbsent("GCC_NONJDK", "root:" + m.format("%H.%n"));
                }
                // G2: SecurityManager.getClassContext / StackTraceUtils.getClassContext
                if (p.classCtx == 0 && ObjIdRules.PremiseApis.isClassContext(d.getJavaClass(), m.getName())) {
                    p.classCtx = 1;
                    p.first.put("CLASSCTX", m.format("%H.%n"));
                }
            }
            if (declaringClassReachable && rootWalker != null) {
                p.g1Event(rootWalker);
            }
            Set<AnalysisType> hiddenTypes = new java.util.HashSet<>();
            Set<ResolvedJavaMethod> gccCounted = new java.util.HashSet<>();
            Set<ObjIdRules.FwdSite> pendingAt = new java.util.HashSet<>();
            for (AnalysisMethod m : reachable) {
                AnalysisType d = m.getDeclaringClass();
                Class<?> jc = d.getJavaClass();
                boolean hidden = jc != null && jc.isHidden();
                boolean app = jc != null && !ObjIdRules.isRuntimeClass(jc, RecursiveTracking.class.getClassLoader());
                if (declaringClassReachable && ObjIdRules.PremiseApis.isOptionEnumeration(jc, m.getName())) {
                    p.g1Event(m.format("%H.%n")); // G1 (a): the walker options are enumerated
                }
                boolean swRead = declaringClassReachable && !ObjIdRules.isWalkerFamily(jc);
                if (hidden) {
                    hiddenTypes.add(d);
                }
                if (!hidden && !app && !swRead) {
                    continue;
                }
                ObjIdRules.BytecodeUses uses = ObjIdRules.bytecodeUses(m.getWrapped(), apis);
                if (uses.unreadable && "no-bytecode".equals(uses.why)) {
                    uses = irUses(m, apis, uses); // a method without bytecode (a synthetic or link-failure body): its IR
                }
                if (swRead && uses.showHidden) {
                    p.g1Event(m.format("%H.%n")); // G1 (a): SHOW_HIDDEN_FRAMES (or the Option class) named outside the walker itself
                } else if (swRead && uses.walkerBuild) {
                    if (allSetFactories(uses, apis)) {
                        for (Object[] ws : uses.unprovenWalkerSites) {
                            p.pending.add(new Object[]{m.getWrapped(), ws[0]}); // the derivation decides
                            pendingAt.add(new ObjIdRules.FwdSite(m.getWrapped(), (Integer) ws[0]));
                        }
                    } else {
                        p.g1Event(m.format("%H.%n") + "(" + uses.walkerWhy + ")"); // G1 (c): options not provably constant without SHOW_HIDDEN_FRAMES
                    }
                }
                if (app && (uses.callerClass || uses.unreadable)) {
                    gccCounted.add(m.getWrapped());
                    p.gccNonJdk++;
                    p.first.putIfAbsent("GCC_NONJDK", m.format("%H.%n") + (uses.unreadable ? "(" + uses.why + ")" : ""));
                }
                if (hidden && (uses.callerSensitive || uses.unreadable)) {
                    if (p.lambdaCsm.add(d)) {
                        p.first.putIfAbsent("LAMBDA_CSM", m.format("%H.%n") + (uses.unreadable ? "(" + uses.why + ")" : ""));
                    }
                }
            }
            p.lambdas = hiddenTypes.size();
            // G1 (d) / G3: the analysis's own invokes (every call the image can make, including
            // build-time intrinsified method handles and calls inlined before the analysis, which points-to records at
            // the outermost caller's position). A walker factory invoke is accepted only at a bytecode-proven constant
            // construction (or inside the walker itself); a getCallerClass invoke positioned in application code counts.
            {
                Map<ResolvedJavaMethod, ObjIdRules.BytecodeUses> usesOf = new java.util.HashMap<>();
                for (AnalysisMethod m : reachable) {
                    List<Object[]> sites = rt.bridge.invokeSites(m);
                    if (sites == null) {
                        continue; // no flows: the method was never parsed by the analysis, so it makes no image calls
                    }
                    for (Object[] site : sites) {
                        ResolvedJavaMethod t = site[0] instanceof AnalysisMethod am ? am.getWrapped() : (ResolvedJavaMethod) site[0];
                        ResolvedJavaMethod pm = site[1] instanceof AnalysisMethod am ? am.getWrapped() : (ResolvedJavaMethod) site[1];
                        int bci = (Integer) site[2];
                        if (t == null) {
                            continue;
                        }
                        Class<?> pc = pm != null && site[1] instanceof AnalysisMethod pam ? pam.getDeclaringClass().getJavaClass() : null;
                        // A StackWalker constructor called outside the walker itself (a synthesised
                        // reflection / JNI factory method): its options come from the caller
                        if (declaringClassReachable && apis.isWalkerConstructor(t) && !(pc != null && ObjIdRules.isWalkerFamily(pc))) {
                            p.g1Event((pm == null ? "?" : pm.format("%H.%n")) + "@" + bci + "(ctor-flow:" + t.format("%H.%n(%p)") + ")");
                        }
                        if (declaringClassReachable && apis.isWalkerFactory(t) && !"".equals(apis.getInstanceShape(t))) {
                            boolean ok;
                            if (pm == null) {
                                ok = false;
                            } else if (pc != null && ObjIdRules.isWalkerFamily(pc)) {
                                ok = true; // inside the walker: its own callers are checked at their invokes of it
                            } else {
                                ok = usesOf.computeIfAbsent(pm, k -> ObjIdRules.bytecodeUses(k, apis)).provenWalkerBcis.contains(bci) ||
                                                pendingAt.contains(new ObjIdRules.FwdSite(pm, bci)); // decided by the derivation below
                            }
                            if (!ok) {
                                p.g1Event((pm == null ? "?" : pm.format("%H.%n")) + "@" + bci + "(flow:" + t.format("%n(%p)") + ")");
                            }
                        }
                        if (apis.isCallerClass(t.getDeclaringClass(), t.getName()) && pc != null && !ObjIdRules.isRuntimeClass(pc, RecursiveTracking.class.getClassLoader()) && gccCounted.add(pm)) {
                            p.gccNonJdk++;
                            p.first.putIfAbsent("GCC_NONJDK", pm.format("%H.%n") + "@" + bci + "(flow)");
                        }
                    }
                }
            }
            // The derived-factory rule over the pending sites (each fails G1 unless proven)
            if (!p.pending.isEmpty()) {
                deriveG1(p, apis, analysisOf);
            }
            // G1 (second half, b): an image-heap StackWalker configured with SHOW_HIDDEN_FRAMES
            if (declaringClassReachable) {
                AnalysisType walkerType = rt.bridge.optionalAnalysisType(apis.stackWalker);
                Map<AnalysisType, Set<ImageHeapConstant>> objs = rt.bridge.heapObjects();
                if (objs == null) {
                    p.g1Event("heap-unavailable");
                } else if (walkerType != null && objs.get(walkerType) != null) {
                    for (ImageHeapConstant k : objs.get(walkerType)) {
                        JavaConstant hc = k.getHostedObject();
                        Object w = hc != null ? com.oracle.graal.pointsto.util.GraalAccess.getOriginalSnippetReflection().asObject(Object.class, hc) : null;
                        if (!(w instanceof StackWalker sw) || ObjIdRules.showsHiddenFrames(sw)) {
                            p.g1Event("heap-walker");
                            break;
                        }
                    }
                }
            }
            if (p.swHidden == 0) {
                p.first.remove("SW_DECL");
            }
            // G4: an instantiated implementation of java.lang.instrument.Instrumentation
            AnalysisType instr = rt.bridge.optionalAnalysisType(apis.instrumentation);
            AnalysisType impl = instr != null ? ObjIdRules.firstInstantiated(instr) : null;
            if (impl != null) {
                p.instr = 1;
                p.first.put("INSTR", impl.toJavaName(true));
            }
        } catch (Throwable t) {
            p.g1all.add("ERROR(" + t.getClass().getSimpleName() + ")"); // the census lists the error path
            p.swHidden = 1; // unreadable: fail closed (the ordinary caller fan everywhere)
            p.first.put("ERROR", t.getClass().getSimpleName());
        }
        p.ms = (System.nanoTime() - t0) / 1_000_000;
        return p;
    }

    /** A (c) failure is pending iff every unproven construction is a single resolved factory with an option-set parameter. */
    static boolean allSetFactories(ObjIdRules.BytecodeUses uses, ObjIdRules.PremiseApis apis) {
        if (uses.unprovenWalkerSites.isEmpty()) {
            return false;
        }
        for (Object[] ws : uses.unprovenWalkerSites) {
            if (ws[1] == null || apis.setParamIndex((ResolvedJavaMethod) ws[1]) < 0) {
                return false;
            }
        }
        return true;
    }

    /** Run the derivation over every pending site; a failure is a G1 event with the derived reason. */
    private void deriveG1(IdPremise p, ObjIdRules.PremiseApis apis, Map<ResolvedJavaMethod, AnalysisMethod> analysisOf) {
        ObjIdRules.FwdIndex fx = new ObjIdRules.FwdIndex();
        for (AnalysisMethod m : rt.bridge.universeMethods()) {
            if (!m.isReachable() && !m.isImplementationInvoked()) {
                continue;
            }
            List<Object[]> sites = rt.bridge.invokeSites(m);
            if (sites == null) {
                continue;
            }
            for (Object[] site : sites) {
                ResolvedJavaMethod t = site[0] instanceof AnalysisMethod am ? am.getWrapped() : (ResolvedJavaMethod) site[0];
                ResolvedJavaMethod pm = site[1] instanceof AnalysisMethod am ? am.getWrapped() : (ResolvedJavaMethod) site[1];
                if (t != null) {
                    List<ResolvedJavaMethod> callees = null;
                    if (site.length > 3 && site[3] instanceof java.util.Collection<?> c) {
                        callees = new ArrayList<>();
                        for (Object o : c) {
                            callees.add(o instanceof AnalysisMethod am ? am.getWrapped() : (ResolvedJavaMethod) o);
                        }
                    }
                    fx.add(t, pm, (Integer) site[2], callees);
                }
            }
        }
        Map<ResolvedJavaMethod, ObjIdRules.FwdFacts> facts = new java.util.HashMap<>();
        ObjIdRules.FwdWorld world = new ObjIdRules.FwdWorld() {
            @Override
            public ObjIdRules.FwdFacts facts(ResolvedJavaMethod m) {
                return facts.computeIfAbsent(m, k -> ObjIdRules.forwardFacts(k, apis));
            }

            @Override
            public java.util.Collection<ObjIdRules.FwdSite> callers(ResolvedJavaMethod m) {
                return fx.callers(m);
            }

            @Override
            public boolean root(ResolvedJavaMethod m) {
                List<ResolvedJavaMethod> all = new ArrayList<>(ObjIdRules.overridden(m));
                all.add(m);
                for (ResolvedJavaMethod x : all) {
                    AnalysisMethod am = analysisOf.get(x);
                    if (am != null && (am.isDirectRootMethod() || am.isVirtualRootMethod())) {
                        return true;
                    }
                }
                return false;
            }

            @Override
            public java.util.Collection<ResolvedJavaMethod> calleesAt(ResolvedJavaMethod m, int bci, ResolvedJavaMethod t) {
                return fx.calleesAt(m, bci, t);
            }

            @Override
            public int factorySetParam(ResolvedJavaMethod t) {
                return apis.setParamIndex(t);
            }
        };
        ObjIdRules.FwdProver prover = new ObjIdRules.FwdProver(world);
        for (Object[] ps : p.pending) {
            ResolvedJavaMethod m = (ResolvedJavaMethod) ps[0];
            int bci = (Integer) ps[1];
            ObjIdRules.FwdVerdict v = prover.provePending(m, bci);
            ResolvedJavaMethod t = world.facts(m).target.get(bci);
            String site = ObjIdRules.FwdProver.name(m) + "@" + bci;
            p.g1fwdLines.add("[objid-g1fwd] site=" + site + " verdict=" + (v.ok() ? "PROVEN" : "FAIL(" + v.reason() + ")") + " depth=" + v.depth() + " chain=[" + v.chain() + "]");
            if (v.ok()) {
                p.g1fwdProven++;
                p.g1fwdMaxDepth = Math.max(p.g1fwdMaxDepth, v.depth());
            } else {
                p.g1fwdFailed++;
                p.g1Event(m.format("%H.%n") + "(" + (t == null ? "?" : t.format("%H.%n(%p)")) + "@" + bci + ")(" + v.reason() + ")");
            }
        }
    }

    /** The census label of an entry path (a caller site, or the link kind of a model / desugared / fold entry). */
    String entryLabel(CallPath p) {
        if (p == null) {
            return "null";
        }
        if (p.call instanceof LocalFlowGraph.LocalVertex cv) {
            return rt.frameName(p.callerFrame) + "@" + cv.bci;
        }
        String kind = p.isFold() ? "fold" : p.call == null ? "null" : p.call.getClass().getSimpleName();
        return rt.frameName(p.callerFrame) + "@" + kind;
    }

    /**
     * Guard part (b), the heap half: the image-heap slots holding C's Class object (its {@code DynamicHub}); fail
     * closed (counted as one holder) when the hub or the holder index is unavailable. Pending READ slots are not
     * counted here: {@link #pendingCheck} decides them.
     */
    int classHolders(AnalysisType c, String[] detail) {
        Object hub = hubConstantData(c);
        if (hub == null && rt.hubConstantsFailed) {
            detail[0] = " hub=unavailable";
            return 1;
        }
        if (hub == null) {
            Map<AnalysisType, Set<ImageHeapConstant>> objs = rt.bridge.heapObjects();
            detail[0] = " hub=none";
            return objs == null ? 1 : 0; // no hub in the snapshot: nothing holds it (unless the snapshot is unavailable)
        }
        Map<Object, List<Object[]>> idx = rt.holderIndex();
        if (idx == null || rt.holderIndexProblem != null) {
            detail[0] = " holderIndex=" + rt.holderIndexProblem;
            return 1;
        }
        List<Object[]> hs = idx.getOrDefault(hub, List.of());
        if (!hs.isEmpty()) {
            StringBuilder sb = new StringBuilder(" holderBy=[");
            for (int i = 0; i < hs.size() && i < 4; i++) {
                Object h = hs.get(i)[0];
                Object mem = hs.get(i)[1];
                sb.append(i == 0 ? "" : ",").append(h instanceof ImageHeapConstant ihc && ihc.getType() instanceof AnalysisType t ? t.toJavaName(false) : String.valueOf(h))
                                .append('.').append(memberName(mem));
            }
            detail[0] = sb.append(']').toString();
        }
        return hs.size();
    }

    /** The {@code ConstantData} of C's hub in the image-heap snapshot, or null. Built once over the snapshot's Class objects. */
    Object hubConstantData(AnalysisType c) {
        Map<AnalysisType, Object> m = rt.hubConstants;
        if (m == null) {
            synchronized (rt.idSites) {
                m = rt.hubConstants;
                if (m == null) {
                    m = new java.util.HashMap<>();
                    Map<AnalysisType, Set<ImageHeapConstant>> objs = rt.bridge.heapObjects();
                    AnalysisType classType = rt.bridge.lookupJavaType(Class.class);
                    try {
                        if (objs != null && classType == null) {
                            rt.hubConstantsFailed = true; // Class itself cannot be looked up: fail closed
                        } else if (objs != null && objs.get(classType) != null) {
                            for (ImageHeapConstant k : objs.get(classType)) {
                                AnalysisType t = rt.bridge.classConstantType(k); // throws when the lookup is unavailable
                                if (t != null) {
                                    m.put(t, k.getConstantData());
                                }
                            }
                        }
                    } catch (Throwable t) {
                        rt.hubConstantsFailed = true; // an unavailable lookup fails closed, never "no holder"
                    }
                    rt.hubConstants = m;
                }
            }
        }
        return m.get(c);
    }

    /**
     * Guard part (c): C is reachable by name or by reflective enumeration: registered for {@code Class.forName}, for JNI, as
     * a reflectively registered class's inner class, or with reflectively registered members. Null = not registered;
     * an unreadable registry answers a reason (fail closed).
     */
    String registryReason(AnalysisType c) {
        try {
            Class<?> jc = c.getJavaClass();
            if (jc == null) {
                return "noClass";
            }
            if (forNameRegistered().contains(jc.getName())) {
                return "forName";
            }
            if (org.graalvm.nativeimage.ImageSingletons.contains(com.oracle.svm.core.jni.access.JNIReflectionDictionary.class)) {
                for (com.oracle.svm.core.jni.access.JNIAccessibleClass jac : com.oracle.svm.core.jni.access.JNIReflectionDictionary.currentLayer().getClasses()) {
                    if (jac != null && jac.getClassObject() == jc) {
                        return "jni";
                    }
                }
            }
            if (org.graalvm.nativeimage.ImageSingletons.contains(com.oracle.svm.hosted.reflect.ReflectionHostedSupport.class)) {
                var rs = org.graalvm.nativeimage.ImageSingletons.lookup(com.oracle.svm.hosted.reflect.ReflectionHostedSupport.class);
                var ex = rs.getReflectionExecutables().get(c);
                if (ex != null && !ex.isEmpty()) {
                    return "reflectExecutables";
                }
                var fs = rs.getReflectionFields().get(c);
                if (fs != null && !fs.isEmpty()) {
                    return "reflectFields";
                }
                for (Set<Class<?>> inner : rs.getReflectionInnerClasses().values()) {
                    if (inner.contains(jc)) {
                        return "innerClass";
                    }
                }
            }
            return null;
        } catch (Throwable t) {
            return "unreadable:" + t.getClass().getSimpleName();
        }
    }

    /**
     * The named guard's registration routes = {@link #registryReason} plus three routes to an instance without a framed
     * birth: a dynamic proxy class, a serialization target and a class registered for {@code Unsafe.allocateInstance}.
     * Unreadable = a reason (fail closed).
     */
    String namedRegistryReason(AnalysisType c) {
        String w2 = registryReason(c);
        if (w2 != null) {
            return w2;
        }
        try {
            Class<?> jc = c.getJavaClass();
            if (java.lang.reflect.Proxy.isProxyClass(jc)) {
                return "proxy";
            }
            Set<Class<?>> ser = serializationTargets();
            if (ser == null) {
                return "unreadable:serialization";
            }
            if (ser.contains(jc)) {
                return "serialization";
            }
            Object m = com.oracle.svm.util.ReflectionUtil.readField(com.oracle.svm.core.hub.ClassForNameSupport.class, "unsafeInstantiatedClasses",
                            com.oracle.svm.core.hub.ClassForNameSupport.currentLayer());
            if (!(m instanceof org.graalvm.collections.EconomicMap<?, ?>)) {
                return "unreadable:unsafeInstantiated";
            }
            @SuppressWarnings("unchecked")
            org.graalvm.collections.EconomicMap<Object, ?> um = (org.graalvm.collections.EconomicMap<Object, ?>) m;
            if (um.containsKey(jc)) {
                return "unsafeAllocated";
            }
            return null;
        } catch (Throwable t) {
            return "unreadable:" + t.getClass().getSimpleName();
        }
    }

    /** The serialization target classes (the hosted registry's hub keys and constructor-accessor declaring classes); null = unreadable. */
    private Set<Class<?>> serializationTargets() {
        if (rt.serializationDone) {
            return rt.serializationTargets;
        }
        synchronized (rt.idSites) {
            if (!rt.serializationDone) {
                Set<Class<?>> out = new java.util.HashSet<>();
                try {
                    Class<?> sc = com.oracle.svm.core.reflect.serialize.SerializationSupport.class;
                    Object sup = com.oracle.svm.core.reflect.serialize.SerializationSupport.currentLayer();
                    Object classes = com.oracle.svm.util.ReflectionUtil.readField(sc, "classes", sup);
                    var cur = ((org.graalvm.collections.EconomicMap<?, ?>) classes).getKeys();
                    for (Object k : cur) {
                        if (!(k instanceof com.oracle.svm.core.reflect.serialize.SerializationSupport.DynamicHubKey hk)) {
                            throw new IllegalStateException("key " + k);
                        }
                        out.add(hk.hub().getHostedJavaClass());
                    }
                    Object acc = com.oracle.svm.util.ReflectionUtil.readField(sc, "constructorAccessors", sup);
                    for (Object k : ((org.graalvm.collections.EconomicMap<?, ?>) acc).getKeys()) {
                        out.add(((com.oracle.svm.core.reflect.serialize.SerializationSupport.SerializationLookupKey) k).getDeclaringClass());
                    }
                    rt.serializationTargets = out;
                } catch (Throwable t) {
                    rt.serializationTargets = null;
                }
                rt.serializationDone = true;
            }
            return rt.serializationTargets;
        }
    }

    /** The names registered for {@code Class.forName} (the hosted registry, read once; a read failure propagates: fail closed). */
    private Set<String> forNameRegistered() {
        Set<String> n = rt.forNameNames;
        if (n == null) {
            n = com.oracle.svm.core.hub.ClassForNameSupport.currentLayer().getKnownClassNames();
            rt.forNameNames = n;
        }
        return n;
    }

    /**
     * The birth index: one pass over the framed graphs (as the closed-field read index): per type, its framed allocation
     * births ({@code NewInstance}/{@code AllocatedObject}) and its Class constants (also of arrays of it, guard part (b)); the
     * reachable methods without a frame: their declaring classes, and from their bytecode the types they allocate or
     * load as a class constant and whether they hold an invokedynamic (their class then counts as a capture host). Fails
     * closed (no class passes the guard) on an enumeration problem, an unreadable unframed body, or a build mode outside
     * the closed world.
     */
    static final class IdBirthIndex {
        final Map<AnalysisType, List<Object[]>> births = new java.util.HashMap<>();
        final Map<AnalysisType, Integer> classConstants = new java.util.HashMap<>();
        final Set<AnalysisType> unframedDeclaring = new java.util.HashSet<>();
        /** The nest hosts of the classes declaring an unframed method with an {@code invokedynamic} (capture hosts). */
        final Set<Class<?>> unframedIndyHosts = new java.util.HashSet<>();
        final Set<AnalysisType> unframedBirths = new java.util.HashSet<>();
        /** Types with a framed birth that has no AllocatedObject (a virtual instance committed only as another object's slot value). */
        final Set<AnalysisType> unwalkableBirths = new java.util.HashSet<>();
        /** Census mode only: per elemental type, its framed Class constants with a use outside the harmless list. */
        final Map<AnalysisType, Integer> harmfulClassConstants = new java.util.HashMap<>();
        /** Census mode only: up to 6 positions of the harmful Class constants per type (print-only). */
        final Map<AnalysisType, List<String>> harmfulClassConstantSites = new java.util.HashMap<>();
        /** Census mode only, print-only: per declaring type, its unframed methods with their cause. */
        final Map<AnalysisType, List<String>> unframedWhy = new java.util.HashMap<>();
        final Map<AnalysisType, Set<ObjRetRules.UnframedCause>> unframedCauses = new java.util.HashMap<>();
        /** Census mode only: per elemental type, the unframed methods allocating / ldc-loading it, with causes. */
        final Map<AnalysisType, List<String>> unframedBirthBy = new java.util.HashMap<>();
        final Map<AnalysisType, Set<ObjRetRules.UnframedCause>> unframedBirthCauses = new java.util.HashMap<>();
        /** objret on: per declaring type its unframed (non-abstract) reachable methods (the INLINED_ONLY exception). */
        final Map<AnalysisType, List<AnalysisMethod>> unframedMethodsOf = new java.util.HashMap<>();
        /** objret on: per elemental type the unframed methods whose bytecode allocates / ldc-loads it. */
        final Map<AnalysisType, Set<AnalysisMethod>> unframedBirthMethodsOf = new java.util.HashMap<>();
        /** objret on (the self-slot run-time readers): companion reads ({@code DynamicHub.companion} / {@code getCompanion()}) not audited. */
        final Set<String> companionReaders = new java.util.TreeSet<>();
        int companionReads;
        long framed;
        long unframed;
        long opaque;
        long sites;
        long universe;
        long frameMethods;
        long frameCount = -1;
        long ms;
        String failReason;
    }

    IdBirthIndex idBirthIndex() {
        IdBirthIndex x = rt.idBirthIndex;
        if (x == null) {
            synchronized (rt.idSites) {
                x = rt.idBirthIndex;
                if (x == null) {
                    x = buildIdBirthIndex();
                    rt.idBirthIndex = x;
                }
            }
        }
        return x;
    }

    private IdBirthIndex buildIdBirthIndex() {
        long t0 = System.nanoTime();
        IdBirthIndex x = new IdBirthIndex();
        try {
            String mode = closedWorldGuard();
            if (mode != null) {
                x.failReason = "build-mode:" + mode;
            }
            x.frameCount = rt.bridge.frameCount();
            for (AnalysisMethod m : rt.bridge.universeMethods()) {
                x.universe++;
                LocalFlowGraph fr = rt.bridge.frameOf(m);
                if (fr != null) {
                    x.frameMethods++;
                }
                if (!m.isReachable() && !m.isImplementationInvoked()) {
                    continue;
                }
                StructuredGraph g = fr != null ? rt.graphOf(fr) : null;
                if (g == null) {
                    x.unframed++;
                    if (!m.isAbstract()) {
                        x.unframedDeclaring.add(m.getDeclaringClass());
                        if (OBJRET_ON) {
                            x.unframedMethodsOf.computeIfAbsent(m.getDeclaringClass(), k -> new ArrayList<>()).add(m);
                            ObjRetRules.UnframedCause uc = unframedCauseOf(m, fr);
                            x.unframedWhy.computeIfAbsent(m.getDeclaringClass(), k -> new ArrayList<>()).add(m.format("%n(%p)") + ":" + uc + unframedFlags(m));
                            x.unframedCauses.computeIfAbsent(m.getDeclaringClass(), k -> java.util.EnumSet.noneOf(ObjRetRules.UnframedCause.class)).add(uc);
                        }
                    }
                    if (!unframedClassUses(m, x)) {
                        x.opaque++;
                    }
                    continue;
                }
                x.framed++;
                for (Node n : g.getNodes()) {
                    if (OBJRET_ON) {
                        companionRead(n, m, x); // the self-slot exception's run-time readers
                    }
                    if (n instanceof CommitAllocationNode can) {
                        // a committed virtual instance without its own AllocatedObject (it lives only as a slot value of
                        // another committed object, e.g. a varargs array): a real birth no walk can start from
                        for (VirtualInstanceNode vo : unwalkableInstances(can)) {
                            if (vo.type() instanceof AnalysisType vt) {
                                x.unwalkableBirths.add(vt);
                            }
                        }
                    } else if (n instanceof NewInstanceNode || n instanceof NewInstanceWithExceptionNode || n instanceof AllocatedObjectNode) {
                        AnalysisType t = exactTypeOf((ValueNode) n);
                        if (t != null) {
                            x.births.computeIfAbsent(t, k -> new ArrayList<>(1)).add(new Object[]{fr, n});
                            x.sites++;
                        }
                    } else if (n instanceof ConstantNode cn && cn.getValue() instanceof JavaConstant jc && jc.getJavaKind() == JavaKind.Object && !jc.isNull()) {
                        AnalysisType t = rt.bridge.classConstantType(jc);
                        if (t != null) {
                            AnalysisType e = t;
                            while (e.isArray()) {
                                e = e.getComponentType();
                            }
                            x.classConstants.merge(e, 1, Integer::sum);
                            String[] cwhy = OBJRET_ON ? new String[1] : null;
                            if (OBJRET_ON && !rt.objectReturn.harmlessClassUses(cn, cwhy)) {
                                x.harmfulClassConstants.merge(e, 1, Integer::sum); // guard part (b): per constant
                                List<String> cl = x.harmfulClassConstantSites.computeIfAbsent(e, k -> new ArrayList<>());
                                if (cl.size() < 6) {
                                    cl.add(m.format("%H.%n") + "(" + cwhy[0] + ")"); // where (print-only)
                                }
                            }
                        }
                    }
                }
            }
            if (x.failReason == null) {
                x.failReason = indexFailure(x.universe, x.frameMethods, x.frameCount);
            }
            if (x.failReason == null && x.opaque > 0) {
                x.failReason = "opaque-unframed=" + x.opaque;
            }
        } catch (Throwable t) {
            x.failReason = "index:" + t.getClass().getSimpleName();
        }
        x.ms = (System.nanoTime() - t0) / 1_000_000;
        return x;
    }

    /**
     * An unframed method's class uses (bytecode): {@code new}/{@code anewarray}/{@code multianewarray} and {@code ldc}
     * class constants name their types ({@link IdBirthIndex#unframedBirths}); an {@code invokedynamic} makes the
     * declaring class's nest host a capture host. False = a body whose bytecode cannot be read (fail closed). Abstract and native
     * methods have no Java body.
     */
    private boolean unframedClassUses(AnalysisMethod m, IdBirthIndex x) {
        ResolvedJavaMethod w = m.getWrapped();
        if (w.isAbstract() || w.isNative()) {
            return true;
        }
        byte[] code;
        try {
            code = w.getCode();
        } catch (Throwable t) {
            code = null;
        }
        if (code == null) {
            return false;
        }
        boolean ok = true;
        jdk.graal.compiler.bytecode.BytecodeStream s = new jdk.graal.compiler.bytecode.BytecodeStream(code);
        jdk.vm.ci.meta.ConstantPool cp = w.getConstantPool();
        while (s.currentBC() != jdk.graal.compiler.bytecode.Bytecodes.END) {
            int bc = s.currentBC();
            try {
                if (bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKEDYNAMIC) {
                    Class<?> dc = m.getDeclaringClass().getJavaClass();
                    Class<?> nh = dc != null ? dc.getNestHost() : null;
                    if (nh == null) {
                        ok = false; // the capture host cannot be named: fail closed
                    } else {
                        x.unframedIndyHosts.add(nh);
                    }
                } else if (bc == jdk.graal.compiler.bytecode.Bytecodes.NEW || bc == jdk.graal.compiler.bytecode.Bytecodes.ANEWARRAY ||
                                bc == jdk.graal.compiler.bytecode.Bytecodes.MULTIANEWARRAY) {
                    noteUnframedType(cp.lookupType(s.readCPI(), bc), x, m);
                } else if (bc == jdk.graal.compiler.bytecode.Bytecodes.LDC || bc == jdk.graal.compiler.bytecode.Bytecodes.LDC_W) {
                    Object k = cp.lookupConstant(s.readCPI());
                    if (k instanceof jdk.vm.ci.meta.JavaType jt) {
                        noteUnframedType(jt, x, m);
                    }
                } else if (OBJRET_ON && (bc == jdk.graal.compiler.bytecode.Bytecodes.GETFIELD || bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKEVIRTUAL ||
                                bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKESPECIAL)) {
                    unframedCompanionRead(cp, s.readCPI(), bc, w, m, x); // never changes ok (the lambda index is unaffected)
                }
            } catch (Throwable t) {
                ok = false;
            }
            s.next();
        }
        return ok;
    }

    private void noteUnframedType(jdk.vm.ci.meta.JavaType jt, IdBirthIndex x, AnalysisMethod by) {
        if (jt instanceof ResolvedJavaType resolved) {
            ResolvedJavaType e = resolved.getElementalType();
            AnalysisType at = e instanceof AnalysisType a ? a : rt.bridge.optionalAnalysisType(e);
            if (at != null) {
                x.unframedBirths.add(at);
                if (OBJRET_ON) {
                    x.unframedBirthMethodsOf.computeIfAbsent(at, k -> new java.util.LinkedHashSet<>()).add(by);
                    ObjRetRules.UnframedCause uc = unframedCauseOf(by, rt.bridge.frameOf(by));
                    List<String> l = x.unframedBirthBy.computeIfAbsent(at, k -> new ArrayList<>());
                    String w = by.format("%H.%n(%p)") + ":" + uc;
                    if (!l.contains(w)) {
                        l.add(w);
                    }
                    x.unframedBirthCauses.computeIfAbsent(at, k -> java.util.EnumSet.noneOf(ObjRetRules.UnframedCause.class)).add(uc);
                }
            }
        }
    }

    /** {@code DynamicHub.companion}: in the analysis universe DynamicHub substitutes {@code java.lang.Class} (both names count). */
    private static boolean isCompanionField(jdk.vm.ci.meta.JavaField f) {
        return f != null && "companion".equals(f.getName()) && ObjRetRules.classHolder(f.getDeclaringClass().toJavaName(true));
    }

    private static boolean isGetCompanion(jdk.vm.ci.meta.JavaMethod t) {
        return t != null && "getCompanion".equals(t.getName()) && ObjRetRules.classHolder(t.getDeclaringClass().toJavaName(true));
    }

    /**
     * The self-slot run-time readers: a framed read of a hub's companion ({@code LoadField DynamicHub.companion}, an invoke of
     * {@code DynamicHub.getCompanion()}) is audited when its method is declared by an audited SVM-internal consumer
     * ({@link ObjRetRules#companionReaderAudited}) or the companion value is only the object of field reads / writes and
     * null checks (it never escapes: reading a slot of T's own companion needs T's hub already). Anything else is recorded
     * (the self-slot discount then fails closed for every class).
     */
    private static void companionRead(Node n, AnalysisMethod m, IdBirthIndex x) {
        ValueNode v = null;
        if (n instanceof LoadFieldNode lf && isCompanionField(lf.field())) {
            v = lf;
        } else if (n instanceof MethodCallTargetNode mct && isGetCompanion(mct.targetMethod()) && mct.invoke() != null) {
            v = mct.invoke().asNode() instanceof ValueNode iv ? iv : null;
            if (v == null) {
                x.companionReaders.add(m.format("%H.%n(%p)") + "(invoke)");
                return;
            }
        } else if (n instanceof ConstantNode cn && cn.getValue() instanceof ImageHeapConstant ihc && ihc.getType() != null &&
                        "com.oracle.svm.core.hub.DynamicHubCompanion".equals(ihc.getType().toJavaName(true))) {
            // A companion read folded into a constant (DynamicHub.companion is final: hub.companion on a
            // constant hub canonicalises to the companion constant), judged like a read. Object constants of the
            // analysis graphs are ImageHeapConstants; snippet / lowering-level reads (class-init and allocation
            // snippets) are not analysis graphs and use the companion as a field base only.
            v = cn;
        }
        if (v == null) {
            return;
        }
        x.companionReads++;
        String holder = m.getDeclaringClass().toJavaName(true);
        if (ObjRetRules.companionReaderAudited(holder) || companionFieldUseOnly(v)) {
            return;
        }
        x.companionReaders.add(m.format("%H.%n(%p)"));
    }

    /** The companion value's uses are only the object of field loads / stores, null checks and Pis (frame states ignored). */
    private static boolean companionFieldUseOnly(ValueNode v0) {
        java.util.ArrayDeque<ValueNode> work = new java.util.ArrayDeque<>();
        Set<Node> seen = new java.util.HashSet<>();
        work.add(v0);
        while (!work.isEmpty()) {
            ValueNode v = work.poll();
            if (!seen.add(v)) {
                continue;
            }
            for (Node u : v.usages()) {
                if (u instanceof VirtualState || u instanceof jdk.graal.compiler.nodes.calc.IsNullNode) {
                    continue;
                }
                if (u instanceof PiNode pi && pi.getOriginalNode() == v) {
                    work.add(pi);
                    continue;
                }
                if (u instanceof LoadFieldNode lf && lf.object() == v) {
                    continue;
                }
                if (u instanceof StoreFieldNode sf && sf.object() == v && sf.value() != v) {
                    continue;
                }
                return false;
            }
        }
        return true;
    }

    /** The self-slot run-time readers in an unframed body (bytecode): a getfield of the companion or a call of getCompanion outside the audited consumers. */
    private static void unframedCompanionRead(jdk.vm.ci.meta.ConstantPool cp, int cpi, int bc, ResolvedJavaMethod w, AnalysisMethod m, IdBirthIndex x) {
        try {
            boolean read = bc == jdk.graal.compiler.bytecode.Bytecodes.GETFIELD ? isCompanionField(cp.lookupField(cpi, w, bc)) : isGetCompanion(lookupMethodIn(cp, cpi, bc, w));
            if (read) {
                x.companionReads++;
                if (!ObjRetRules.companionReaderAudited(m.getDeclaringClass().toJavaName(true))) {
                    x.companionReaders.add("unframed:" + m.format("%H.%n(%p)"));
                }
            }
        } catch (Throwable t) {
            x.companionReaders.add("unreadable(" + t.getClass().getSimpleName() + "):" + m.format("%H.%n(%p)")); // fail closed (the self-slot discount only)
        }
    }

    /** Print-only: why a reachable method has no frame, from the analysis method's state. */
    ObjRetRules.UnframedCause unframedCauseOf(AnalysisMethod m, LocalFlowGraph fr) {
        boolean pointsTo = m instanceof com.oracle.graal.pointsto.meta.PointsToAnalysisMethod;
        boolean flows = false;
        boolean stub = false;
        boolean init = false;
        boolean sim = false;
        try {
            if (m instanceof com.oracle.graal.pointsto.meta.PointsToAnalysisMethod ptm) {
                var mtf = ptm.getTypeFlow();
                flows = mtf != null && mtf.flowsGraphCreated();
                stub = flows && mtf.getMethodFlowsGraph().isStub();
            }
            init = m.getDeclaringClass().isInitialized();
            sim = rt.bridge.classInitSimulated(m.getDeclaringClass());
        } catch (Throwable t) {
            return ObjRetRules.UnframedCause.OTHER;
        }
        return ObjRetRules.unframedCause(m.isClassInitializer(), init, sim, m.isNative(), m.isIntrinsicMethod(), m.isImplementationInvoked(), m.isInlined(), pointsTo, flows, stub,
                        fr != null);
    }

    /** Print-only: the analysis flags of an unframed method, and why it is reachable. */
    private static String unframedFlags(AnalysisMethod m) {
        StringBuilder sb = new StringBuilder("{impl=").append(m.isImplementationInvoked()).append(",inl=").append(m.isInlined()).append(",intr=").append(m.isIntrinsicMethod())
                        .append(",root=").append(m.isDirectRootMethod() || m.isVirtualRootMethod()).append(",bridge=").append(m.isBridge()).append(",synth=").append(m.isSynthetic())
                        .append(",wrapped=").append(m.getWrapped().getClass().getSimpleName());
        Object why = m.isImplementationInvoked() ? m.getImplementationInvokedReason() : m.isInlined() ? "inlined" : null;
        if (why != null) {
            String w = String.valueOf(why).replace('\n', ' ');
            sb.append(",reason=").append(w.length() > 160 ? w.substring(0, 160) + "..." : w);
        }
        return sb.append('}').toString();
    }

    /** The census line part {@code objid{…}} (print-only). */
    String objidCensus() {
        Map<String, Counter> noq = new TreeMap<>();
        Map<String, Counter> guard = new TreeMap<>();
        int usable = 0;
        int precise = 0;
        int fellBack = 0;
        Map<String, Counter> firstRef = new TreeMap<>();
        List<String> lines = new ArrayList<>();
        List<String> drops = new ArrayList<>();
        for (IdQuery q : rt.idQueries.values()) {
            if (q.noq != null) {
                bump(noq, q.noq.name());
                continue;
            }
            bump(guard, q.fail == null ? "pass" : q.fail.name());
            if (q.fail != null) {
                if (q.fail != ObjIdRules.GuardFail.NO_FRAMED_BIRTH || q.births.size() > 0) {
                    lines.add("[sug-fwd-rtrack-objid] class=" + q.type.toJavaName(true) + " guard=" + q.fail + " " + q.detail);
                }
                continue;
            }
            if (!q.usable()) {
                continue;
            }
            usable++;
            Set<RTrackRefusal> refs = java.util.EnumSet.noneOf(RTrackRefusal.class);
            for (RAtom a : q.atoms) {
                refs.addAll(a.table.refusalsSnapshot());
            }
            if (refs.isEmpty()) {
                precise++;
            } else {
                fellBack++;
                for (RTrackRefusal r : refs) {
                    bump(firstRef, r.name());
                }
            }
            StringBuilder sb = new StringBuilder("[sug-fwd-rtrack-objid] class=").append(q.type.toJavaName(true)).append(" guard=pass ").append(q.detail)
                            .append(" refused=").append(refs);
            List<String> bs = new ArrayList<>();
            for (RAtom a : q.atoms) {
                bs.add(rt.frameName(a.birthFrame));
            }
            java.util.Collections.sort(bs);
            sb.append(" birthIn=").append(bs);
            // The caller set itself = the query tables' entry paths per frame (every delivery branch:
            // the identity hooks and the OWNER(query) branch read these lists)
            Map<LocalFlowGraph, Set<String>> byFrame = new java.util.HashMap<>();
            for (RAtom a : q.atoms) {
                for (Map.Entry<LocalFlowGraph, EntryList<CallPath>> e : a.table.entryPaths.entrySet()) {
                    Set<String> es = byFrame.computeIfAbsent(e.getKey(), k -> new java.util.TreeSet<>());
                    EntryList<CallPath> l = e.getValue();
                    for (int i = 0; i < l.size(); i++) {
                        es.add(entryLabel(l.get(i)));
                    }
                }
            }
            List<String> fl = new ArrayList<>();
            for (Map.Entry<LocalFlowGraph, Set<String>> e : byFrame.entrySet()) {
                fl.add(rt.frameName(e.getKey()) + "<-" + e.getValue());
            }
            java.util.Collections.sort(fl);
            sb.append(" entries=").append(fl);
            lines.add(sb.toString());
            if (refs.isEmpty()) {
                // The dangerous direction: a caller site of a hooked frame kept by the caller-index filter that the precise set lacks
                for (Map.Entry<LocalFlowGraph, Set<String>> e : byFrame.entrySet()) {
                    if (!rt.objidHookedFrames.contains(e.getKey())) {
                        continue;
                    }
                    dropLines(e.getKey(), e.getValue(), drops);
                }
                for (LocalFlowGraph hf : rt.objidHookedFrames) {
                    AnalysisMethod fm = rt.bridge.methodOf(hf);
                    if (!byFrame.containsKey(hf) && fm != null && fm.getDeclaringClass().equals(q.type)) {
                        dropLines(hf, Set.of(), drops); // hooked, no entry at all: every kept site is a drop
                    }
                }
            }
        }
        java.util.Collections.sort(drops);
        for (String l : drops) {
            System.out.println(l);
        }
        java.util.Collections.sort(lines);
        for (String l : lines) {
            System.out.println(l);
        }
        IdBirthIndex x = rt.idBirthIndex;
        StringBuilder sb = new StringBuilder(" objid{frames=")
                        .append(rt.objidFrames.get()).append(" classes=").append(rt.idQueries.size())
                        .append(" noq=").append(top(noq)).append(" guard=").append(top(guard)).append(" usable=").append(usable).append(" precise=").append(precise)
                        .append(" fellBack=").append(fellBack).append(" refusedBy=").append(top(firstRef)).append(" returns=").append(rt.objidReturns.get())
                        .append(" fallbacks=").append(rt.objidFallbacks.get()).append(" params=").append(rt.objidParams.get()).append(" paramFallbacks=").append(rt.objidParamFallbacks.get()).append(
                                        " fellOn=")
                        .append(top(rt.objidFellBy)).append(" deliveries=").append(rt.objidDeliveries.get())
                        .append(" contra=").append(rt.objidContra.get()).append(" contraUnchecked=").append(rt.objidContraUnchecked.get())
                        .append(" classEscapes=").append(rt.objidClassEscapes.get());
        if (x != null) {
            sb.append(" index{framed=").append(x.framed).append(" unframed=").append(x.unframed).append(" opaque=").append(x.opaque).append(" births=").append(x.sites)
                            .append(" indyHosts=").append(x.unframedIndyHosts.size()).append(" unframedTypes=").append(x.unframedBirths.size())
                            .append(" failed=").append(x.failReason).append(" ms=").append(x.ms).append('}');
        }
        sb.append(" pendingUnknownType=").append(rt.pendingUnknownType).append(" drops=").append(rt.objidDrops.get());
        // the allow-list's premise test (print-only): pending kinds that may hold a Class / a lambda instance, not listed
        List<String> na = rt.idQueries.isEmpty() ? List.of() : pendingNotAllowed(); // (a query built the holder index)
        sb.append(" pendingKinds=").append(rt.pendingSlots.size()).append(" pendingNotAllowed=").append(na.size()).append(na.isEmpty() ? "" : na.toString());
        System.out.println(idPremise().line()); // the per-image conditional premise census line
        System.out.println(idPremise().g1AllLine()); // every G1 event (print-only)
        System.out.println(idPremise().g1FwdLine()); // the derived-factory rule census
        for (String l : idPremise().g1fwdLines) {
            System.out.println(l);
        }
        return sb.append('}').toString();
    }

    /** Print-only: every caller site of {@code frame} kept by the caller-index filter whose label the precise set lacks. */
    private void dropLines(LocalFlowGraph frame, Set<String> delivered, List<String> out) {
        List<ForwardFixpoint.CallerSite> kept = rt.worldTop.fanCallersOf(frame);
        if (kept == null) {
            return;
        }
        for (ForwardFixpoint.CallerSite s : kept) {
            LocalFlowGraph.LocalVertex rc = s.call();
            String label = rc == null ? "?" : rt.frameName(rc.owner) + "@" + rc.bci;
            if (!delivered.contains(label)) {
                rt.objidDrops.incrementAndGet();
                out.add("[sug-fwd-rtrack-b] OBJID-DROP frame=" + rt.frameName(frame) + " site=" + label);
            }
        }
    }
}
