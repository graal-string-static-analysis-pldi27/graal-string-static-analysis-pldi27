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

import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.DUMP;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.PENDING_ALLOWLIST;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.READ_ERROR;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.focused;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.ResolvedJavaField;

import com.oracle.graal.pointsto.heap.ImageHeapConstant;
import com.oracle.graal.pointsto.heap.ImageHeapInstance;
import com.oracle.graal.pointsto.heap.ImageHeapObjectArray;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.svm.hosted.phases.StringAnalysisChildInlining;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.Bridge;

/**
 * World-top and caller-less frames of {@link RecursiveTracking}.
 */
final class WorldTopRule {
    private final RecursiveTracking rt;

    WorldTopRule(RecursiveTracking rt) {
        this.rt = rt;
    }

    /** The allowlist's membership test (pure; pinned): exact class, then an exact field name or the class wildcard. */
    static boolean pendingAllowlisted(String declaringClass, String fieldName) {
        List<String> l = PENDING_ALLOWLIST.get(declaringClass);
        return l != null && (l.contains(fieldName) || l.contains("*"));
    }

    /** The allowlist's existence check: the number of listed classes / named fields that do not exist (each printed loudly). */
    static int pendingAllowlistMissing() {
        int missing = 0;
        for (Map.Entry<String, List<String>> e : new TreeMap<>(PENDING_ALLOWLIST).entrySet()) {
            Class<?> k;
            try {
                k = Class.forName(e.getKey(), false, RecursiveTracking.class.getClassLoader());
            } catch (Throwable t) {
                System.err.println("[rtrack-e2] ADDRESS-ALLOWLIST-MISSING class " + e.getKey() + " (every frame is outside)");
                missing++;
                continue;
            }
            for (String fn : e.getValue()) {
                if (fn.equals("*")) {
                    continue;
                }
                try {
                    k.getDeclaredField(fn);
                } catch (Throwable t) {
                    System.err.println("[rtrack-e2] ADDRESS-ALLOWLIST-MISSING field " + e.getKey() + "." + fn + " (every frame is outside)");
                    missing++;
                }
            }
        }
        return missing;
    }

    void e2Note(String rule, LocalFlowGraph frame) {
        rt.e2Frames.computeIfAbsent(rule, k -> ConcurrentHashMap.newKeySet()).add(rt.frameName(frame));
    }

    /**
     * The world-top predicate ("outside caller unmodelled"): the frame may be invoked by a caller that is in no caller
     * index. Pure function of fixed post-analysis metadata ({@link #outsideCallerPredicate}). A metadata read failure
     * answers true (the refusal direction).
     *
     * <p>The world-top rule: a frame whose outside caller is unmodelled refuses it in both directions, whatever its
     * direct callers: backward {@link RTrackRefusal#WORLD_TOP_ENTRY} at the parameter case, forward
     * {@link RTrackRefusal#WORLD_TOP_EXIT} at a return with an empty path; world-top frames read the IR caller index
     * too. The direct callers are still fanned over.
     *
     * <p>The predicate's indirect-call part: virtual roots and every implementation the points-to analysis linked through a
     * virtual root's dispatch.
     *
     * <p>The address-taken disjunct: the target of a {@code MethodPointer} (an image-heap word slot or a constant in an
     * analysed graph) can be called through that pointer by an indirect call no caller index lists.
     *
     * <p>A pending value (an {@code AnalysisFuture} never computed during analysis) in a read word slot is skipped only when
     * its declaring field is on {@link RecursiveTracking#PENDING_ALLOWLIST}: fields SVM fills after analysis, whose targets are (by SVM's
     * construction of the JNI and C-entry stub registries) registered roots or native entries, already outside under the
     * other disjuncts (an instance JNI target is a virtual root: its {@code nonvirtualTarget} slot relies on the
     * predicate's indirect-call part). Every other pending read slot is a scan failure (every frame outside). A real read
     * error always fails.
     */
    boolean outsideCaller(LocalFlowGraph frame) {
        Boolean b = rt.narrowMemo.get(frame);
        if (b != null) {
            return b;
        }
        boolean v;
        ReflectionBridge rb = rt.reflBridge();
        AnalysisMethod m = rt.bridge.methodOf(frame);
        if (m == null || !rb.complete()) {
            v = outsideCallerString(frame); // the coverage proof failed / unreadable metadata: the plain predicate
        } else {
            try {
                Set<AnalysisMethod> reachedNonRefl = virtualRootReachedNonReflective();
                Set<AnalysisMethod> unmodelled = addressTakenUnmodelled();
                if (rt.virtualReadFailures > 0 || rt.addressScanFailures > 0) {
                    v = outsideCallerString(frame); // the plain predicate's failure rules (every instance / every frame outside)
                } else {
                    boolean jni = rb.registeredOutside(m); // the JNI / C-entry registries + the foreign-call belt
                    boolean nat = m.isNativeEntryPoint();
                    boolean dScan = ReflectionBridge.reflectiveFirstReason(m.getDirectRootReason()); // + the child's reflection extra root
                    boolean vScan = ReflectionBridge.reflectiveFirstReason(m.getVirtualRootReason());
                    boolean dOnly = ReflectionBridge.reflectiveOnly(rb.reflDirect.contains(m), dScan, jni, nat);
                    boolean vOnly = ReflectionBridge.reflectiveOnly(rb.reflVirtual.contains(m), vScan, jni, nat);
                    boolean address = unmodelled.contains(m);
                    v = ReflectionBridge.narrowedOutside(nat, jni, m.isDirectRootMethod(), dOnly, m.isVirtualRootMethod(), vOnly,
                                    reachedNonRefl.contains(m), address);
                    if (!v && outsideCallerString(frame) && !rt.narrowMemo.containsKey(frame)) {
                        e2Note("E3-NARROWED", frame); // a frame set (the counter below is its size)
                    }
                }
            } catch (Throwable t) {
                v = true;
            }
        }
        Boolean prev = rt.narrowMemo.putIfAbsent(frame, v);
        return prev != null ? prev : v;
    }

    /**
     * The plain world-top predicate (used when the bridge proof fails).
     */
    boolean outsideCallerString(LocalFlowGraph frame) {
        Boolean b = rt.outsideMemo.get(frame);
        if (b != null) {
            return b;
        }
        boolean v;
        AnalysisMethod m = rt.bridge.methodOf(frame);
        if (m == null) {
            v = true; // no method = unreadable metadata -> the refusal direction (the javadoc's rule)
        } else {
            try {
                // Any read failure of the virtual-root set makes every instance frame outside (the
                // refusal direction), never the name test; virtual dispatch never reaches a static method.
                boolean reached = virtualRootReached().contains(m) || (rt.virtualReadFailures > 0 && !m.isStatic());
                // The address-taken disjunct; a failed or incomplete scan makes every frame outside.
                boolean address = addressTaken().contains(m) || rt.addressScanFailures > 0;
                v = outsideCallerPredicate(m.isNativeEntryPoint(), m.isDirectRootMethod(), m.isVirtualRootMethod(), reached, address);
            } catch (Throwable t) {
                v = true;
            }
        }
        Boolean prev = rt.outsideMemo.putIfAbsent(frame, v);
        return prev != null ? prev : v;
    }

    /**
     * The world-top predicate as a pure function (pinned by WorldTopRuleTest): a native entry point, a direct root
     * (any registration reason: the conservative reading of the first-reason-only {@code isDirectRootMethod}), a virtual
     * root, an implementation reached through a virtual root's dispatch, or an address-taken method.
     */
    static boolean outsideCallerPredicate(boolean nativeEntry, boolean directRoot, boolean virtualRoot, boolean reachedThroughVirtualRoot,
                    boolean addressTaken) {
        return nativeEntry || directRoot || virtualRoot || reachedThroughVirtualRoot || addressTaken;
    }

    /**
     * The implementations reached through a virtual root's dispatch: for every virtual root R, the callees the points-to
     * analysis linked on the virtual invoke {@code PointsToAnalysis.addRootMethod} creates for R (its receiver flow is R's
     * declaring type, so it links every implementation of every instantiated subtype). These calls have no
     * {@code InvokeInfo}, so no caller index lists them. A read failure (an unreadable root invoke, or an empty universe)
     * is counted, and {@link #outsideCaller} then answers true for every instance frame (the refusal direction).
     */
    private Set<AnalysisMethod> virtualRootReached() {
        Set<AnalysisMethod> v = rt.virtualReached;
        return v != null ? v : virtualRootReachedBuild();
    }

    /** The implementations reached through a virtual root that is not reflective-only (built with {@link #virtualRootReached}). */
    private Set<AnalysisMethod> virtualRootReachedNonReflective() {
        virtualRootReached();
        return rt.virtualReachedNonRefl;
    }

    private Set<AnalysisMethod> virtualRootReachedBuild() {
        ContainerAtoms.enterMon(rt.e2BuildLock);
        try {
            synchronized (rt.e2BuildLock) {
                return virtualRootReachedBuildLocked();
            }
        } finally {
            ContainerAtoms.exitMon(rt.e2BuildLock);
        }
    }

    private Set<AnalysisMethod> virtualRootReachedBuildLocked() {
        if (rt.virtualReached != null) {
            return rt.virtualReached;
        }
        Set<AnalysisMethod> out = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        Set<AnalysisMethod> outNonRefl = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        ReflectionBridge rb = rt.reflBridge();
        int roots = 0;
        int failures = 0;
        int methods = 0;
        for (AnalysisMethod m : rt.bridge.universeMethods()) {
            methods++;
            boolean vr;
            try {
                vr = m.isVirtualRootMethod();
            } catch (Throwable t) {
                failures++;
                continue;
            }
            if (!vr) {
                continue;
            }
            roots++;
            rt.virtualRootNames.add(m.format("%H.%n(%P)"));
            try {
                com.oracle.graal.pointsto.flow.InvokeTypeFlow inv = ((com.oracle.graal.pointsto.meta.PointsToAnalysisMethod) m)
                                .getContextInsensitiveVirtualInvoke(com.oracle.svm.common.meta.MultiMethod.ORIGINAL_METHOD);
                java.util.Collection<AnalysisMethod> callees = inv.getAllCallees();
                out.addAll(callees);
                // A virtual root whose only source is a reflection accessor is dispatched by the bridge
                boolean reflOnly = rb != null && ReflectionBridge.reflectiveOnly(rb.reflVirtual.contains(m),
                                ReflectionBridge.reflectiveFirstReason(m.getVirtualRootReason()), rb.registeredOutside(m), m.isNativeEntryPoint());
                if (!reflOnly) {
                    outNonRefl.addAll(callees);
                }
            } catch (Throwable t) {
                failures++;
            }
        }
        if (methods == 0) {
            failures++; // an empty universe is a swallowed failure, never "no virtual root"
        }
        rt.virtualRootCount = roots;
        rt.virtualReadFailures = failures;
        rt.virtualReachedNonRefl = outNonRefl;
        rt.virtualReached = out;
        return out;
    }

    Set<AnalysisMethod> addressTaken() {
        Set<AnalysisMethod> v = rt.addressTakenSet;
        return v != null ? v : addressTakenBuild();
    }

    /** The address-taken methods without the pointers held only in the bridge table's accessor pointer fields. */
    private Set<AnalysisMethod> addressTakenUnmodelled() {
        addressTaken();
        return rt.addressTakenUnmodelledSet;
    }

    private Set<AnalysisMethod> addressTakenBuild() {
        ContainerAtoms.enterMon(rt.e2BuildLock);
        try {
            synchronized (rt.e2BuildLock) {
                return addressTakenBuildLocked();
            }
        } finally {
            ContainerAtoms.exitMon(rt.e2BuildLock);
        }
    }

    /**
     * The targets of every {@code MethodPointer} the image can hold: (a) the reachable image-heap objects' word-typed
     * instance fields and word-component array elements, and the build-time values of word-typed statics; (b) the
     * {@code SubstrateMethodPointerConstant}s of every analysed graph's encoding. A pending word slot, an unavailable heap,
     * an empty universe, or an unresolvable pointer target counts as a failure (then every frame is outside).
     */
    private Set<AnalysisMethod> addressTakenBuildLocked() {
        if (rt.addressTakenSet != null) {
            return rt.addressTakenSet;
        }
        Set<AnalysisMethod> out = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        Set<AnalysisMethod> outUnmodelled = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        ReflectionBridge rb = rt.reflBridge();
        int accessorSlots = 0;
        int unconfirmed = 0;
        // 0 failures, 1 heap word slots, 2 heap pointers, 3 graph pointers, 4 graphs, 5 other relocated words,
        // failure causes: 6 unresolved field, 7 pending read slot, 8 unresolved target, 9 read error; 10 pending unread slot (not a failure)
        // 11 pending read slots not allowlisted (failures under the allowlist rule), 12 pending read slots allowlisted (skipped), 13 allowlist entries missing
        int[] c = new int[14];
        c[13] = pendingAllowlistMissing();
        c[0] += c[13];
        Map<AnalysisType, Set<ImageHeapConstant>> objs = rt.bridge.heapObjects();
        if (objs == null) {
            c[0]++;
        } else {
            for (Map.Entry<AnalysisType, Set<ImageHeapConstant>> e : objs.entrySet()) {
                for (ImageHeapConstant h : e.getValue()) {
                    if (h instanceof ImageHeapInstance inst) {
                        boolean accessorHolder = rb != null && rb.accessorConstants.contains(h);
                        Object holderHosted = null;
                        for (ResolvedJavaField rf : h.getType().getInstanceFields(true)) {
                            AnalysisField f = rt.bridge.resolveField(rf);
                            if (f == null) {
                                c[0]++;
                                c[6]++;
                                continue;
                            }
                            if (!f.getType().isWordType()) {
                                continue;
                            }
                            c[1]++;
                            Object v;
                            try {
                                v = inst.getFieldValue(f);
                            } catch (Throwable t) {
                                v = READ_ERROR;
                            }
                            // An accessor pointer slot of the bridge table is called only through the bridged edges
                            boolean bridged = accessorHolder && ReflectionBridge.isAccessorPointerField(f.getDeclaringClass().toJavaName(true), f.getName());
                            if (bridged) {
                                accessorSlots++;
                            }
                            // An allowlisted pending slot is confirmed by the registries' holder objects
                            if (rb != null && v != null && v != READ_ERROR &&
                                            !(v instanceof JavaConstant || v instanceof com.oracle.svm.core.meta.MethodPointer) && f.isRead() &&
                                            pendingAllowlisted(f.getDeclaringClass().toJavaName(true), f.getName())) {
                                if (holderHosted == null) {
                                    JavaConstant hc = h.getHostedObject();
                                    holderHosted = hc != null ? com.oracle.graal.pointsto.util.GraalAccess.getOriginalSnippetReflection().asObject(Object.class, hc) : READ_ERROR;
                                }
                                if (rb.registryFailure != null || !rb.pendingHolderConfirmed(f.getDeclaringClass().toJavaName(true), holderHosted)) {
                                    unconfirmed++;
                                    c[0]++; // the registries do not list the holder: its future pointer is unknown
                                    rt.addressPendingClasses.merge("unconfirmed:" + f.getDeclaringClass().toJavaName(true) + "." + f.getName(), 1, Integer::sum);
                                }
                            }
                            notePointer(out, bridged ? null : outUnmodelled, v, c, 2, f.isRead(), f);
                        }
                    } else if (h instanceof ImageHeapObjectArray oa && h.getType() instanceof AnalysisType at && at.getComponentType() != null &&
                                    at.getComponentType().isWordType()) {
                        for (int i = 0; i < oa.getLength(); i++) {
                            c[1]++;
                            Object v;
                            try {
                                v = oa.getElement(i);
                            } catch (Throwable t) {
                                v = READ_ERROR;
                            }
                            notePointer(out, outUnmodelled, v, c, 2, true, null);
                        }
                    }
                }
            }
        }
        try {
            for (AnalysisField f : rt.bridge.universeFields()) {
                if (f.isStatic() && f.getType().isWordType() && (f.getDeclaringClass().isInitialized() || rt.bridge.classInitSimulated(f.getDeclaringClass()))) {
                    c[1]++;
                    notePointer(out, outUnmodelled, rt.buildTimeStaticValue(f), c, 2, f.isRead(), f);
                }
            }
        } catch (Throwable t) {
            c[0]++;
            c[9]++;
        }
        int methods = 0;
        for (AnalysisMethod m : rt.bridge.universeMethods()) {
            methods++;
            jdk.graal.compiler.nodes.EncodedGraph g;
            try {
                g = m.getAnalyzedGraph();
            } catch (Throwable t) {
                c[0]++;
                c[9]++;
                continue;
            }
            if (g == null) {
                continue; // not analysed code: never compiled, so no pointer constant of it runs
            }
            c[4]++;
            Object[] os = g.getObjects();
            if (os == null) {
                continue;
            }
            for (Object o : os) {
                if (o instanceof com.oracle.svm.core.meta.SubstrateMethodPointerConstant || o instanceof com.oracle.svm.hosted.meta.PatchedWordConstant ||
                                o instanceof com.oracle.svm.core.meta.MethodPointer) {
                    notePointer(out, outUnmodelled, o, c, 3, true, null);
                }
            }
        }
        if (methods == 0) {
            c[0]++;
        }
        rt.addressScanFailures = c[0];
        rt.addressAccessorSlotsSkipped = accessorSlots;
        rt.pendingUnconfirmed = unconfirmed;
        rt.addressTakenUnmodelledSet = outUnmodelled;
        rt.addressCensus = " addressTaken=" + out.size() + " addressScanFailures=" + c[0] + " addressWordSlots=" + c[1] + " addressHeapPointers=" + c[2] +
                        " addressGraphPointers=" + c[3] + " addressGraphs=" + c[4] + " addressOtherRelocated=" + c[5] + " addressFail{unresolvedField=" + c[6] +
                        " pendingRead=" + c[7] + " pendingNotAllowlisted=" + c[11] + " pendingAllowlisted=" + c[12] +
                        " allowlistMissing=" + c[13] + " unresolvedTarget=" + c[8] + " readError=" + c[9] + "} addressPendingUnread=" + c[10] +
                        " addressPendingUnexpected=" + new TreeMap<>(rt.addressPendingClasses) + " addressUnmodelled=" + outUnmodelled.size() +
                        " accessorSlotsBridged=" + accessorSlots + " pendingUnconfirmed=" + unconfirmed;
        rt.addressTakenSet = out;
        return out;
    }

    /**
     * One scanned value: a MethodPointer target joins {@code out}; a pending READ slot or an unresolvable target fails.
     * A pending slot of a field no code reads is not a failure: no code can load (and so call) its pointer.
     */
    private void notePointer(Set<AnalysisMethod> out, Set<AnalysisMethod> outUnmodelled, Object v, int[] c, int counterIdx, boolean read, AnalysisField field) {
        if (v == null) {
            return;
        }
        if (v == READ_ERROR) {
            c[0]++; // a real read error: always the refusal direction
            c[9]++;
            return;
        }
        if (!(v instanceof JavaConstant || v instanceof com.oracle.svm.core.meta.MethodPointer)) {
            if (read) {
                c[7]++;
                String dc = field != null ? field.getDeclaringClass().toJavaName(true) : null;
                boolean allowed = dc != null && pendingAllowlisted(dc, field.getName());
                if (allowed) {
                    c[12]++;
                } else {
                    c[11]++;
                    // the unexpected pending slots, by declaring field (array elements: by holder kind)
                    rt.addressPendingClasses.merge(field != null ? dc + "." + field.getName() : "array-element", 1, Integer::sum);
                }
                if (!allowed) {
                    c[0]++; // a pending future in a read slot outside the allowlist: the slot's pointer is unknown
                }
            } else {
                c[10]++;
            }
            return;
        }
        Object w = v;
        if (v instanceof com.oracle.svm.hosted.meta.PatchedWordConstant pwc) {
            w = pwc.getWord();
        } else if (v instanceof com.oracle.svm.core.meta.SubstrateMethodPointerConstant mpc) {
            w = mpc.pointer();
        }
        if (w instanceof com.oracle.svm.core.meta.MethodPointer mp) {
            AnalysisMethod am = mp.getMethod() != null ? rt.bridge.resolveMethod(mp.getMethod()) : null;
            if (am == null) {
                if (mp.getMethod() != null) {
                    c[0]++; // a target the universe cannot name: unmatched = unknown
                    c[8]++;
                }
                return;
            }
            out.add(am);
            if (outUnmodelled != null) {
                outUnmodelled.add(am);
            }
            c[counterIdx]++;
        } else if (v instanceof com.oracle.svm.hosted.meta.PatchedWordConstant) {
            c[5]++; // another relocated word (e.g. a CEntryPointLiteral code pointer: its target is a native entry)
        }
    }

    /**
     * The world-top and no-caller rules at a container RETURN with no usable path (pure; pinned): the refusal to add,
     * or null. A non-empty caller list is still fanned over after a refusal.
     *
     * <p>A return with an empty path out of a frame that is not world-top and has no caller in the complete IR caller index
     * refuses {@link RTrackRefusal#NO_CALLER_EXIT}, for both atom kinds, so such a walk never ends silently.
     */
    static RTrackRefusal returnExitRefusal(boolean outside, int nCallers) {
        if (outside) {
            return RTrackRefusal.WORLD_TOP_EXIT; // the world-top rule
        }
        if (nCallers == 0) {
            return RTrackRefusal.NO_CALLER_EXIT;
        }
        return null;
    }

    /**
     * The world-top rule at a backward PARAMETER case with no path (pure; pinned): the refusal of the sink, if any. An
     * outside-caller frame refuses WORLD_TOP_ENTRY whatever its direct callers (which are still fanned over); otherwise
     * an empty list refuses DARK_ENTRY.
     */
    static RTrackRefusal parameterEntryRefusal(boolean outside, int nCallers) {
        if (outside) {
            return RTrackRefusal.WORLD_TOP_ENTRY;
        }
        if (nCallers == 0) {
            return RTrackRefusal.DARK_ENTRY;
        }
        return null;
    }

    /** World-top census fields, printed in the {@code [sug-fwd-rtrack]} line. */
    String e2Census() {
        StringBuilder sb = new StringBuilder(" e2{");
        Set<AnalysisMethod> vr = rt.virtualReached;
        sb.append("virtualRoots=").append(rt.virtualRootCount).append(" virtualReached=").append(vr != null ? vr.size() : -1)
                        .append(" virtualReadFailures=").append(rt.virtualReadFailures).append(rt.addressCensus)
                        .append(" worldTopExit=").append(rt.e2WorldTopExit.get()).append(" ownerRetWorldTop=").append(rt.e2OwnerRetWorldTop.get())
                        .append(" worldTopEntryWithCallers=").append(rt.e2WorldTopEntryWithCallers.get())
                        .append(" noCallerExit=").append(rt.e2NoCallerExit.get()).append(" staticOutsideMint=").append(rt.e2StaticOutsideMint.get())
                        .append(" stringWorldTopExit=").append(rt.e2StringWorldTopExit.get()).append(" stringNoCallerExit=").append(rt.e2StringNoCallerExit.get());
        for (Map.Entry<String, Set<String>> e : new TreeMap<>(rt.e2Frames).entrySet()) {
            sb.append(' ').append(e.getKey()).append("Frames=").append(e.getValue().size());
        }
        return sb.append('}').toString();
    }

    /**
     * The caller-index site filter (the mirror of {@link RecursiveTracking#pointsToReceiverNarrow}): the callers of {@code frame} for a
     * path-less fan. A site of {@link RecursiveTracking#callersOf} is dropped only when its call's child-final points-to receiver state
     * proves that no receiver dispatches to the frame's method ({@code DispatchResolution.callerSiteDecision}). Kept on
     * every doubt: a static frame or a direct callee, a site that is not one of the LFG's CHA sites (IR-index sites come
     * from the points-to call graph itself, bridge sites are VM calls), a call left by a parse-time-inlined scope,
     * no/several invoke flows, a saturated invoke or receiver, an all-instantiated or empty state, a type that resolves to
     * nothing or outside the call's CHA fan, an exception. Never empties the list. The belt ({@link RecursiveTracking#beltOk}), the static
     * fan and the diagnostics keep reading {@link RecursiveTracking#callersOf}. Premise: the child's final, unsaturated points-to receiver
     * state at an invoke contains the exact class of every run-time receiver there (the points-to soundness contract).
     * Deterministic: a pure function of the final state, memoised per frame.
     *
     * <p>The caller filter: the two path-less caller fans ({@link RecursiveTracking#returnAllCallers}, {@link RecursiveTracking#parameterIndexCase}) are
     * filtered by the call's final points-to receiver state (this method).
     */
    List<ForwardFixpoint.CallerSite> fanCallersOf(LocalFlowGraph frame) {
        return fanOrAll(rt.callersOf(frame), all -> memoFanCallers(frame, all));
    }

    /** The filter's gate (pinned by {@code CallerReceiverFilterTest}): a null or empty list is returned unfiltered. */
    static <S> List<S> fanOrAll(List<S> all, java.util.function.UnaryOperator<List<S>> filter) {
        if (all == null || all.isEmpty()) {
            return all;
        }
        return filter.apply(all);
    }

    /** One frame's filtered fan: the decisions per site and the filtered list (a pure function of the final state). */
    private record FanDecision(List<ForwardFixpoint.CallerSite> out, Map<ForwardFixpoint.CallerSite, String> decision) {
    }

    private List<ForwardFixpoint.CallerSite> memoFanCallers(LocalFlowGraph frame, List<ForwardFixpoint.CallerSite> all) {
        List<ForwardFixpoint.CallerSite> cached = rt.fanCallersMemo.get(frame);
        if (cached != null) {
            return cached;
        }
        FanDecision d = computeFanCallers(frame, all);
        List<ForwardFixpoint.CallerSite> prev = rt.fanCallersMemo.putIfAbsent(frame, d.out());
        if (prev != null) {
            return prev; // a racing thread won: it alone counts and dumps this frame
        }
        fanCensus(frame, all, d);
        return d.out();
    }

    private FanDecision computeFanCallers(LocalFlowGraph frame, List<ForwardFixpoint.CallerSite> all) {
        AnalysisMethod fm = rt.bridge.methodOf(frame);
        List<ForwardFixpoint.CallerSite> lfg = rt.bridge.callersOf(frame);
        Set<ForwardFixpoint.CallerSite> lfgSites = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        if (lfg != null) {
            lfgSites.addAll(lfg);
        }
        Map<ForwardFixpoint.CallerSite, String> decision = new IdentityHashMap<>();
        for (ForwardFixpoint.CallerSite c : all) {
            decision.put(c, callerSiteReason(rt.bridge, fm, c, lfgSites));
        }
        List<ForwardFixpoint.CallerSite> out = DispatchResolution.keepNeverEmpty(all, c -> !DispatchResolution.CALLER_DROP.equals(decision.get(c)));
        return new FanDecision(out, decision);
    }

    /**
     * The census of one frame, run once per frame by the memo's winner. Self-check (print-only): every dropped site's
     * own points-to callees must not contain the frame's method ({@code contra}, expected 0).
     */
    private void fanCensus(LocalFlowGraph frame, List<ForwardFixpoint.CallerSite> all, FanDecision d) {
        List<ForwardFixpoint.CallerSite> out = d.out();
        rt.cptFrames.incrementAndGet();
        rt.cptSites.addAndGet(all.size());
        AnalysisMethod fm = rt.bridge.methodOf(frame);
        int drops = 0;
        List<String> contra = new ArrayList<>();
        for (ForwardFixpoint.CallerSite c : all) {
            String r = d.decision().get(c);
            if (DispatchResolution.CALLER_DROP.equals(r)) {
                drops++;
                try {
                    LocalFlowGraph.LocalVertex v = c.call();
                    AnalysisMethod mc = c.caller() != null ? c.caller() : rt.bridge.methodOf(v.owner);
                    java.util.Collection<AnalysisMethod> callees = rt.bridge.pointsToCallees(mc, v);
                    if (callees == null) {
                        rt.cptContraUnchecked.incrementAndGet();
                    } else if (fm != null && callees.contains(fm)) {
                        rt.cptContra.incrementAndGet();
                        contra.add(rt.frameName(v.owner) + "@" + v.bci);
                    }
                } catch (Throwable ex) {
                    rt.cptContraUnchecked.incrementAndGet();
                }
            } else {
                rt.cptKeep.computeIfAbsent(r, k -> new AtomicLong()).incrementAndGet();
            }
        }
        if (!contra.isEmpty()) {
            System.out.println("[sug-fwd-rtrack-b] CALLERPT-CONTRA frame=" + rt.frameName(frame) + " droppedButLinked=" + contra);
        }
        if (out == all && drops > 0) {
            rt.cptUnemptied.incrementAndGet();
        } else if (out != all) {
            rt.cptFramesNarrowed.incrementAndGet();
            rt.cptDropped.addAndGet(all.size() - out.size());
        }
        if (DUMP && focused(rt.frameName(frame))) {
            StringBuilder kept = new StringBuilder();
            StringBuilder dropped = new StringBuilder();
            Map<String, Integer> why = new TreeMap<>();
            for (ForwardFixpoint.CallerSite c : all) {
                String r = d.decision().get(c);
                String name = c.call() != null ? rt.frameName(c.call().owner) + "@" + c.call().bci : "null";
                if (DispatchResolution.CALLER_DROP.equals(r)) {
                    dropped.append(dropped.length() == 0 ? "" : ", ").append(name);
                } else {
                    kept.append(kept.length() == 0 ? "" : ", ").append(name).append('(').append(r).append(')');
                    why.merge(r, 1, Integer::sum);
                }
            }
            System.out.println("[rtrack-dump] CALLERPT frame=" + rt.frameName(frame) + " all=" + all.size() + " out=" + out.size() + (out == all && drops > 0 ? " UNEMPTIED" : "") +
                            " kept=[" + kept + "] dropped=[" + dropped + "] keepReasons=" + why);
        }
    }

    /**
     * One site's decision ({@code DispatchResolution.CALLER_DROP} or a keep reason); static over the bridge for the
     * premise JUnit ({@code CallerReceiverFilterTest}).
     */
    static String callerSiteReason(Bridge bridge, AnalysisMethod fm, ForwardFixpoint.CallerSite c, Set<ForwardFixpoint.CallerSite> lfgSites) {
        LocalFlowGraph.LocalVertex v = c.call();
        if (v == null) {
            return "noCall";
        }
        if (!lfgSites.contains(c)) {
            return "notLfg"; // an IR-index site (already points-to typed) or a reflection-bridge site
        }
        if (v.irNode instanceof Invoke inv) {
            String k = irKeepReason(StringAnalysisChildInlining.isFromInlinedScope(inv),
                            inv.callTarget() instanceof MethodCallTargetNode ct ? ct.invokeKind() : null);
            if (k != null) {
                return k;
            }
        }
        try {
            AnalysisMethod mc = c.caller() != null ? c.caller() : bridge.methodOf(v.owner);
            if (mc == null) {
                return "noCaller";
            }
            String[] why = {"noTypes"};
            if (fm == null || fm.isStatic() || v.calleeMethod == null || v.calleeMethod.isStatic() || v.calleeMethod.canBeStaticallyBound()) {
                return "direct";
            }
            List<AnalysisType> types = bridge.pointsToReceiverTypes(mc, v, r -> why[0] = r);
            if (types == null) {
                return "pt:" + why[0];
            }
            List<DispatchResolution.ResolvedTarget> fan = bridge.committedFan(mc, v);
            return DispatchResolution.callerSiteDecision(types, v.calleeMethod, fm, fan);
        } catch (Throwable ex) {
            return "exception";
        }
    }

    /**
     * The IR-level keep of one LFG site (pure; pinned by {@code CallerReceiverFilterTest}): {@code inlined} for a call left
     * by a parse-time-inlined scope (checked first), {@code direct} for a direct invoke kind (invokespecial, invokestatic:
     * no receiver dispatch, e.g. a {@code super.} call), null = no IR-level keep (the points-to state decides).
     */
    static String irKeepReason(boolean fromInlinedScope, jdk.graal.compiler.nodes.CallTargetNode.InvokeKind kind) {
        if (fromInlinedScope) {
            return "inlined";
        }
        if (kind != null && kind.isDirect()) {
            return "direct";
        }
        return null;
    }

    String callerPtCensus() {
        StringBuilder sb = new StringBuilder(" callerPt{frames=").append(rt.cptFrames.get()).append(" narrowed=").append(rt.cptFramesNarrowed.get())
                        .append(" sites=").append(rt.cptSites.get()).append(" dropped=").append(rt.cptDropped.get()).append(" unemptied=").append(rt.cptUnemptied.get())
                        .append(" contra=").append(rt.cptContra.get()).append(" contraUnchecked=").append(rt.cptContraUnchecked.get()).append(" keep=[");
        List<String> keys = new ArrayList<>(rt.cptKeep.keySet());
        java.util.Collections.sort(keys);
        for (int i = 0; i < keys.size(); i++) {
            sb.append(i == 0 ? "" : ",").append(keys.get(i)).append('=').append(rt.cptKeep.get(keys.get(i)).get());
        }
        return sb.append("]}").toString();
    }
}
