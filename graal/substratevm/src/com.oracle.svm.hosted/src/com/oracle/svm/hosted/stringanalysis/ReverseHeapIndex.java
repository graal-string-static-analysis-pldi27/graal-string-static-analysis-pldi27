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

import static com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.constantSiteOf;
import static com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.isNamedQuery;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.HOLDER_FAN_CAP;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.bump;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import jdk.graal.compiler.nodes.ConstantNode;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaField;

import com.oracle.graal.pointsto.heap.ImageHeapConstant;
import com.oracle.graal.pointsto.heap.ImageHeapInstance;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtom;

/**
 * The reverse heap index of {@link RecursiveTracking}: every heap holder of a constant K (a build-time object H with
 * H.f == K or H[i] == K, or a static field), built once over the image heap.
 */
final class ReverseHeapIndex {
    private final RecursiveTracking rt;

    ReverseHeapIndex(RecursiveTracking rt) {
        this.rt = rt;
    }

    private boolean pendingSlotAdmits(RAtom k) {
        if (rt.pendingUnknownType) {
            return true;
        }
        AnalysisType tk = k.constant != null && k.constant.getType() instanceof AnalysisType at ? at : null;
        if (tk == null) {
            return !rt.pendingSlotTypes.isEmpty();
        }
        for (AnalysisType p : rt.pendingSlotTypes) {
            if (p.isAssignableFrom(tk)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The refinement of the pending-snapshot rule: a heap instance (never an array) whose exact class declares no
     * reference-typed instance field (superclasses and injected fields included: e.g. the JDK's non-capturing lambdas).
     * No member of its table can hold a reference, so its contents are complete whatever its holders. Its identity flows
     * are kept: the walk is not skipped (never {@code completeByProof}: an empty {@code entryPaths} would make every
     * {@code OWNER(K)} atom return nowhere). Why a missed holder route X is still sound: an object allocated in K's method
     * on a path K's walk does not know receives a tracked value only through a store whose owner resolution walks back
     * through X's receiver, which crosses the unindexed route and refuses there (the build-time holder rule, the static
     * rule, an Unsafe / method-handle refusal); the owner then merges and the merged atom returns to every caller, X
     * included. So the forward-only gap concerns only objects that hold nothing tracked.
     */
    private static boolean referenceFreeInstance(RAtom k) {
        if (!(k.constant instanceof ImageHeapInstance) || !(k.constant.getType() instanceof AnalysisType t)) {
            return false;
        }
        for (ResolvedJavaField f : t.getInstanceFields(true)) {
            if (f.getJavaKind() == JavaKind.Object) {
                return false;
            }
        }
        return true;
    }

    void scheduleHeapHolders(RAtom k) {
        rt.constantsNeedingHolders.incrementAndGet();
        Map<Object, List<Object[]>> idx = rt.holderIndex();
        if (idx == null || rt.holderIndexProblem != null) {
            rt.refuse(k.table, RTrackRefusal.CONSTANT_HOLDERS_UNINDEXED);
            return;
        }
        if (pendingSlotAdmits(k)) {
            if (referenceFreeInstance(k) && !isNamedQuery(k)) { // a heap-birth query takes the strict pending-snapshot rule
                // K holds no reference, so its table's contents are
                // complete whatever its holders; its identity flows (T(K).entryPaths, the OWNER(K) returns) stay walked:
                // the known holders are scheduled below and K's ConstantNode walk runs as for any constant
                rt.pendingReferenceFree.incrementAndGet();
            } else {
                // A read heap slot whose declared type admits K is
                // still a pending future: K may be in it, so K's holder set is not
                // provably complete (never executed: the no-future rule).
                rt.heapSnapshotPending.incrementAndGet();
                rt.refuse(k.table, RTrackRefusal.HEAP_SNAPSHOT_PENDING);
                return;
            }
        }
        List<Object[]> hs = idx.getOrDefault(constantSiteOf(k), List.of());
        int n = hs.size();
        synchronized (rt.holderFanHist) {
            rt.holderFanHist[n == 0 ? 0 : n == 1 ? 1 : n <= 4 ? 2 : n <= 16 ? 3 : n <= 64 ? 4 : n <= 256 ? 5 : n <= 1024 ? 6 : 7]++;
        }
        if (HOLDER_FAN_CAP > 0 && n > HOLDER_FAN_CAP) {
            rt.refuse(k.table, RTrackRefusal.CONSTANT_HOLDERS_UNINDEXED); // whole-table, a set size of the static index
            return;
        }
        for (Object[] rec : hs) {
            rt.heapHoldersScheduled.incrementAndGet();
            if (rec[0] instanceof ImageHeapConstant h) {
                rt.constantAtom(h); // schedules H: its build-time store of K registers K's escape
            } else if (rec[0] instanceof AnalysisField sf) {
                rt.staticTable(sf); // the static's build-time value K: K's escape at the static's loads
            }
        }
    }

    /**
     * A read slot whose value is a pending future: the value is
     * not scanned, so nothing reachable only through it is indexed either. The declared-type test is therefore complete
     * only for a type whose values hold no reference (a primitive array); any other declared type (and an unknown one)
     * admits every constant.
     */
    void notePending(AnalysisType declared, String where) {
        if (declared == null || !(declared.isArray() && declared.getComponentType().getJavaKind().isPrimitive())) {
            rt.pendingUnknownType = true; // an unknown or reference-holding declared type admits every constant
        } else {
            rt.pendingSlotTypes.add(declared);
        }
        bump(rt.pendingSlotsBy, where);
    }

    /** One snapshot slot: records holder → value; returns true for a pending future in a READ slot (index incomplete). */
    boolean indexSlot(Map<Object, List<Object[]>> idx, Object v, Object holder, Object member, boolean read) {
        if (v == null) {
            return false;
        }
        if (!(v instanceof JavaConstant jc)) {
            if (read) {
                rt.heapIndexPendingRead.incrementAndGet();
                return true;
            }
            rt.heapIndexPendingUnread.incrementAndGet();
            return false;
        }
        if (jc instanceof ImageHeapConstant k) {
            rt.heapIndexEdges.incrementAndGet();
            idx.computeIfAbsent(k.getConstantData(), x -> new ArrayList<>(1)).add(new Object[]{holder, member});
        }
        return false;
    }

    String holderFanHistogram() {
        String[] lab = {"0", "1", "2-4", "5-16", "17-64", "65-256", "257-1024", "1025+"};
        StringBuilder sb = new StringBuilder("holderFan{");
        synchronized (rt.holderFanHist) {
            for (int i = 0; i < lab.length; i++) {
                sb.append(i > 0 ? " " : "").append(lab[i]).append(':').append(rt.holderFanHist[i]);
            }
        }
        return sb.append('}').toString();
    }
}
