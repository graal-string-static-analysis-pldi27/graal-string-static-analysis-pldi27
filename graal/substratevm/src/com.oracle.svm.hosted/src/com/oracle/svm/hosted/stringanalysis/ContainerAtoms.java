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

import java.util.Comparator;
import java.util.List;

import com.oracle.graal.pointsto.meta.AnalysisMethod;

/**
 * The heap-context vocabulary of the recursive container tracking: an atom key is {@code (birthplace, HeapContext)},
 * and the context is decided only by {@link ContextPolicy}.
 *
 * <p>Also the home of the one-monitor tripwire: a thread never holds one Table/Sink monitor while acquiring another's;
 * {@link ContainerTables} brackets every such acquisition with {@link #enterMon}/{@link #exitMon} and the solve prints
 * {@link #lockOrderSummary()} ({@code atomMonNestViolations} must be 0).
 */
final class ContainerAtoms {

    private ContainerAtoms() {
    }

    /**
     * One invoke hop of the allocation call-string, keyed on the call site: the caller frame and bci (notation
     * {@code X@bci→Y}). Not {@code (callee, bci)}: that pair can alias the invokes of two distinct caller frames at one
     * bci and merge chains with no runtime counterpart (precision-only).
     *
     * <p>Canonical order: {@link TransferFacts#methodFlowKey}, then {@link TransferFacts#methodDescriptorKey}, then bci.
     */
    static final class ContextElement {
        final AnalysisMethod method;
        final int bci;
        /**
         * Owner-site element: identity is the owner atom's allocation site, printed {@code obj@<site>}. Null for
         * call-site elements; the two kinds never compare equal.
         */
        final Object ownerSite;
        private final String canonicalKey;

        ContextElement(AnalysisMethod method, int bci) {
            this(method, bci, null, null);
        }

        private ContextElement(AnalysisMethod method, int bci, Object ownerSite, String siteKey) {
            this.method = method;
            this.bci = bci;
            this.ownerSite = ownerSite;
            this.canonicalKey = ownerSite != null
                            ? "obj@" + siteKey
                            : TransferFacts.methodFlowKey(method) + "@b" + bci;
        }

        /** The owner-site element (identity = the site object). */
        static ContextElement ofOwner(Object ownerSite, String siteKey) {
            return new ContextElement(null, -1, java.util.Objects.requireNonNull(ownerSite), siteKey);
        }

        boolean isOwnerElement() {
            return ownerSite != null;
        }

        /** The canonical comparison key (deterministic total order input). */
        String canonicalKey() {
            return canonicalKey;
        }

        /** The canonical element order (kinds first). */
        static final Comparator<ContextElement> CANONICAL_ORDER = Comparator.comparing((ContextElement e) -> e.ownerSite != null ? "obj" : "call")
                        .thenComparing(e -> e.method != null ? TransferFacts.methodFlowKey(e.method) : "")
                        .thenComparing(e -> e.method != null ? TransferFacts.methodDescriptorKey(e.method) : "")
                        .thenComparing(e -> e.ownerSite != null ? e.canonicalKey : "")
                        .thenComparingInt(e -> e.bci);

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!(obj instanceof ContextElement other)) {
                return false;
            }
            return bci == other.bci && method == other.method && ownerSite == other.ownerSite;
        }

        @Override
        public int hashCode() {
            return 31 * System.identityHashCode(method) + bci * (ownerSite != null ? 7 : 1) +
                            (ownerSite != null ? System.identityHashCode(ownerSite) : 0);
        }

        @Override
        public String toString() {
            return canonicalKey;
        }
    }

    /**
     * The canonical heap call-string: an interned, immutable element tuple in walk order (demand seed → allocation),
     * ordered lexicographically by {@link ContextElement#CANONICAL_ORDER}. Atom keys carry the k-truncated suffix: two
     * demand chains reaching the same allocation whose contexts share that suffix are the same atom.
     */
    static final class HeapContext implements Comparable<HeapContext> {
        /** The interned empty context (the context-free degenerate: same-frame atoms, hub pools). */
        static final HeapContext EMPTY = new HeapContext(List.of(), false);
        /**
         * The context of the one context-insensitive atom for a site whose owner/entering call could not be resolved.
         * Distinct from {@link #EMPTY}: a merged atom is visible in dumps and its return rule is "every caller".
         */
        static final HeapContext MERGED = new HeapContext(List.of(), true);

        private final List<ContextElement> elements;
        private final boolean merged;
        private final int hash;

        private HeapContext(List<ContextElement> elements, boolean merged) {
            this.elements = elements;
            this.merged = merged;
            this.hash = elements.hashCode() * (merged ? -13 : 1);
        }

        /**
         * The owner-merged form of a chain context, for a static chain's unknown instance owner; distinct from the
         * owner-specific contexts even where k-truncation drops the owner.
         */
        static HeapContext mergedOf(List<ContextElement> elements) {
            return elements.isEmpty() ? MERGED : new HeapContext(List.copyOf(elements), true);
        }

        /** The factory for arbitrary (policy-computed) element tuples. */
        static HeapContext of(List<ContextElement> elements) {
            return new HeapContext(List.copyOf(elements), false);
        }

        List<ContextElement> elements() {
            return elements;
        }

        int depth() {
            return elements.size();
        }

        boolean isMerged() {
            return merged;
        }

        @Override
        public int compareTo(HeapContext other) {
            if (merged != other.merged) {
                return merged ? 1 : -1;
            }
            int n = Math.min(elements.size(), other.elements.size());
            for (int i = 0; i < n; i++) {
                int c = ContextElement.CANONICAL_ORDER.compare(elements.get(i), other.elements.get(i));
                if (c != 0) {
                    return c;
                }
            }
            return Integer.compare(elements.size(), other.elements.size());
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!(obj instanceof HeapContext other)) {
                return false;
            }
            return merged == other.merged && hash == other.hash && elements.equals(other.elements);
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public String toString() {
            return merged ? "ctxMERGED" + (elements.isEmpty() ? "" : String.valueOf(elements)) : "ctx" + elements;
        }
    }

    // ------------------------------------------------------------------
    // The one-monitor lock discipline tripwire.
    //
    // Invariant (enforced by ContainerTables' collect-under/run-outside protocols, checked here at runtime): a thread
    // never holds one Table/Sink monitor while acquiring another's. With at most one such monitor held per thread, no
    // wait-for cycle between them exists at any thread count. Re-entering the same monitor is legal. Leaf locks (a
    // Waiter's exactly-once bitset lock, the LFG vertexLock) take nothing inside and are not bracketed.
    // ------------------------------------------------------------------

    /**
     * Per-thread state: which Table/Sink monitor this thread holds and how deep, plus the engine's per-thread container
     * state read by {@code RecursiveTracking}: the skipped-task count (the guard's "no work done" test) and, inside a
     * parallel container round, the thread's output buffer.
     */
    static final class MonState {
        Object owner;
        int depth;
        long skips;
        java.util.ArrayList<Runnable> out;
    }

    private static final ThreadLocal<MonState> MON = ThreadLocal.withInitial(MonState::new);

    /**
     * Engine worker thread carrying its {@link MonState} in a field, avoiding a ThreadLocal lookup per bracketing (a
     * visible cost). The driver thread uses {@link #DRIVER_MON}; other threads (unit tests) use the ThreadLocal.
     */
    static final class MonThread extends Thread {
        final MonState mon = new MonState();

        MonThread(Runnable r, String name, long stackSize) {
            super(null, r, name, stackSize);
        }
    }

    private static volatile Thread driverThread;
    private static final MonState DRIVER_MON = new MonState();

    /** The solve's driver thread (set once per solve; the driver's state is then a static field). */
    static void setDriver(Thread t) {
        driverThread = t;
    }

    /** This thread's engine state (worker field / driver static / ThreadLocal otherwise). */
    static MonState threadState() {
        return state();
    }

    private static MonState state() {
        Thread t = Thread.currentThread();
        if (t instanceof MonThread mt) {
            return mt.mon;
        }
        return t == driverThread ? DRIVER_MON : MON.get();
    }

    /** Nested acquisitions of a different monitor (must stay 0). */
    static final java.util.concurrent.atomic.LongAdder atomMonNestViolations = new java.util.concurrent.atomic.LongAdder();

    /** Same-monitor re-entrancy observed (diagnostic only). */
    static final java.util.concurrent.atomic.LongAdder atomMonReentries = new java.util.concurrent.atomic.LongAdder();

    /** Called immediately before acquiring {@code monitor}. */
    static void enterMon(Object monitor) {
        MonState m = state();
        if (m.owner == null) {
            m.owner = monitor;
            m.depth = 1;
        } else if (m.owner == monitor) {
            m.depth++;
            atomMonReentries.increment();
        } else {
            // Invariant broken: a cross-monitor nesting. Counted, never silent ([sug-fwd-lockorder] reports it).
            atomMonNestViolations.increment();
            m.depth++; // keep enter/exit balanced; the owner stays the outer monitor
        }
    }

    /** Called immediately after releasing {@code monitor}. */
    static void exitMon(Object monitor) {
        MonState m = state();
        if (--m.depth <= 0) {
            m.owner = null;
            m.depth = 0;
        }
    }

    /** The lock-discipline line (always printed; counters only). */
    static String lockOrderSummary() {
        return "[sug-fwd-lockorder] atomMonNestViolations=" + atomMonNestViolations.sum() +
                        " atomMonReentries=" + atomMonReentries.sum();
    }
}
