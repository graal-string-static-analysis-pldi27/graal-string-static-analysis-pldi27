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
import java.util.EnumSet;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.IntPredicate;

import com.oracle.svm.hosted.stringanalysis.ContextPolicy.CallPath;

/**
 * The recursive container-tracking substrate: {@link Table}, {@link EntryList}, {@link Waiter}, {@link Sink} and the
 * reaching-version pools ({@link FramePools}/{@link MemberPools}), with append/register protocols that make every
 * delivery exactly-once and every waiter a recipient of its table's refusals (the binding rule: registering on any list
 * of a table registers on its refusal set).
 *
 * <p>Grow-only everywhere: entries, waiters, refusals, sink atoms and the atom registry only grow. Completeness is
 * carried: a table is complete at quiescence iff its refusal set is empty; there is deliberately no "built" state a
 * reader may act on.
 *
 * <p>All mutators take exactly one table/sink monitor at a time and never run a continuation while holding it
 * (collect-under/run-outside; the invariant the {@code [sug-fwd-lockorder]} tripwire guards). Refusal wake-ups go
 * through {@link #DEFER}, so refusal chains do not recurse inline.
 */
final class ContainerTables {

    private ContainerTables() {
    }

    /**
     * How wake-ups that may cascade (refusal deliveries) are run: the engine
     * installs its queue ({@code RecursiveTracking}); unit tests run inline.
     */
    static volatile Consumer<Runnable> DEFER = Runnable::run;

    /**
     * The container drain's current round (determinism, the epoch rule). A table or sink records the round of its first
     * refusal; the stop rule for refused objects sees a refusal only from the next round on, so the work a refused object does depends on the
     * round contents, never on the schedule inside a round. Unit tests leave it at 0.
     */
    static volatile long ROUND;
    /** Census: stop-rule tests on an object first refused in the current round (live: stop; epoch: go on). */
    static final java.util.concurrent.atomic.LongAdder SAME_ROUND_STOP_TESTS = new java.util.concurrent.atomic.LongAdder();

    /** The epoch rule of {@code stopVisible}: a refusal first made in drain round {@code refusedRound} is visible from the next round on. */
    static boolean refusedBefore(long refusedRound) {
        if (refusedRound == ROUND) {
            SAME_ROUND_STOP_TESTS.increment(); // census: a test that the live rule answers "stop" inside the refusing round
        }
        return refusedRound < ROUND;
    }

    /** A refusal recipient (a table or a sink): refusing twice is a no-op. */
    interface Refusable {
        boolean hasRefusal(RTrackRefusal r);

        boolean hasAnyRefusal();

        /** Whether this object's result depends on a delivery of the object-return rule ({@code fwd.rtrack.objret=1}) (ID-DEP). */
        default boolean idDep() {
            return false;
        }

        /**
         * Set ID-DEP (monotone); answers the dependents to mark next (the waiters' / listeners' targets), empty when
         * it was set already. Run by {@link ContainerTables#markIdDep} only.
         */
        default List<Refusable> setIdDep() {
            return List.of();
        }

        /**
         * The stop rule's test: refused in an earlier round (the epoch rule); the default is the live test.
         *
         * <p>The stop rule for refused objects: once a table or a sink carries a refusal, its further growth can only feed
         * consumers that already received that refusal (refusals propagate to every consumer, whose candidates reject and
         * whose usage lists are suppressed), so the work is skipped (walk positions of a refused atom, backward steps of a
         * refused sink, continuations into a refused target). Every budget-measured quantity of an object depends only on
         * the tables it consumes, so a quantity a stopped object shrinks belongs to an object that is refused in every
         * schedule.
         *
         * <p>Determinism: a refusal becomes visible to this rule only from the drain round after the one in which the
         * object was first refused. Otherwise a parallel round could cut a refused object's work at a schedule-dependent
         * point and its refusal names (never its refused status) would vary run to run. Every item of a round runs
         * whatever the other items of that round refuse, so a refused object's partial content is a function of the round
         * contents; the serial drain runs the same rounds ({@code RecursiveTracking.drainSerialRounds}).
         */
        default boolean stopVisible() {
            return hasAnyRefusal();
        }
    }

    /**
     * Mark {@code start} as ID-DEP and, transitively, every object reading it along the waiter / listener edges
     * refusals travel. Iterative, no monitor held between objects. A reader without a target whose source is ID-DEP is
     * unaudited: counted in {@link #ID_DEP_UNTARGETED} and its consumer is not marked. Monotone; never refuses and never
     * changes a walk: only the cross-candidate precedence reads the flag.
     */
    static void markIdDep(Refusable start) {
        java.util.ArrayDeque<Refusable> work = new java.util.ArrayDeque<>();
        work.add(start);
        while (!work.isEmpty()) {
            Refusable r = work.poll();
            for (Refusable d : r.setIdDep()) {
                if (d != null && !d.idDep()) {
                    work.add(d);
                }
            }
        }
    }

    /** Census: deliveries of ID-DEP to a reader without a target (unaudited; its consumer is not marked). */
    static final java.util.concurrent.atomic.LongAdder ID_DEP_UNTARGETED = new java.util.concurrent.atomic.LongAdder();
    /** Census: the unaudited readers by waiter / listener key kind (the key's first element). */
    static final Map<String, java.util.concurrent.atomic.LongAdder> ID_DEP_UNTARGETED_BY = new ConcurrentHashMap<>();

    static void untargeted(Object key) {
        ID_DEP_UNTARGETED.increment();
        String k = key instanceof List<?> l && !l.isEmpty() ? String.valueOf(l.get(0)) : key == null ? "null" : key.getClass().getSimpleName();
        ID_DEP_UNTARGETED_BY.computeIfAbsent(k, x -> new java.util.concurrent.atomic.LongAdder()).increment();
    }

    /** Census: tables / sinks marked ID-DEP. */
    static final java.util.concurrent.atomic.LongAdder ID_DEP_TABLES = new java.util.concurrent.atomic.LongAdder();
    static final java.util.concurrent.atomic.LongAdder ID_DEP_SINKS = new java.util.concurrent.atomic.LongAdder();

    /**
     * The ID-DEP flag of a reader whose consumer is not a Table / Sink (the accumulator pass-2 receiver sinks,
     * {@code accrecv}): the reader's listener targets this flag, and the consumer (the accumulator extraction candidate)
     * is marked ID-DEP from it at emission, so an unaudited reader propagates conservatively. Never refused; monotone.
     */
    static final class DepFlag implements Refusable {
        private volatile boolean idDep;

        @Override
        public boolean hasRefusal(RTrackRefusal r) {
            return false;
        }

        @Override
        public boolean hasAnyRefusal() {
            return false;
        }

        @Override
        public boolean idDep() {
            return idDep;
        }

        @Override
        public List<Refusable> setIdDep() {
            idDep = true;
            return List.of();
        }
    }

    /**
     * The target of a reader that has no consumer (a census-only waiter, e.g. the named query's first-refusal
     * recorder): already ID-DEP, so the marking stops there, and it is not counted as unaudited.
     */
    static final Refusable NO_READER = new Refusable() {
        @Override
        public boolean hasRefusal(RTrackRefusal r) {
            return false;
        }

        @Override
        public boolean hasAnyRefusal() {
            return false;
        }

        @Override
        public boolean idDep() {
            return true;
        }
    };

    // ------------------------------------------------------------------
    // The refusal catalogue. Every refusal is a named mark, never a silent cut. budgetClass marks the budget-class
    // refusals, which take precedence over the usage validation (their usages are a schedule-dependent subset).
    // ------------------------------------------------------------------
    enum RTrackRefusal {
        WALK_BUDGET(true),
        BACKWARD_BUDGET(true),
        TRACK_DEPTH(true),
        STORE_FAN_CAP(true),
        CALLER_FAN_CAP(true),
        RETURN_FAN_CAP(true),
        EVALUATION_GUARD(true),
        /** A backward resolution resolved more than fwd.rtrack.sinkfan atoms. */
        SINK_ATOM_FAN(true),
        CHA_FAN_CAP(false),
        NO_TARGET(false),
        MISSING_IR(false),
        DARK_ENTRY(false),
        WORLD_TOP_ENTRY(false),
        BELT(false),
        UNCLASSIFIED_ACCESS(false),
        UNRESOLVED_VALUE(false),
        UNSAFE_ACCESS(false),
        REFLECTIVE_FIELD(false),
        EXCEPTION_FLOW_UNMODELLED(false),
        HEAP_SNAPSHOT_PENDING(false),
        /**
         * A constant's table needs its heap holders and the reverse holder index is unavailable (over its build budget,
         * or incomplete because a read reference slot is a pending future). Budget class.
         */
        CONSTANT_HOLDERS_UNINDEXED(true),
        /**
         * An access to thread-local state that bypasses the modelled operations: a tracked value entering the
         * {@code ThreadLocalMap}/{@code Entry} internals, an overridden {@code childValue} (inheritance not modelled), a
         * thread-local variable whose exact type is unknown.
         */
        THREAD_LOCAL_UNMODELLED(false),
        /**
         * A return with an empty path out of a frame whose outside caller is unmodelled (a native entry point, a direct
         * root, a virtual root, or an implementation reached through a virtual root's dispatch): the value reaches a
         * caller the analysis does not see. Forward twin of {@link #WORLD_TOP_ENTRY}. The world-top rule.
         */
        WORLD_TOP_EXIT(false),
        /**
         * A return with an empty path out of a frame that is not world-top and has no caller in the complete IR caller
         * index. Forward twin of {@link #DARK_ENTRY}. The no-caller rule.
         */
        NO_CALLER_EXIT(false),
        /**
         * The walked value is an argument of an invoke at a {@code StringConcatFactory} indy site whose IR the concat
         * recogniser does not recognise (not the F1 {@code linkToTargetMethod} form). This and the following constants
         * are appended last, so no earlier name moves in the printed order.
         */
        UNRECOGNISED_CONCAT(false),
        /**
         * JDK models ({@code JdkModels}, {@code JdkModelEngine}): a tracked value meets a modelled JDK family where the
         * model does not state the effect: an unlisted method of a closed class, an IR access to a field the family's
         * slots abstract, a slot the entry does not cover, an image-heap container of a modelled class. Never an IR
         * fallback.
         */
        JDK_MODEL_UNMODELLED(false),
        /**
         * A string atom is the argument (slot 1) of a call whose resolved target is {@code String.equals(Object)} and the
         * call has no Phase-A site, so the equals matrix cannot redirect it. Never entered: entering the body is a latent
         * hole for Lazy Concat, which excuses usages inside {@code String.equals}.
         */
        EQUALS_ARG_NO_SITE(false),
        /**
         * A seeded Single Byte literal (an {@code ldc} of a length-1 String) reaches an
         * identity observation ({@code ==}, {@code identityHashCode}, a monitor). The replacement swaps the interned
         * literal for the pooled {@code SingleByteString} at that one {@code ldc}, so its identity differs from the same
         * literal elsewhere.
         */
        LITERAL_IDENTITY(false),
        /**
         * Lambda object-identity tracking (premise: no foreign birth of the class): an identity query atom's Class object
         * escapes ({@code getClass()}, a hub load, {@code clone()}), so a foreign birth of its class (Unsafe, JNI, MH
         * {@code allocateInstance}) becomes possible and the class's birth set is not complete. Only query atoms refuse it
         * (for other atoms these are observations); the query then falls back to the dispatch fan.
         */
        CLASS_ESCAPE(false),
        /**
         * A quiet string atom's "no load" claim for an escape rests on a holder walk that ended without a recorded sound
         * reason (a path-less return whose caller set never delivered and never fell back; a return with no analysed
         * caller and no refusal). Refused at quiescence by the holder-end rule
         * ({@code HolderEndRule.holderEndRule}).
         */
        HOLDER_END_UNEXPLAINED(false),
        /**
         * The compareTo mirror ({@code StringAtoms.compareToArgRow}): a string atom is the argument (slot 1) of a call
         * whose resolved target is {@code String.compareTo(String)} and the call has no Phase-A site the parent could
         * redirect to {@code maybeCustomStringCompareTo} (no vertex, an inlined-scope invoke, a reflective crossing), or
         * of the bridge {@code compareTo(Object)} without its internal site. Never entered (the stock body reads the argument's {@code value}).
         */
        COMPARETO_ARG_NO_SITE(false),
        /**
         * A string atom has a usage keyed in a hidden class (a
         * lambda proxy {@code $$Lambda}, a {@code /0x} hidden class; the concat machinery excepted). Such keys are
         * unstable between child and parent (lambda-proxy renaming is stable only single-threaded), so the parent could
         * miss the site (an equals-argument redirect that never matches) or apply another proxy's entry.
         */
        HIDDEN_SINK(false),
        /**
         * The builder-append mirror ({@code StringAtoms.mirrorArgRow}, knob {@code svm.stringanalysis.mirror.append},
         * default 1): a string atom is the string argument of a call whose resolved target is a builder
         * append/insert/replace/constructor entry point ({@link AppendMirror}) and the call has no site the parent could
         * lower to the mirror (no Phase-A vertex, an inlined-scope invoke, an interface-declared invoke, a hidden-class
         * key, a model callback without such sites). Never entered (the stock body would receive the rep).
         */
        MIRROR_ARG_NO_SITE(false);

        final boolean budgetClass;

        RTrackRefusal(boolean budgetClass) {
            this.budgetClass = budgetClass;
        }

        /** The verdict class a string dependent receives for this refusal. */
        TransferFacts.IncompleteReason verdictReason() {
            if (budgetClass) {
                return TransferFacts.IncompleteReason.RESOURCE_LIMIT;
            }
            return switch (this) {
                case CHA_FAN_CAP, NO_TARGET -> TransferFacts.IncompleteReason.UNKNOWN_TARGET;
                case MISSING_IR -> TransferFacts.IncompleteReason.MISSING_IR;
                case DARK_ENTRY, BELT, NO_CALLER_EXIT, HOLDER_END_UNEXPLAINED -> TransferFacts.IncompleteReason.INCOMPLETE_TRAVERSAL;
                default -> TransferFacts.IncompleteReason.UNTRACKABLE_CONTAINER;
            };
        }
    }

    // ------------------------------------------------------------------
    // EntryList: append-only list + waiters, both mutated only under the owning table's monitor; entries deduped by a
    // caller-supplied key.
    // ------------------------------------------------------------------
    static final class EntryList<T> {
        final Table table;
        final String kind;
        /**
         * Lock-free reads of the append-only entry array. Appends run under the table monitor; {@link #get}/{@link #size}
         * read without it. Safe: an index is read only after the append that wrote it, the slot is written before the
         * volatile publication, and a grown copy is made under the monitor after every earlier slot write, so every
         * published array holds every published index.
         */
        private volatile Object[] entryArr = new Object[2];
        private volatile int entryCount;
        private final Set<Object> dedup = new HashSet<>(4);
        /** The distinct (frame, IR node) accesses — STORE_FAN_CAP's measure ("distinct stores"). */
        private final Set<Object> distinctNodes = new HashSet<>(4);
        private final List<Waiter> waiters = new ArrayList<>(2);
        private final Set<Object> waiterKeys = new HashSet<>(4);

        EntryList(Table table, String kind) {
            this.table = table;
            this.kind = kind;
        }

        int size() {
            return entryCount;
        }

        @SuppressWarnings("unchecked")
        T get(int idx) {
            if (idx < 0 || idx >= entryCount) {
                throw new IndexOutOfBoundsException(idx + " / " + entryCount);
            }
            return (T) entryArr[idx];
        }

        int waiterCount() {
            ContainerAtoms.enterMon(table.monitor);
            try {
                synchronized (table.monitor) {
                    return waiters.size();
                }
            } finally {
                ContainerAtoms.exitMon(table.monitor);
            }
        }

        /**
         * Append an entry (deduped). Returns the new index, or -1 for a duplicate (a no-op that wakes nobody). Existing
         * waiters get a {@link Waiter#deliver} for the new index, outside the monitor.
         */
        int append(T entry, Object dedupKey) {
            return append(entry, dedupKey, null);
        }

        int distinctNodeCount() {
            ContainerAtoms.enterMon(table.monitor);
            try {
                synchronized (table.monitor) {
                    return distinctNodes.size();
                }
            } finally {
                ContainerAtoms.exitMon(table.monitor);
            }
        }

        int append(T entry, Object dedupKey, Object nodeKey) {
            int idx;
            Waiter[] snap;
            ContainerAtoms.enterMon(table.monitor);
            try {
                synchronized (table.monitor) {
                    if (!dedup.add(dedupKey)) {
                        return -1;
                    }
                    distinctNodes.add(nodeKey != null ? nodeKey : dedupKey);
                    idx = entryCount;
                    Object[] a = entryArr;
                    if (idx == a.length) {
                        a = java.util.Arrays.copyOf(a, Math.max(4, a.length * 2));
                    }
                    a[idx] = entry;
                    entryArr = a;
                    entryCount = idx + 1;
                    snap = waiters.toArray(new Waiter[0]);
                }
            } finally {
                ContainerAtoms.exitMon(table.monitor);
            }
            for (Waiter w : snap) {
                w.deliver(idx);
            }
            return idx;
        }

        /**
         * Register a waiter (deduped by its semantic key). It fires for every existing and future entry and, by the
         * binding rule, receives the table's existing and future refusals (registering on any list of T registers on
         * T's refusal set). Returns false for a no-op registration.
         */
        boolean register(Waiter w) {
            int count;
            RTrackRefusal[] refs;
            boolean dep;
            ContainerAtoms.enterMon(table.monitor);
            try {
                synchronized (table.monitor) {
                    if (!waiterKeys.add(w.key)) {
                        return false; // a no-op registration (the dedup)
                    }
                    waiters.add(w);
                    table.allWaiters.add(w);
                    count = entryCount;
                    refs = table.refusals.toArray(new RTrackRefusal[0]);
                    dep = table.idDep;
                }
            } finally {
                ContainerAtoms.exitMon(table.monitor);
            }
            if (dep) {
                Refusable d = w.idDepTarget(); // a reader of an ID-DEP table (before its entries: a dependence on it)
                if (d != null) {
                    markIdDep(d);
                }
            }
            for (int i = 0; i < count; i++) {
                w.deliver(i);
            }
            for (RTrackRefusal r : refs) {
                w.deliverRefusal(r);
            }
            return true;
        }
    }

    // ------------------------------------------------------------------
    // Waiter: a continuation parked on one entry list (pool grain expressed by the filter), woken exactly once per
    // (waiter, entry) and per (waiter, refusal).
    // ------------------------------------------------------------------
    static final class Waiter {
        /** The semantic identity: registering an equal key twice on one list is a no-op. */
        final Object key;
        /** Fires per entry index (with no monitor held). */
        final Consumer<Integer> continuation;
        /** Optional pool filter (the reaching-version pools): the delivery runs only when it passes. */
        final IntPredicate filter;
        /** Receives the table's refusals (the binding rule). */
        final Consumer<RTrackRefusal> onRefusal;
        /**
         * The object {@link #onRefusal} refuses, if any: a refusal it already carries needs no wake-up (refusal is
         * idempotent, so skipping is exact and avoids a flood of no-op queue items).
         */
        final Refusable refusalTarget;
        /** The object this waiter's continuation feeds (ID-DEP travels there); by default the refusal target. */
        final Refusable depTarget;
        private final BitSet delivered = new BitSet();
        private final EnumSet<RTrackRefusal> refusalsSeen = EnumSet.noneOf(RTrackRefusal.class);

        Waiter(Object key, Consumer<Integer> continuation, IntPredicate filter, Consumer<RTrackRefusal> onRefusal) {
            this(key, continuation, filter, onRefusal, null);
        }

        Waiter(Object key, Consumer<Integer> continuation, IntPredicate filter, Consumer<RTrackRefusal> onRefusal,
                        Refusable refusalTarget) {
            this(key, continuation, filter, onRefusal, refusalTarget, refusalTarget);
        }

        Waiter(Object key, Consumer<Integer> continuation, IntPredicate filter, Consumer<RTrackRefusal> onRefusal,
                        Refusable refusalTarget, Refusable depTarget) {
            this.key = key;
            this.continuation = continuation;
            this.filter = filter;
            this.onRefusal = onRefusal;
            this.refusalTarget = refusalTarget;
            this.depTarget = depTarget;
        }

        /** The dependent to mark when the source list's table is ID-DEP (null = unaudited, counted). */
        Refusable idDepTarget() {
            if (depTarget == null) {
                untargeted(key);
            }
            return depTarget;
        }

        /** Exactly-once per (waiter, entry); the filter gates pool grain. */
        void deliver(int idx) {
            synchronized (this) {
                if (delivered.get(idx)) {
                    return;
                }
                delivered.set(idx);
            }
            if (filter != null && !filter.test(idx)) {
                return;
            }
            continuation.accept(idx);
        }

        /** Exactly-once per (waiter, refusal) — the wake-on-refusal path. */
        void deliverRefusal(RTrackRefusal r) {
            synchronized (this) {
                if (!refusalsSeen.add(r)) {
                    return;
                }
            }
            if (onRefusal != null && (refusalTarget == null || !refusalTarget.hasRefusal(r))) {
                DEFER.accept(() -> onRefusal.accept(r));
            }
        }
    }

    // ------------------------------------------------------------------
    // Table: one per owner (an rtrack atom key, or a static field). Complete is computed at quiescence as
    // refusals.isEmpty().
    // ------------------------------------------------------------------
    static final class Table implements Refusable {
        /** The rtrack atom key, or the static {@code AnalysisField}. */
        final Object owner;
        final Object monitor = new Object();
        volatile boolean buildScheduled;
        /** A length-0 array atom — complete by proof, never walked. */
        final boolean completeByProof;
        private final EnumSet<RTrackRefusal> refusals = EnumSet.noneOf(RTrackRefusal.class);
        private final List<Waiter> allWaiters = new ArrayList<>(2);
        final Map<Object, EntryList<StoreEntry>> stores = new ConcurrentHashMap<>();
        final Map<Object, EntryList<LoadEntry>> loads = new ConcurrentHashMap<>();
        /** How this atom's walk entered each method (atom tables only). */
        final Map<LocalFlowGraph, EntryList<CallPath>> entryPaths = new ConcurrentHashMap<>();
        /**
         * The grow-only edge registry of the recursion folds this table owns, keyed (root frame, target frame): by owner
         * and root only, never by a fold's {@code next}, so a truncated copy of a fold keeps its registry. Waiters on these
         * lists take no refusals: the registry is crossings, not contents.
         */
        final Map<List<LocalFlowGraph>, EntryList<ContextPolicy.FoldEdge>> foldEdges = new ConcurrentHashMap<>();
        /** This owner's interned {@code FoldInfo}s (keyed (root, rootMctx, owner)). */
        final Map<Object, ContextPolicy.FoldInfo> foldIntern = new ConcurrentHashMap<>();
        /** Per member the reaching-version structure (lazily, per frame). */
        final Map<Object, MemberPools> pools = new ConcurrentHashMap<>();
        /**
         * Clone (the clone atom's own table): {@code clone.m = src.m} for every member m, seeded into {@code stores(m)}
         * when the member list is first created (null otherwise).
         */
        volatile Function<Object, List<StoreEntry>> implicitStore;
        /**
         * Clone (the source side): a clone node reading every member of this atom; each seeds a desugared load into every
         * {@code loads(m)} list (existing ones now, future ones at creation).
         */
        private final List<Function<Object, LoadEntry>> wildcardLoads = new ArrayList<>(0);

        Table(Object owner, boolean completeByProof) {
            this.owner = owner;
            this.completeByProof = completeByProof;
        }

        EntryList<StoreEntry> stores(Object member) {
            EntryList<StoreEntry> l = stores.get(member);
            if (l != null) {
                return l;
            }
            l = stores.computeIfAbsent(member, k -> new EntryList<>(this, "stores"));
            Function<Object, List<StoreEntry>> imp = implicitStore;
            if (imp != null) {
                for (StoreEntry e : imp.apply(member)) {
                    l.append(e, e.dedupKey(), e.nodeKey());
                }
            }
            return l;
        }

        EntryList<LoadEntry> loads(Object member) {
            EntryList<LoadEntry> l = loads.get(member);
            if (l != null) {
                return l;
            }
            l = loads.computeIfAbsent(member, k -> new EntryList<>(this, "loads"));
            List<Function<Object, LoadEntry>> wl;
            ContainerAtoms.enterMon(monitor);
            try {
                synchronized (monitor) {
                    wl = wildcardLoads.isEmpty() ? List.of() : List.copyOf(wildcardLoads);
                }
            } finally {
                ContainerAtoms.exitMon(monitor);
            }
            for (Function<Object, LoadEntry> f : wl) {
                LoadEntry e = f.apply(member);
                l.append(e, e.dedupKey());
            }
            return l;
        }

        /** A clone of this atom reads every member (now and for future member lists). */
        void addWildcardLoad(Function<Object, LoadEntry> factory) {
            List<Map.Entry<Object, EntryList<LoadEntry>>> existing;
            ContainerAtoms.enterMon(monitor);
            try {
                synchronized (monitor) {
                    wildcardLoads.add(factory);
                    existing = new ArrayList<>(loads.entrySet());
                }
            } finally {
                ContainerAtoms.exitMon(monitor);
            }
            for (Map.Entry<Object, EntryList<LoadEntry>> e : existing) {
                LoadEntry le = factory.apply(e.getKey());
                e.getValue().append(le, le.dedupKey());
            }
        }

        EntryList<CallPath> entryPaths(LocalFlowGraph frame) {
            return entryPaths.computeIfAbsent(frame, k -> new EntryList<>(this, "entryPaths"));
        }

        /** The registered edges of this table's folds with root {@code root} that call into {@code target}. */
        EntryList<ContextPolicy.FoldEdge> foldEdges(LocalFlowGraph root, LocalFlowGraph target) {
            return foldEdges.computeIfAbsent(List.of(root, target), k -> new EntryList<>(this, "foldEdges"));
        }

        MemberPools pools(Object member) {
            return pools.computeIfAbsent(member, k -> new MemberPools(member));
        }

        boolean refused() {
            ContainerAtoms.enterMon(monitor);
            try {
                synchronized (monitor) {
                    return !refusals.isEmpty();
                }
            } finally {
                ContainerAtoms.exitMon(monitor);
            }
        }

        /** The drain round of the first refusal (MAX = unrefused; the epoch rule); written under the monitor. */
        private volatile long refusedRound = Long.MAX_VALUE;

        @Override
        public boolean stopVisible() {
            return refusedBefore(refusedRound);
        }

        @Override
        public boolean hasRefusal(RTrackRefusal r) {
            ContainerAtoms.enterMon(monitor);
            try {
                synchronized (monitor) {
                    return refusals.contains(r);
                }
            } finally {
                ContainerAtoms.exitMon(monitor);
            }
        }

        @Override
        public boolean hasAnyRefusal() {
            return refused();
        }

        List<RTrackRefusal> refusalsSnapshot() {
            ContainerAtoms.enterMon(monitor);
            try {
                synchronized (monitor) {
                    return List.copyOf(refusals);
                }
            } finally {
                ContainerAtoms.exitMon(monitor);
            }
        }

        int waiterCount() {
            ContainerAtoms.enterMon(monitor);
            try {
                synchronized (monitor) {
                    return allWaiters.size();
                }
            } finally {
                ContainerAtoms.exitMon(monitor);
            }
        }

        /** ID-DEP (monotone; written under the monitor). */
        private volatile boolean idDep;

        @Override
        public boolean idDep() {
            return idDep;
        }

        @Override
        public List<Refusable> setIdDep() {
            Waiter[] snap;
            ContainerAtoms.enterMon(monitor);
            try {
                synchronized (monitor) {
                    if (idDep) {
                        return List.of();
                    }
                    idDep = true;
                    snap = allWaiters.toArray(new Waiter[0]);
                }
            } finally {
                ContainerAtoms.exitMon(monitor);
            }
            ID_DEP_TABLES.increment();
            List<Refusable> out = new ArrayList<>(snap.length);
            for (Waiter w : snap) {
                out.add(w.idDepTarget());
            }
            return out;
        }

        /**
         * Record a refusal (deduped) and wake every waiter on any list of this table (the binding rule), with the same
         * append-and-wake discipline as entries. Returns true when the refusal is new.
         */
        boolean refuse(RTrackRefusal r) {
            Waiter[] snap;
            ContainerAtoms.enterMon(monitor);
            try {
                synchronized (monitor) {
                    if (!refusals.add(r)) {
                        return false;
                    }
                    if (refusedRound == Long.MAX_VALUE) {
                        refusedRound = ROUND;
                    }
                    snap = allWaiters.toArray(new Waiter[0]);
                }
            } finally {
                ContainerAtoms.exitMon(monitor);
            }
            for (Waiter w : snap) {
                w.deliverRefusal(r);
            }
            return true;
        }
    }

    // ------------------------------------------------------------------
    // Entries. Frames are null only for build-time store entries, which connect to every load by construction.
    // ------------------------------------------------------------------
    /**
     * The entry identity, deduped by (frame, node, path, mctx). A (frame, node) key would drop a second route (another
     * call path / method context) to the same store or load, so its other callers / return paths would never be
     * explored (a false-ADMIT hole, and first-route-wins is schedule dependent). The (frame, node) half is the pool
     * identity and the STORE_FAN_CAP measure.
     */
    record EntryKey(Object frame, Object node, CallPath path, Object mctx) {
    }

    /** A store or load entry: its keys by position (a build-time entry, frame null, keys as "bt"). */
    interface TableEntry {
        LocalFlowGraph frame();

        Object node();

        CallPath path();

        Object mctx();

        default Object dedupKey() {
            return new EntryKey(frame() == null ? (Object) "bt" : frame(), node(), path(), mctx());
        }

        default Object nodeKey() {
            return List.of(frame() == null ? (Object) "bt" : frame(), node());
        }
    }

    record StoreEntry(LocalFlowGraph frame, Object node, Object value, CallPath path, Object mctx) implements TableEntry {
    }

    record LoadEntry(LocalFlowGraph frame, Object node, CallPath path, Object mctx) implements TableEntry {
    }

    // ------------------------------------------------------------------
    // Sink: the monotone result of one backward tracking (grow-only atom set, refusal set, per-sink visited set),
    // identified by its root (frame, node, mctx, path). The result is a pure function of the root (every backward rule
    // reads only the position and the monotone tables), so equal roots share one sink and every consumer attaches as a
    // listener, delivered exactly once per (listener, atom) / (listener, refusal).
    // ------------------------------------------------------------------
    /**
     * The visited key (frame, node, path, mctx), a fixed-hash quadruple. The whole method context is part of the
     * position because {@code backward} reads it (the parameter case's owner shortcut, the load case's base sink, the
     * popped link's restored caller context; {@code mintStatic} and the load case read static contexts too). A
     * (frame, node, path) key would drop a second route under a different context with no refusal.
     */
    static final class VisitKey {
        final Object frame;
        final Object node;
        final CallPath path;
        final Object mctx;
        final int hash;

        VisitKey(Object frame, Object node, CallPath path, Object mctx) {
            this.frame = frame;
            this.node = node;
            this.path = path;
            this.mctx = mctx;
            int h = System.identityHashCode(frame) * 31 + System.identityHashCode(node) * 7;
            h = h * 31 + (path != null ? path.hashCode() : 0);
            this.hash = h * 31 + (mctx != null ? mctx.hashCode() : 0);
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!(obj instanceof VisitKey o)) {
                return false;
            }
            return hash == o.hash && frame == o.frame && node == o.node && (path == o.path || (path != null && path.equals(o.path))) &&
                            (mctx == o.mctx || (mctx != null && mctx.equals(o.mctx)));
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    /** A consumer of a sink's monotone result (onAtom / onRefusal run with no monitor held). */
    record Listener(Object key, Consumer<Object> onAtom, Consumer<RTrackRefusal> onRefusal, Refusable refusalTarget, Refusable depTarget) {
        Listener(Object key, Consumer<Object> onAtom, Consumer<RTrackRefusal> onRefusal) {
            this(key, onAtom, onRefusal, null, null);
        }

        /** The dependent (ID-DEP) is the refusal target unless given ({@code depTarget}). */
        Listener(Object key, Consumer<Object> onAtom, Consumer<RTrackRefusal> onRefusal, Refusable refusalTarget) {
            this(key, onAtom, onRefusal, refusalTarget, refusalTarget);
        }

        void refuse(RTrackRefusal r) {
            if (onRefusal != null && (refusalTarget == null || !refusalTarget.hasRefusal(r))) {
                DEFER.accept(() -> onRefusal.accept(r));
            }
        }

        /** The dependent of an ID-DEP sink (null = unaudited, counted). */
        Refusable idDepTarget() {
            if (depTarget == null) {
                untargeted(key);
            }
            return depTarget;
        }
    }

    static final class Sink implements Refusable {
        static final class Stats {
            final AtomicLong maxVisited = new AtomicLong();
            final AtomicLong sumVisited = new AtomicLong();
            final AtomicLong count = new AtomicLong();
            final AtomicLong trackDepthMax = new AtomicLong();
            private final long[] hist = new long[9];

            void record(int visitedSize, int trackDepth) {
                count.incrementAndGet();
                sumVisited.addAndGet(visitedSize);
                maxVisited.getAndAccumulate(visitedSize, Math::max);
                trackDepthMax.getAndAccumulate(trackDepth, Math::max);
                int b = visitedSize <= 0 ? 0
                                : visitedSize == 1 ? 1
                                                : visitedSize <= 4 ? 2
                                                                : visitedSize <= 16 ? 3
                                                                                : visitedSize <= 32 ? 4
                                                                                                : visitedSize <= 64 ? 5
                                                                                                                : visitedSize <= 128 ? 6 : visitedSize <= 512 ? 7 : 8;
                synchronized (this) {
                    hist[b]++;
                }
            }

            String histogram() {
                String[] labels = {"0", "1", "2-4", "5-16", "17-32", "33-64", "65-128", "129-512", "513+"};
                StringBuilder sb = new StringBuilder("[");
                synchronized (this) {
                    for (int i = 0; i < hist.length; i++) {
                        if (i > 0) {
                            sb.append(' ');
                        }
                        sb.append(labels[i]).append(':').append(hist[i]);
                    }
                }
                return sb.append(']').toString();
            }
        }

        final Object rootKey;
        private final Set<Object> atoms = new java.util.LinkedHashSet<>(2);
        private final EnumSet<RTrackRefusal> refusals = EnumSet.noneOf(RTrackRefusal.class);
        private final List<Listener> listeners = new ArrayList<>(1);
        private final Set<Object> listenerKeys = new HashSet<>(2);
        final Set<VisitKey> visited = ConcurrentHashMap.newKeySet();
        /** |visited| before a release (the distribution statistic survives the release). */
        volatile int peakVisited;
        /** The aggregate load-case engagement count (TRACK_DEPTH proxy). */
        final AtomicLong trackDepth = new AtomicLong();
        /** The backward-budget measure: |visited|. */
        final int backwardBudget;
        final int trackDepthCap;

        Sink(Object rootKey, int backwardBudget, int trackDepthCap) {
            this.rootKey = rootKey;
            this.backwardBudget = backwardBudget;
            this.trackDepthCap = trackDepthCap;
        }

        /** Add a visited key; false when already present (per-sink visited; context-sensitive). */
        boolean visit(Object frame, Object node, CallPath pathSuffix, Object mctx) {
            return visited.add(new VisitKey(frame, node, pathSuffix, mctx));
        }

        int listenerCount() {
            ContainerAtoms.enterMon(this);
            try {
                synchronized (this) {
                    return listeners.size();
                }
            } finally {
                ContainerAtoms.exitMon(this);
            }
        }

        boolean refused() {
            ContainerAtoms.enterMon(this);
            try {
                synchronized (this) {
                    return !refusals.isEmpty();
                }
            } finally {
                ContainerAtoms.exitMon(this);
            }
        }

        /** The drain round of the first refusal (MAX = unrefused; the epoch rule); written under the monitor. */
        private volatile long refusedRound = Long.MAX_VALUE;

        @Override
        public boolean stopVisible() {
            return refusedBefore(refusedRound);
        }

        @Override
        public boolean hasRefusal(RTrackRefusal r) {
            ContainerAtoms.enterMon(this);
            try {
                synchronized (this) {
                    return refusals.contains(r);
                }
            } finally {
                ContainerAtoms.exitMon(this);
            }
        }

        @Override
        public boolean hasAnyRefusal() {
            return refused();
        }

        /**
         * Attach a listener (deduped by key): it receives every atom and refusal already in the sink and every future
         * one, exactly once. Returns false for a no-op.
         */
        boolean addListener(Listener l) {
            Object[] atomSnap;
            RTrackRefusal[] refSnap;
            boolean dep;
            ContainerAtoms.enterMon(this);
            try {
                synchronized (this) {
                    if (!listenerKeys.add(l.key())) {
                        return false;
                    }
                    listeners.add(l);
                    atomSnap = atoms.toArray();
                    refSnap = refusals.toArray(new RTrackRefusal[0]);
                    dep = idDep;
                }
            } finally {
                ContainerAtoms.exitMon(this);
            }
            if (dep) {
                Refusable d = l.idDepTarget(); // a reader of an ID-DEP sink
                if (d != null) {
                    markIdDep(d);
                }
            }
            for (Object a : atomSnap) {
                if (l.onAtom() != null) {
                    l.onAtom().accept(a);
                }
            }
            for (RTrackRefusal r : refSnap) {
                l.refuse(r);
            }
            return true;
        }

        /** The resolved-atom count (a set size of this sink's own monotone result). */
        int atomCount() {
            ContainerAtoms.enterMon(this);
            try {
                synchronized (this) {
                    return atoms.size();
                }
            } finally {
                ContainerAtoms.exitMon(this);
            }
        }

        boolean addAtom(Object atomKey) {
            Listener[] snap;
            ContainerAtoms.enterMon(this);
            try {
                synchronized (this) {
                    if (!atoms.add(atomKey)) {
                        return false;
                    }
                    snap = listeners.toArray(new Listener[0]);
                }
            } finally {
                ContainerAtoms.exitMon(this);
            }
            for (Listener l : snap) {
                if (l.onAtom() != null) {
                    l.onAtom().accept(atomKey);
                }
            }
            return true;
        }

        /** ID-DEP (monotone; written under the monitor). */
        private volatile boolean idDep;

        @Override
        public boolean idDep() {
            return idDep;
        }

        @Override
        public List<Refusable> setIdDep() {
            Listener[] snap;
            ContainerAtoms.enterMon(this);
            try {
                synchronized (this) {
                    if (idDep) {
                        return List.of();
                    }
                    idDep = true;
                    snap = listeners.toArray(new Listener[0]);
                }
            } finally {
                ContainerAtoms.exitMon(this);
            }
            ID_DEP_SINKS.increment();
            List<Refusable> out = new ArrayList<>(snap.length);
            for (Listener l : snap) {
                out.add(l.idDepTarget());
            }
            return out;
        }

        boolean refuse(RTrackRefusal r) {
            Listener[] snap;
            ContainerAtoms.enterMon(this);
            try {
                synchronized (this) {
                    if (!refusals.add(r)) {
                        return false;
                    }
                    if (refusedRound == Long.MAX_VALUE) {
                        refusedRound = ROUND;
                    }
                    snap = listeners.toArray(new Listener[0]);
                }
            } finally {
                ContainerAtoms.exitMon(this);
            }
            for (Listener l : snap) {
                l.refuse(r);
            }
            return true;
        }

        List<Object> atomsSnapshot() {
            ContainerAtoms.enterMon(this);
            try {
                synchronized (this) {
                    return List.copyOf(atoms);
                }
            } finally {
                ContainerAtoms.exitMon(this);
            }
        }

        List<RTrackRefusal> refusalsSnapshot() {
            ContainerAtoms.enterMon(this);
            try {
                synchronized (this) {
                    return List.copyOf(refusals);
                }
            } finally {
                ContainerAtoms.exitMon(this);
            }
        }
    }

    // ------------------------------------------------------------------
    // The reaching-version pools. Per (table, member, frame) a reaching-definitions dataflow over the frame's fixed
    // IR: GEN = a member store; KILL = only a store whose receiver is the same SSA value (aliases may-merge, never
    // separate: the soundness asymmetry); JOIN = union. The result is a pure function of the fixed IR (deterministic;
    // it may be computed lazily at first record). FrameCfg makes it unit testable; the production adapter builds it
    // from the frame's scheduled IR (RecursiveTracking).
    // ------------------------------------------------------------------
    static final class PoolAccess {
        final int id;
        final boolean store;
        /** The receiver SSA value (identity-compared). */
        final Object receiver;
        final int block;
        final int order;
        /** The IR access node the table entries carry (the lookup key of connected()). */
        final Object node;

        PoolAccess(int id, boolean store, Object receiver, int block, int order, Object node) {
            this.id = id;
            this.store = store;
            this.receiver = receiver;
            this.block = block;
            this.order = order;
            this.node = node;
        }
    }

    /**
     * Dataflow events that are not member accesses: an {@link #INVOKE} (any node that may run analysed code; the same
     * method may re-enter on the same object, so every E_w is re-generated after it) and a receiver's {@link #DEF}
     * point (the execution of the receiver's SSA definition: its fresh stores become stale, never killed again, and
     * E_receiver is re-generated). {@code order} uses the scale of {@link PoolAccess#order}.
     */
    static final class PoolEvent {
        static final int INVOKE = 0;
        static final int DEF = 1;
        final int kind;
        final Object receiver;
        final int block;
        final int order;

        PoolEvent(int kind, Object receiver, int block, int order) {
            this.kind = kind;
            this.receiver = receiver;
            this.block = block;
            this.order = order;
        }

        static PoolEvent invoke(int block, int order) {
            return new PoolEvent(INVOKE, null, block, order);
        }

        static PoolEvent def(Object receiver, int block, int order) {
            return new PoolEvent(DEF, receiver, block, order);
        }
    }

    /**
     * The pure CFG input of one frame's member dataflow. Every E_w is generated at {@code entryBlock}; {@code events}
     * holds the invoke and receiver-definition points; {@code neverKill} names receivers whose definition point could
     * not be located: their stores are never killed (the coarse, sound form of the staleness rule for that receiver).
     */
    record FrameCfg(int nBlocks, int[][] predecessors, List<PoolAccess> accesses, int entryBlock, List<PoolEvent> events,
                    Set<Object> neverKill) {
        FrameCfg(int nBlocks, int[][] predecessors, List<PoolAccess> accesses) {
            this(nBlocks, predecessors, accesses, 0, List.of(), Set.of());
        }
    }

    /**
     * The per-frame reaching computation for one member: for every load, the store accesses that may reach it along
     * the CFG (loop back edges included). Deterministic: the least fixpoint of a monotone function over a finite
     * lattice is independent of the worklist order.
     */
    static final class FramePools {
        /** Per load id: every version that may reach it (stores fresh ∪ stale, and E bits). */
        private final BitSet[] reachingAtLoad;
        /** Per load id: the E-bit id of the load's own receiver, or -1. */
        private final int[] eOfLoad;
        /** IR store node → its access (a node may be both a load and a store: the desugared copy). */
        private final Map<Object, PoolAccess> storeByNode;
        private final Map<Object, PoolAccess> loadByNode;

        private FramePools(BitSet[] reachingAtLoad, int[] eOfLoad, Map<Object, PoolAccess> storeByNode,
                        Map<Object, PoolAccess> loadByNode) {
            this.reachingAtLoad = reachingAtLoad;
            this.eOfLoad = eOfLoad;
            this.storeByNode = storeByNode;
            this.loadByNode = loadByNode;
        }

        /**
         * One dataflow step in block order: an access or a {@link PoolEvent}. Within one position: loads, stores, then
         * events (an invoke's re-entry and a definition take effect after the node).
         */
        private record Step(int order, int rank, PoolAccess access, PoolEvent event) {
        }

        /** The dataflow fact: fresh store versions (killable), stale store versions (never killed), E bits (in fresh). */
        private static final class Fact {
            final BitSet fresh;
            final BitSet stale;

            Fact(BitSet fresh, BitSet stale) {
                this.fresh = fresh;
                this.stale = stale;
            }

            Fact copy() {
                return new Fact((BitSet) fresh.clone(), (BitSet) stale.clone());
            }

            @Override
            public boolean equals(Object o) {
                return o instanceof Fact f && fresh.equals(f.fresh) && stale.equals(f.stale);
            }

            @Override
            public int hashCode() {
                return fresh.hashCode() * 31 + stale.hashCode();
            }
        }

        /**
         * The reaching-definitions dataflow with the other-invocation and staleness amendments (one computation for
         * every member of every frame):
         * <ul>
         * <li>GEN = a member store (a fresh version); KILL = a store on the same receiver SSA value kills only the fresh
         * same-receiver versions (aliases may-merge, never separate);</li>
         * <li>the other-invocation version E_w per receiver SSA value w, generated at frame entry and after every
         * {@link PoolEvent#INVOKE}, killed by a store on w;</li>
         * <li>staleness: at w's definition point the fresh stores on w become stale (a re-executed definition names
         * another object, so a later store on w cannot overwrite the earlier one's object) and E_w is re-generated (a
         * kill of E_w never survives a re-execution of w's definition);</li>
         * <li>JOIN = union of both the fresh and the stale sets.</li>
         * </ul>
         * The least fixpoint is unique, independent of the iteration order.
         */
        static FramePools compute(FrameCfg cfg) {
            List<PoolAccess> accesses = cfg.accesses();
            int n = accesses.size();
            Map<Object, PoolAccess> storeByNode = new IdentityHashMap<>();
            Map<Object, PoolAccess> loadByNode = new IdentityHashMap<>();
            for (PoolAccess a : accesses) {
                (a.store ? storeByNode : loadByNode).put(a.node, a);
            }
            Object[] receiverById = new Object[n];
            boolean[] killable = new boolean[n];
            Map<Object, Integer> eId = new IdentityHashMap<>();
            for (PoolAccess a : accesses) {
                receiverById[a.id] = a.receiver;
                killable[a.id] = !cfg.neverKill().contains(a.receiver);
                eId.computeIfAbsent(a.receiver, k -> n + eId.size());
            }
            int nb = cfg.nBlocks();
            List<List<Step>> steps = new ArrayList<>(nb);
            for (int b = 0; b < nb; b++) {
                steps.add(new ArrayList<>());
            }
            for (PoolAccess a : accesses) {
                steps.get(a.block).add(new Step(a.order, a.store ? 1 : 0, a, null));
            }
            for (PoolEvent e : cfg.events()) {
                if (e.block >= 0 && e.block < nb) {
                    steps.get(e.block).add(new Step(e.order, 2 + e.kind, null, e));
                }
            }
            for (List<Step> l : steps) {
                l.sort(java.util.Comparator.comparingInt(Step::order).thenComparingInt(Step::rank));
            }
            BitSet allE = new BitSet();
            for (int id : eId.values()) {
                allE.set(id);
            }
            Ctx ctx = new Ctx(receiverById, killable, eId, allE);
            Fact[] in = new Fact[nb];
            Fact[] out = new Fact[nb];
            for (int b = 0; b < nb; b++) {
                in[b] = entryFact(cfg, b, allE);
                out[b] = transfer(in[b], steps.get(b), ctx, null);
            }
            boolean changed = true;
            while (changed) {
                changed = false;
                for (int b = 0; b < nb; b++) {
                    Fact newIn = entryFact(cfg, b, allE);
                    for (int p : cfg.predecessors()[b]) {
                        newIn.fresh.or(out[p].fresh);
                        newIn.stale.or(out[p].stale);
                    }
                    Fact newOut = transfer(newIn, steps.get(b), ctx, null);
                    if (!newIn.equals(in[b]) || !newOut.equals(out[b])) {
                        in[b] = newIn;
                        out[b] = newOut;
                        changed = true;
                    }
                }
            }
            BitSet[] atLoad = new BitSet[n];
            int[] eOfLoad = new int[n];
            java.util.Arrays.fill(eOfLoad, -1);
            for (int b = 0; b < nb; b++) {
                transfer(in[b], steps.get(b), ctx, (load, fact) -> {
                    BitSet r = (BitSet) fact.fresh.clone();
                    r.or(fact.stale);
                    atLoad[load.id] = r;
                    eOfLoad[load.id] = eId.get(load.receiver);
                });
            }
            return new FramePools(atLoad, eOfLoad, storeByNode, loadByNode);
        }

        private record Ctx(Object[] receiverById, boolean[] killable, Map<Object, Integer> eId, BitSet allE) {
        }

        /** Every E_w (other-invocation version) is generated at the frame entry. */
        private static Fact entryFact(FrameCfg cfg, int b, BitSet allE) {
            Fact f = new Fact(new BitSet(), new BitSet());
            if (b == cfg.entryBlock()) {
                f.fresh.or(allE);
            }
            return f;
        }

        private static Fact transfer(Fact in, List<Step> blockSteps, Ctx ctx,
                        java.util.function.BiConsumer<PoolAccess, Fact> atLoad) {
            Fact state = in.copy();
            for (Step s : blockSteps) {
                if (s.access != null) {
                    PoolAccess a = s.access;
                    if (!a.store) {
                        if (atLoad != null) {
                            atLoad.accept(a, state);
                        }
                        continue;
                    }
                    // KILL: fresh same-receiver stores (a stale one names an older object) and E_w.
                    if (ctx.killable[a.id]) {
                        for (int i = state.fresh.nextSetBit(0); i >= 0 && i < ctx.receiverById.length; i = state.fresh.nextSetBit(i + 1)) {
                            if (ctx.receiverById[i] == a.receiver && ctx.killable[i]) {
                                state.fresh.clear(i);
                            }
                        }
                        state.fresh.clear(ctx.eId.get(a.receiver));
                    }
                    state.fresh.set(a.id);
                } else if (s.event.kind == PoolEvent.INVOKE) {
                    state.fresh.or(ctx.allE); // another invocation may have run
                } else {
                    Object w = s.event.receiver;
                    Integer e = ctx.eId.get(w);
                    if (e == null) {
                        continue; // a definition of a value no access of this member uses
                    }
                    // Staleness: the fresh stores on w go stale; E_w is re-generated.
                    for (int i = state.fresh.nextSetBit(0); i >= 0 && i < ctx.receiverById.length; i = state.fresh.nextSetBit(i + 1)) {
                        if (ctx.receiverById[i] == w) {
                            state.fresh.clear(i);
                            state.stale.set(i);
                        }
                    }
                    state.fresh.set(e);
                }
            }
            return state;
        }

        /** The pure reaching relation: the dataflow says {@code store} (this invocation's) may reach {@code load}. */
        boolean reaches(PoolAccess store, PoolAccess load) {
            BitSet r = reachingAtLoad[load.id];
            return r != null && r.get(store.id);
        }

        /**
         * The load's reaching set contains E_w for its own receiver w: another invocation of this frame may have written
         * the object last, so every same-frame store may be current at the load.
         */
        boolean otherInvocationReaches(PoolAccess load) {
            BitSet r = reachingAtLoad[load.id];
            int e = eOfLoad[load.id];
            return r == null || e < 0 || r.get(e);
        }

        /** A same-frame (σ, λ) pair connects iff σ reaches λ or E_{recv(λ)} reaches λ. */
        boolean connects(PoolAccess store, PoolAccess load) {
            return reaches(store, load) || otherInvocationReaches(load);
        }

        PoolAccess storeAccess(Object node) {
            return storeByNode.get(node);
        }

        PoolAccess loadAccess(Object node) {
            return loadByNode.get(node);
        }
    }

    /**
     * The per-(table, member) pool view: the frame→FramePools cache plus connected(), the cross-frame merge: same frame
     * → the in-frame dataflow; different frames (or a build-time store with no frame) → always connected. The FrameCfg
     * source is a static hook the engine installs once, before any table exists.
     */
    static final class MemberPools {
        static volatile java.util.function.BiFunction<LocalFlowGraph, Object, FrameCfg> CFG_SOURCE = (f, m) -> new FrameCfg(0, new int[0][], List.of());

        static void setCfgSource(java.util.function.BiFunction<LocalFlowGraph, Object, FrameCfg> src) {
            CFG_SOURCE = src;
        }

        final Object member;
        final Map<LocalFlowGraph, FramePools> byFrame = new ConcurrentHashMap<>();

        MemberPools(Object member) {
            this.member = member;
        }

        FramePools framePools(LocalFlowGraph frame) {
            if (frame == null) {
                return null;
            }
            return byFrame.computeIfAbsent(frame, f -> FramePools.compute(CFG_SOURCE.apply(f, member)));
        }

        /**
         * connected(): the pool-grain predicate waiters filter on. In-frame separation assumes sequential, per-object
         * semantics: a racing store to the same object from another thread between a same-frame store and load is not
         * considered.
         */
        boolean connected(LocalFlowGraph storeFrame, Object storeNode, LocalFlowGraph loadFrame, Object loadNode) {
            if (storeFrame == null || loadFrame == null || storeFrame != loadFrame) {
                return true; // cross-frame (or build-time): always MERGE
            }

            FramePools fp = framePools(storeFrame);
            if (fp == null) {
                return true; // no IR for the frame — merge (sound default)
            }
            PoolAccess s = fp.storeAccess(storeNode);
            PoolAccess l = fp.loadAccess(loadNode);
            if (s == null || l == null) {
                return true; // an access the scan did not see — merge
            }
            return fp.connects(s, l); // the in-frame reaching relation, other-invocation versions included
        }
    }
}
