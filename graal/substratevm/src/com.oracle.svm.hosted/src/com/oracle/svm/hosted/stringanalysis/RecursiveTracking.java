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

import static com.oracle.svm.hosted.stringanalysis.HolderEndRule.soundEndCause;
import static com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.isIdQuery;
import static com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.constantSiteOf;
import static com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.isNamedQuery;
import static com.oracle.svm.hosted.stringanalysis.ThreadLocalModel.isCurrentThreadVmtl;
import static com.oracle.svm.hosted.stringanalysis.ThreadLocalModel.mayBeThreadNode;
import static com.oracle.svm.hosted.stringanalysis.ThreadLocalModel.vmtlIdentity;
import static com.oracle.svm.hosted.stringanalysis.WorldTopRule.parameterEntryRefusal;
import static com.oracle.svm.hosted.stringanalysis.WorldTopRule.returnExitRefusal;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Consumer;
import java.util.function.IntPredicate;

import jdk.graal.compiler.core.common.type.IntegerStamp;
import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.FrameState;
import jdk.graal.compiler.nodes.IndirectCallTargetNode;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PhiNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.UnwindNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.VirtualState;
import jdk.graal.compiler.nodes.calc.ConditionalNode;
import jdk.graal.compiler.nodes.cfg.ControlFlowGraph;
import jdk.graal.compiler.nodes.cfg.HIRBlock;
import jdk.graal.compiler.nodes.extended.BoxNode;
import jdk.graal.compiler.nodes.extended.BytecodeExceptionNode;
import jdk.graal.compiler.nodes.extended.RawLoadNode;
import jdk.graal.compiler.nodes.extended.RawStoreNode;
import jdk.graal.compiler.nodes.extended.UnsafeMemoryLoadNode;
import jdk.graal.compiler.nodes.extended.UnsafeMemoryStoreNode;
import jdk.graal.compiler.nodes.java.AbstractUnsafeCompareAndSwapNode;
import jdk.graal.compiler.nodes.java.AtomicReadAndWriteNode;
import jdk.graal.compiler.nodes.java.DynamicNewArrayNode;
import jdk.graal.compiler.nodes.java.DynamicNewInstanceNode;
import jdk.graal.compiler.nodes.java.ExceptionObjectNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.LoadIndexedNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.NewArrayNode;
import jdk.graal.compiler.nodes.java.NewArrayWithExceptionNode;
import jdk.graal.compiler.nodes.java.NewInstanceWithExceptionNode;
import jdk.graal.compiler.nodes.java.NewInstanceNode;
import jdk.graal.compiler.nodes.java.NewMultiArrayNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.java.StoreIndexedNode;
import jdk.graal.compiler.nodes.spi.LimitedValueProxy;
import jdk.graal.compiler.nodes.virtual.AllocatedObjectNode;
import jdk.graal.compiler.nodes.virtual.CommitAllocationNode;
import jdk.graal.compiler.nodes.virtual.VirtualArrayNode;
import jdk.graal.compiler.nodes.virtual.VirtualInstanceNode;
import jdk.graal.compiler.nodes.virtual.VirtualObjectNode;
import jdk.graal.compiler.replacements.nodes.BasicArrayCopyNode;
import jdk.graal.compiler.replacements.nodes.ObjectClone;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

import com.oracle.graal.pointsto.heap.ImageHeapConstant;
import com.oracle.graal.pointsto.heap.ImageHeapInstance;
import com.oracle.graal.pointsto.heap.ImageHeapObjectArray;
import com.oracle.graal.pointsto.heap.ImageHeapPrimitiveArray;
import com.oracle.graal.pointsto.heap.TypeData;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.svm.hosted.phases.StringAnalysisChildInlining;
import com.oracle.svm.hosted.phases.StringAnalysisChildNoFold;
import com.oracle.svm.hosted.stringanalysis.ClosedFieldEscape.FieldLoadSite;
import com.oracle.svm.hosted.stringanalysis.ClosedFieldEscape.FieldReadIndex;
import com.oracle.svm.hosted.stringanalysis.ClosedFieldEscape.FieldWriteIndex;
import com.oracle.svm.hosted.stringanalysis.ContainerAtoms.ContextElement;
import com.oracle.svm.hosted.stringanalysis.ContainerAtoms.HeapContext;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.EntryList;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.FrameCfg;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Listener;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.LoadEntry;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.PoolAccess;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Sink;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.StoreEntry;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Table;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Waiter;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.CallPath;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.MethodContext;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.EscKind;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.EscRec;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.HolderLog;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.WaitRec;
import com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.IdBirthIndex;
import com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.IdPremise;
import com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.IdQuery;
import com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.IdSite;
import com.oracle.svm.hosted.stringanalysis.ObjectIdentityRule.PendingSlot;
import com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.InlinedIndex;
import com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.NamedPremise;
import com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.NamedQuery;
import com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.NavCensus;
import com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.NavIndex;
import com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.ObjretHook;
import com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.SelfSlotImage;
import com.oracle.svm.hosted.stringanalysis.ObjectReturnRule.TriggerRec;
import com.oracle.svm.hosted.stringanalysis.ThreadLocalModel.InitialValue;
import com.oracle.svm.hosted.stringanalysis.ThreadLocalModel.TlOp;

/**
 * The recursive container-tracking engine: one procedure, identical at every level. Backward tasks deliver atoms into
 * monotone sinks; tables are built by the owner's forward walk over the IR and publish entries to pool-grain waiters
 * woken on every growth; completeness is read only at quiescence. The engine uses LFG vertices where they exist and its
 * own detached identities otherwise (the only LFG mints are the lazy, copy-on-write string-side mints). Equal backward
 * roots share one interned sink; copies/clones continue forward through their desugared store and backward through
 * their desugared load; build-time stores are ordinary stores.
 *
 * <p><b>The receiver-entry invariant</b>: every forward entry of a tracked receiver into
 * an instance frame records {@code T(receiver).entryPaths(frame)}, whether or not the frame's IR reads {@code this}.
 * The owner return depends on it: an OWNER(o) atom leaves a frame only through the entries o recorded there, and an
 * allocation in a frame that never reads {@code this} gets owner-specific atoms too (its owner sink is slot 0 of the
 * entering call). Every forward crossing enters the receiver through {@link #enterReceiver}, the one place that records
 * the entry.
 *
 * <p>Some rules live in their own classes, each a stateless part of this engine that reads and writes the engine's
 * state through its {@code rt} field: {@link HolderEndRule}, {@link ThreadLocalModel}, {@link ObjectReturnRule},
 * {@link ObjectIdentityRule}, {@link ClosedFieldEscape}, {@link ReflectionBridgeCrossings}, {@link WorldTopRule} and
 * {@link ReverseHeapIndex}. The state itself (fields, knobs, locks) stays here.
 */
final class RecursiveTracking {

    // ------------------------------------------------------------------
    // The knobs.
    // ------------------------------------------------------------------
    /** The sink's aggregate load-case engagement count cap. */
    static final int TRACK_DEPTH_CAP = Integer.getInteger("svm.stringanalysis.fwd.rtrack.trackdepth", 16);
    /** The per-(table, member) store fan cap. */
    static final int STORE_FAN_CAP = Integer.getInteger("svm.stringanalysis.fwd.rtrack.storefan", 16);
    /**
     * Sink atom fan cap: a sink that resolves more than this many atoms is refused whole (budget class →
     * RESOURCE_LIMIT; never first-N: the decision is a set size of the sink's own monotone result, so it is
     * order-independent). Knob {@code fwd.rtrack.sinkfan} (default 128; 0 = off).
     */
    static final int SINK_FAN_CAP = Integer.getInteger("svm.stringanalysis.fwd.rtrack.sinkfan", 128);
    /** The backward-exploration bound per sink, measured as |sink.visited| (a set size, never the DFS depth). */
    static final int BACKWARD_BUDGET_DEFAULT = 512;
    static final int BACKWARD_BUDGET = Integer.getInteger("svm.stringanalysis.fwd.reversedepth", BACKWARD_BUDGET_DEFAULT);
    /** The bound on the no-path caller fan, the owner fan and the static fan. */
    static final int ROOT_FAN_CAP = Integer.getInteger("svm.stringanalysis.fwd.rootexitfancap", 32);
    /** The consistent-caller fan of a return without a usable path. */
    static final int RETURN_FAN_CAP = 32;
    /**
     * The per-atom forward-walk budget in positions (exceeding it is a whole-table refusal, WALK_BUDGET). Knob
     * {@code fwd.rtrack.walkbudget}.
     */
    static final int WALK_BUDGET = Integer.getInteger("svm.stringanalysis.fwd.rtrack.walkbudget", 4096);

    static final int CHA_CAP = DispatchResolution.CHA_FANOUT_CAP;
    /** The JDK models ({@link JdkModels}, the tables; {@link JdkModelEngine}, their application at the crossings). */
    final JdkModelEngine models = new JdkModelEngine(this);
    /** The holder-end rule (stateless; its state stays here). */
    final HolderEndRule holderEnd = new HolderEndRule(this);
    /** The thread-local mechanism (stateless; its state stays here). */
    final ThreadLocalModel threadLocal = new ThreadLocalModel(this);
    /** The object-return rule (stateless; its state stays here). */
    final ObjectReturnRule objectReturn = new ObjectReturnRule(this);
    /** Lambda object-identity tracking (stateless; its state stays here). */
    final ObjectIdentityRule objectIdentity = new ObjectIdentityRule(this);
    /** The closed-field escape and the field-held receivers (stateless; their state stays here). */
    final ClosedFieldEscape closedField = new ClosedFieldEscape(this);
    /** The reflection bridge crossings (stateless; their state stays here). */
    final ReflectionBridgeCrossings reflectionCrossings = new ReflectionBridgeCrossings(this);
    /** World-top and caller-less frames (stateless; their state stays here). */
    final WorldTopRule worldTop = new WorldTopRule(this);
    /** The reverse heap index (stateless; its state stays here). */
    final ReverseHeapIndex reverseHeap = new ReverseHeapIndex(this);
    /** The owner resolutions of an allocation in a this-less instance frame (visits, not sites; census). */
    final Counter thislessOwnerResolutions = new Counter();
    /** The monitor model ({@link MonitorPrimitive}): the object slot of a monitor operation is observed. */
    final Counter monitorObservations = new Counter();
    /** Keyed by (target method, frame); formatted only when the census line is printed. */
    final Map<List<Object>, Counter> monitorObservationsBy = new ConcurrentHashMap<>();
    private final Map<ResolvedJavaMethod, Boolean> monitorOpMemo = new ConcurrentHashMap<>();

    /** The monitor model at a resolved target. */
    boolean isMonitorOperation(ResolvedJavaMethod m) {
        if (m == null) {
            return false;
        }
        return monitorOpMemo.computeIfAbsent(m, MonitorPrimitive::isOperation);
    }

    /**
     * The model rules of one resolved target, in order, shared by every crossing: a translated thread-local operation, a
     * JDK model entry, an unlisted method of a closed model class, a monitor operation, or none. A pure function of the
     * target.
     */
    enum TargetRule {
        THREAD_LOCAL,
        MODEL,
        CLOSED,
        MONITOR,
        ORDINARY
    }

    record TargetCheck(TargetRule rule, TlOp tl, JdkModels.Op op, JdkModels.Family closed) {
    }

    private static final TargetCheck ORDINARY_TARGET = new TargetCheck(TargetRule.ORDINARY, TlOp.NONE, null, null);
    private static final TargetCheck MONITOR_TARGET = new TargetCheck(TargetRule.MONITOR, TlOp.NONE, null, null);

    TargetCheck targetCheck(ResolvedJavaMethod t) {
        TlOp tl = threadLocal.tlOp(t);
        if (tl != TlOp.NONE) {
            return new TargetCheck(TargetRule.THREAD_LOCAL, tl, null, null);
        }
        JdkModels.Op op = models.op(t);
        if (op != null) {
            return new TargetCheck(TargetRule.MODEL, TlOp.NONE, op, null);
        }
        JdkModels.Family f = models.closedUnlisted(t);
        if (f != null) {
            return new TargetCheck(TargetRule.CLOSED, TlOp.NONE, null, f);
        }
        return isMonitorOperation(t) ? MONITOR_TARGET : ORDINARY_TARGET;
    }

    final Counter exactRecvNarrowed = new Counter();
    final Counter lazyArgStamps = new Counter();
    final Counter lazyArgStampsNarrowing = new Counter();
    final Counter deadTargetsDropped = new Counter();
    final Map<String, Counter> deadTargetsBy = new ConcurrentHashMap<>();

    /**
     * The dead-target rule, called only for a target without a frame: a dispatch target that the post-fixpoint
     * points-to universe proves never executed ({@code !isImplementationInvoked() && !isReachable()}, the predicate of
     * {@code LfgWalk.isNeverExecutedDirectInvoke}) is not a target: in the closed world the dispatch never lands there,
     * so it contributes nothing and needs no refusal. (The CHA formula keys on instantiation only and keeps such
     * implementations, which would make them MISSING_IR.)
     */
    boolean dropDeadTarget(ResolvedJavaMethod m, String side) {
        if (m instanceof AnalysisMethod am && !am.isImplementationInvoked() && !am.isReachable()) {
            deadTargetsDropped.incrementAndGet();
            bump(deadTargetsBy, side + "/" + am.format("%H.%n(%p)"));
            return true;
        }
        return false;
    }

    /**
     * The owner-decision round budget: when this many rounds have decided something, every remaining pending owner
     * decision takes the MERGED atom (a sound merge at a round boundary, never a refusal). Knob
     * {@code fwd.rtrack.ownerrounds}.
     */
    static final int OWNER_ROUND_BUDGET = Integer.getInteger("svm.stringanalysis.fwd.rtrack.ownerrounds", 32);
    /** The container items counted toward the global guard. */
    private static final long EVALUATION_GUARD = 4L * Integer.getInteger("svm.stringanalysis.fwd.maxevals", 5_000_000);
    /** The single array-element member key (index-insensitive). */
    static final Object ARRAY_ELEMENT = new Object() {
        @Override
        public String toString() {
            return "[]";
        }
    };

    /** The detail-dump switch (print-only, default off). */
    static final boolean DUMP = Boolean.getBoolean("svm.stringanalysis.rtrack.dump");
    /** The dump's focus: comma-separated substrings of a frame/atom name (empty = everything). */
    static final String[] DUMP_FOCUS = System.getProperty("svm.stringanalysis.rtrack.dumpfocus", "").isEmpty() ? new String[0]
                    : System.getProperty("svm.stringanalysis.rtrack.dumpfocus").split(",");

    static boolean focused(String s) {
        if (DUMP_FOCUS.length == 0) {
            return true;
        }
        for (String f : DUMP_FOCUS) {
            if (s.contains(f)) {
                return true;
            }
        }
        return false;
    }

    /** A progress line every 2^18 container items (flag-on only; out of the proof bar). */
    private static final long PROGRESS_MASK = (1L << 18) - 1;

    /** The engine bridge — the pieces ForwardFixpoint already owns. */
    interface Bridge {
        List<DispatchResolution.ResolvedTarget> resolveCrossing(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call,
                        boolean receiverPosition, ForwardFixpoint.Block siteBlock);

        AnalysisMethod methodOf(LocalFlowGraph frame);

        List<ForwardFixpoint.CallerSite> callersOf(LocalFlowGraph frame);

        boolean isWorldTop(LocalFlowGraph frame);

        StructuredGraph decodeIrGraph(AnalysisMethod method);

        AnalysisField resolveField(ResolvedJavaField field);

        AnalysisMethod resolveMethod(ResolvedJavaMethod method);

        ForwardFixpoint.Block siteBlockOf(LocalFlowGraph frame, LocalFlowGraph.LocalVertex site);

        /** {@code widenType(exactType)} as a block (null for a null type). */
        ForwardFixpoint.Block widenedBlockOf(AnalysisType exactType);

        LocalFlowGraph frameOf(AnalysisMethod method);

        /** The heap snapshot's reachable objects (null when unavailable). */
        Map<AnalysisType, Set<ImageHeapConstant>> heapObjects();

        /** The declaring class's initializer was simulated at build time (its statics are snapshot values). */
        boolean classInitSimulated(AnalysisType type);

        /** The simulated build-time value of a static (a published result, never runs a future); null = unknown. */
        JavaConstant simulatedStaticValue(AnalysisField f);

        /** Every method of the universe (the complete caller index's source). */
        Iterable<AnalysisMethod> universeMethods();

        /** The number of frames ({@code frameOf} non-null); -1 = unknown (the read index then fails closed). */
        default long frameCount() {
            return -1;
        }

        /** Every static field of the universe (build-time values are holders too). */
        Iterable<AnalysisField> staticFields();

        /** Every field of the universe (the word-typed statics' pointers). */
        Iterable<AnalysisField> universeFields();

        /**
         * The arg-position receiver stamp of an invoke the LFG never registered (as Phase A computes it,
         * {@code ArgStampResolution.stampOfUnregisteredInvoke}); null = ⊤ (keep the fan).
         */
        Set<AnalysisType> argStampOfUnregistered(Invoke inv);

        /** The analysis type of a JDK class (null = unavailable: the thread-local rules refuse by name). */
        default AnalysisType lookupJavaType(Class<?> c) {
            return null;
        }

        /** The analysis method of an original method, substitutions applied (null = none/unavailable). */
        default AnalysisMethod resolveMethodSubstituted(ResolvedJavaMethod method) {
            return null;
        }

        /** Every registered foreign-call target (null = unavailable: the narrowing is off). */
        default List<AnalysisMethod> foreignCallTargets() {
            return null;
        }

        /**
         * The exact types of the call's final points-to receiver state (the receiver-aware dispatch rule's
         * per-call fact), or null = unavailable, with the reason given to {@code why} (the fallback census).
         */
        default List<AnalysisType> pointsToReceiverTypes(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call, Consumer<String> why) {
            why.accept("noPointsTo");
            return null;
        }

        /**
         * The call's committed CHA fan as the caller index resolved it (memoised per (caller, bci); the same list as
         * {@code resolveCrossing(ctx, call, true, null)}). Two vertices of one caller sharing a bci share one memo entry;
         * the index used that same entry, and a fan only ever adds doubt (a type outside it keeps the site), so no
         * unsound drop.
         */
        default List<DispatchResolution.ResolvedTarget> committedFan(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call) {
            return resolveCrossing(ctx, call, true, null);
        }

        /**
         * Print-only self-check: the callees points-to itself linked at the call's unique invoke flow
         * (null = unavailable). A dropped caller site must never list the frame's method here.
         */
        default java.util.Collection<AnalysisMethod> pointsToCallees(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call) {
            return null;
        }

        /**
         * The premise's source: the analysis invoke sites of {@code m}'s flows, each {@code {declared target,
         * position method, bci, callees}} (an invoke inlined before the analysis sits at its outermost caller's position;
         * {@code callees} = the points-to callees linked at the flow, a {@code Collection<AnalysisMethod>}, null
         * when unavailable); null = the analysis built no flows for {@code m}. An unavailable answer throws (the premise
         * fails closed).
         */
        default List<Object[]> invokeSites(AnalysisMethod m) {
            throw new UnsupportedOperationException("invokeSites unavailable");
        }

        /**
         * The type a Class (hub) constant stands for, or null (not a Class constant). An unavailable lookup
         * throws (the callers fail closed; null never means "unavailable").
         */
        default AnalysisType classConstantType(JavaConstant c) {
            throw new UnsupportedOperationException("classConstantType unavailable");
        }

        /**
         * The analysis type of a JVMCI type if the universe has it (never creates one), or null (not in the
         * universe). An unavailable lookup throws.
         */
        default AnalysisType optionalAnalysisType(jdk.vm.ci.meta.ResolvedJavaType t) {
            throw new UnsupportedOperationException("optionalAnalysisType unavailable");
        }
    }

    // ------------------------------------------------------------------
    // The atom registry.
    // ------------------------------------------------------------------
    static final class RAtomKey {
        final Object site;          // allocation/clone site vertex | ConstantData
        final HeapContext context;
        private final int hash;

        private RAtomKey(Object site, HeapContext context) {
            this.site = site;
            this.context = context;
            this.hash = System.identityHashCode(site) * 31 + context.hashCode();
        }

        @Override
        public boolean equals(Object obj) {
            return obj instanceof RAtomKey other && site == other.site && context.equals(other.context);
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public String toString() {
            return "ratom[" + ContextPolicy.siteKey(site) + "," + context + "]";
        }
    }

    enum AtomKind {
        ALLOCATION,
        CONSTANT,
        /** The one current-thread singleton (no birthplace; its walk starts at every read site). */
        CURRENT_THREAD,
        /**
         * One per creation site of an activated heuristic ({@link StringAtoms}); the same walk, with the string rows.
         */
        STRING
    }

    /** A position of an atom's walk: (frame, node, path, mctx), the walk key plus the invocation context. */
    private static final class WalkKey {
        final LocalFlowGraph frame;
        final Node node;
        final CallPath path;
        final MethodContext mctx;
        final int hash;

        WalkKey(LocalFlowGraph frame, Node node, CallPath path, MethodContext mctx) {
            this.frame = frame;
            this.node = node;
            this.path = path;
            this.mctx = mctx;
            this.hash = ((System.identityHashCode(frame) * 31 + System.identityHashCode(node)) * 31 +
                            (path != null ? path.hashCode() : 0)) * 31 + (mctx != null ? mctx.hashCode() : 0);
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof WalkKey k && hash == k.hash && frame == k.frame && node == k.node && Objects.equals(path, k.path) &&
                            Objects.equals(mctx, k.mctx);
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    final class RAtom {
        final RAtomKey key;
        final Table table;
        final AtomKind kind;
        /** ALLOCATION: the birthplace IR node and its frame + the mint mctx. */
        final LocalFlowGraph birthFrame;
        final ValueNode birthNode;
        final MethodContext mintMctx;
        final RAtomKey ownerKey;     // the owner-context atom (birthReturns' waiter target)
        /** CONSTANT: the representative ImageHeapConstant (snapshot reads). */
        final ImageHeapConstant constant;
        final boolean length0;
        /**
         * The receiver-dispatch block, fixed at mint from the atom key's site alone (null = the full fan: constant,
         * current-thread and TL atoms, and a site without an LFG vertex identity).
         */
        final ForwardFixpoint.Block siteBlock;
        volatile Set<WalkKey> visited = ConcurrentHashMap.newKeySet();
        final AtomicInteger steps = new AtomicInteger();
        /**
         * Every method context this atom was minted under (a merged/truncated key is reached from several contexts). The
         * walk starts at the birthplace under each one: the merged table must be the union (merge soundness); walking only
         * the first minter's context would miss entries.
         */
        final Set<MethodContext> mintMctxs = ConcurrentHashMap.newKeySet();
        /** STRING atoms only (null otherwise): the seed, the recorded usages, the walk census. */
        final StringAtoms.StringSeed seed;
        final Set<TransferFacts.UsageFact> strUsages;
        /**
         * Type-check sites (observation only, never a usage): the {@code checkcast}/{@code instanceof String} site keys
         * whose non-strict {@code InstanceOfNode} this STRING atom's walk reached ({@link TypeCheckSites#observationKey});
         * null for container atoms and at {@code typecheck.ic=0}.
         */
        final Set<String> strTypeChecks;
        /** An escape waiter of this atom delivered at least one load entry to continueAt. */
        volatile boolean wiredAnyLoad;
        final AtomicInteger strEscapes;
        /**
         * True once any heap-escape event of this STRING atom's value was seen ({@link #markStored}: field/array-element,
         * static, commit-materialised holder, container-model, ThreadLocal or VM thread-local store). Monotone, read at
         * emit after the final drain. An admitted accumulator extraction whose atoms never set it is stack-confined
         * ({@code ACCUMULATOR_VIEW_SHARED}). Unlike {@link #strEscapes} it covers every escape route. STRING atoms only.
         */
        volatile boolean strStored;
        /**
         * A container atom had a heap-escape event ({@link #markStored}). Read only for the fresh String[] of an
         * element-source array row ({@link #elementContainerStored}).
         */
        volatile boolean containerStored;
        /** Print-only: the distinct IR nodes of the walk (positions / nodes = the path multiplicity). */
        final Set<NodeId> strNodes;
        /** Silent-end census (print-only, STRING atoms only): where the walk stopped without an effect (capped).
         * Allocated only when the census is on ({@link #SILENT_CENSUS}); at 0 the set stays null (a
         * few KB of child heap per STRING atom saved; every reader is behind the same knob). */
        final Set<String> strSilentEnds;
        /**
         * The escapes, the holder silent ends and the return waits of this atom, the facts
         * {@link HolderEndRule#holderEndRule} reads (null until the first event).
         */
        volatile HolderLog hlog;

        RAtom(RAtomKey key, AtomKind kind, LocalFlowGraph birthFrame, ValueNode birthNode, MethodContext mintMctx,
                        RAtomKey ownerKey, ImageHeapConstant constant, boolean length0) {
            this.mintMctxs.add(mintMctx != null ? mintMctx : MethodContext.UNKNOWN);
            this.key = key;
            this.kind = kind;
            this.birthFrame = birthFrame;
            this.birthNode = birthNode;
            this.mintMctx = mintMctx;
            this.ownerKey = ownerKey;
            this.constant = constant;
            this.length0 = length0;
            this.table = new Table(key, length0);
            this.siteBlock = siteBlockOfKey(key, birthNode);
            this.seed = null;
            this.strUsages = null;
            this.strTypeChecks = null;
            this.strEscapes = null;
            this.strNodes = null;
            this.strSilentEnds = null;
        }

        /** A STRING atom (context EMPTY, the MERGED return rule; the block is σ.block, fixed at mint). */
        RAtom(RAtomKey key, StringAtoms.StringSeed seed, ForwardFixpoint.Block stringBlock) {
            this.mintMctxs.add(MethodContext.UNKNOWN);
            this.key = key;
            this.kind = AtomKind.STRING;
            this.birthFrame = seed.frame;
            this.birthNode = seed.births.isEmpty() ? null : seed.births.get(0);
            this.mintMctx = MethodContext.UNKNOWN;
            this.ownerKey = null;
            this.constant = null;
            this.length0 = false;
            this.table = new Table(key, false);
            this.siteBlock = stringBlock;
            this.seed = seed;
            this.strUsages = ConcurrentHashMap.newKeySet();
            this.strTypeChecks = TypeCheckSites.MODE != 0 ? ConcurrentHashMap.newKeySet() : null;
            this.strEscapes = new AtomicInteger();
            this.strNodes = ConcurrentHashMap.newKeySet();
            this.strSilentEnds = SILENT_CENSUS ? ConcurrentHashMap.newKeySet() : null;
        }
    }

    /** The interned backward root (a sink is a pure function of its root). */
    record SinkRoot(LocalFlowGraph frame, Object node, MethodContext mctx, CallPath path) {
        /** An IR node by identity; a model operand (a value record: a chain or a temp) by value. */
        @Override
        public boolean equals(Object o) {
            return o instanceof SinkRoot r && frame == r.frame && (node == r.node || !(node instanceof Node) && node != null && node.equals(r.node)) && Objects.equals(mctx, r.mctx) &&
                            Objects.equals(path, r.path);
        }

        @Override
        public int hashCode() {
            return ((System.identityHashCode(frame) * 31 + (node instanceof Node || node == null ? System.identityHashCode(node) : node.hashCode())) * 31 + Objects.hashCode(mctx)) * 31 +
                            Objects.hashCode(path);
        }
    }

    /** A store marker for a commit's initial store (the commit, the object, the entry index). */
    record CommitStore(CommitAllocationNode commit, VirtualObjectNode object, int index) {
        @Override
        public String toString() {
            return "CommitStore(" + object + "#" + index + ")";
        }
    }

    /** The desugared-load ValueRef of a copy/clone: (the copy/clone node, the member); src from the node. */
    record DesugaredLoad(ValueNode node, Object member) {
        ValueNode src() {
            if (node instanceof BasicArrayCopyNode acn) {
                return acn.getSource();
            }
            return node instanceof ObjectClone oc ? oc.getObject() : null;
        }
    }

    final Bridge bridge;
    final Map<RAtomKey, RAtom> atoms = new ConcurrentHashMap<>();
    private final ConcurrentHashMap<RAtomKey, RAtomKey> atomIntern = new ConcurrentHashMap<>();
    final Map<AnalysisField, Table> staticTables = new ConcurrentHashMap<>();
    private final Map<SinkRoot, Sink> sinks = new ConcurrentHashMap<>();
    /** (frame, member) → the FIXED-IR dataflow input (shared by all tables). */
    private final Map<List<Object>, FrameCfg> frameCfgCache = new ConcurrentHashMap<>();
    private final Map<LocalFlowGraph, Object[]> frameBlocks = new ConcurrentHashMap<>();
    /** Graphs of frames without an LFG graph instance (decoded once, pinned: node identity). */
    private final Map<AnalysisMethod, StructuredGraph> pinnedGraphs = new ConcurrentHashMap<>();
    /** rtrack-private identities for IR nodes the LFG never materialised (never registered in the LFG). */
    private final Map<NodeId, LocalFlowGraph.LocalVertex> detached = new ConcurrentHashMap<>();

    /**
     * Cost only: the identity key of an IR node for the image-wide {@link #detached} map. {@code Node.hashCode()} is the
     * per-graph id, so nodes of many graphs collide; {@code Node.equals} is identity, so an identity-hashed key is the
     * same key set.
     */
    record NodeId(Node n) {
        @Override
        public boolean equals(Object o) {
            return o instanceof NodeId k && k.n == n;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(n);
        }
    }

    /** Build-time holders: a build-time value's ConstantData → the (holder table, member) that hold it. */
    private final Map<Object, List<Object[]>> buildTimeHolders = new ConcurrentHashMap<>();
    private final ConcurrentLinkedQueue<Runnable> queue = new ConcurrentLinkedQueue<>();
    /**
     * Cost only (a processing order, not a rule): refusal wake-ups ({@link Uncounted}) are drained before any other
     * container item, so the stop rule for refused objects skips their work earlier. Output is order-free (unrefused
     * content = F in every fair schedule; refused status is schedule-independent; refused candidates have their usages
     * suppressed).
     */
    private final ConcurrentLinkedQueue<Runnable> refusalQueue = new ConcurrentLinkedQueue<>();
    long refusalRounds;

    /** Route an item into its queue (refusal wake-ups first). */
    private void push(Runnable item) {
        if (item instanceof Uncounted) {
            refusalQueue.add(item);
        } else {
            queue.add(item);
        }
    }

    private boolean queuesEmpty() {
        return refusalQueue.isEmpty() && queue.isEmpty();
    }

    private void clearQueues() {
        queue.clear();
        refusalQueue.clear();
        queueLen.reset();
    }

    private final List<OwnerResolution> ownerResolutions = new ArrayList<>();
    final ArgStampResolution argStampIndex;
    volatile boolean guardTripped;
    final AtomicLong containerItems = new AtomicLong();
    private final AtomicLong refusalWakeups = new AtomicLong();
    /** The queue length (a counter: ConcurrentLinkedQueue.size() is O(n); the progress line reads it). */
    private final java.util.concurrent.atomic.LongAdder queueLen = new java.util.concurrent.atomic.LongAdder();

    // Census (counters; out of the proof bar).
    final long[] counters = new long[ContextPolicy.CIDX_COUNT];
    final Counter censusCompleteByProof = new Counter();
    final Counter censusWalksScheduled = new Counter();
    final Counter censusStoreEntries = new Counter();
    final Counter censusLoadEntries = new Counter();
    final Counter censusEntryPaths = new Counter();
    final Counter censusWaiters = new Counter();
    final Counter censusDeliveries = new Counter();
    final Counter censusStaticTables = new Counter();
    final Counter censusListeners = new Counter();
    final Counter censusVisited = new Counter();
    final Counter heapSnapshotPending = new Counter();
    final Counter primitiveArrayProofs = new Counter();
    final Map<String, Counter> sinkRootsByKind = new ConcurrentHashMap<>();
    final Map<String, Counter> unclassifiedByClass = new ConcurrentHashMap<>();
    /** Print-only: the R2 uses refused UNSAFE_ACCESS at the walk's fallback, by class. */
    final Map<String, Counter> r2UnsafeByClass = new ConcurrentHashMap<>();
    final Map<String, Counter> unresolvedByClass = new ConcurrentHashMap<>();
    final Map<RTrackRefusal, Counter> refusalsByKind = new ConcurrentHashMap<>();

    /** The JVM-wide deep-push count at construction; the census prints this engine's share. */
    private final long deepPushesAtStart = CallPath.BACKWARD_DEEP_PUSHES.get();

    RecursiveTracking(Bridge bridge, ArgStampResolution argStampIndex) {
        this.bridge = bridge;
        this.argStampIndex = argStampIndex;
        FLAT_UNDELIVERED.clear(); // per analysis run (a hosted JVM may run several)
        TypeCheckSites.NON_OUTERMOST_OBSERVED.clear(); // per analysis run
        ContainerTables.MemberPools.setCfgSource(this::frameCfgOf);
        ContainerTables.DEFER = r -> enqueue(new Uncounted(r));
    }

    private void countRefusal(RTrackRefusal r) {
        refusalsByKind.computeIfAbsent(r, k -> new Counter()).incrementAndGet();
    }

    /**
     * A census counter on a {@link java.util.concurrent.atomic.LongAdder} (no shared cache line under parallel rounds).
     * Census only: nothing decides on these values (decision counters keep their atomics).
     */
    static final class Counter {
        private final java.util.concurrent.atomic.LongAdder a = new java.util.concurrent.atomic.LongAdder();

        void incrementAndGet() {
            a.increment();
        }

        void addAndGet(long d) {
            a.add(d);
        }

        long get() {
            return a.sum();
        }

        @Override
        public String toString() {
            return Long.toString(a.sum());
        }
    }

    static void bump(Map<String, Counter> m, String k) {
        m.computeIfAbsent(k, x -> new Counter()).incrementAndGet();
    }

    // ------------------------------------------------------------------
    // The queue and the drain (quiescence = the container queue empty).
    // ------------------------------------------------------------------
    /**
     * A refusal wake-up. Not counted toward the guard: their number is bounded by |waiters| × |refusal kinds|
     * (exactly-once per pair).
     */
    private record Uncounted(Runnable r) implements Runnable {
        @Override
        public void run() {
            r.run();
        }
    }

    void enqueue(Runnable item) {
        if (!guardTripped) {
            if (inParallelRound) {
                // Inside a parallel container round every item goes to the running thread's output buffer; the
                // round merges the buffers in batch-index order (= the serial FIFO order at item grain).
                ContainerAtoms.MonState ts = ContainerAtoms.threadState();
                if (ts.out != null) {
                    ts.out.add(item);
                    return;
                }
            }
            push(item);
            queueLen.increment();
        }
    }

    boolean hasWork() {
        return !queuesEmpty();
    }

    boolean guardTripped() {
        return guardTripped;
    }

    /**
     * Print-only EVALUATION_GUARD watch: the counted items are schedule-dependent, so a run close to the guard could trip
     * it in one schedule and not another. Returns a warning when this run counted more than half the guard, else null.
     */
    String guardHeadroomWarning() {
        long n = containerItems.get();
        if (n * 2 <= EVALUATION_GUARD) {
            return null;
        }
        return "[sug-fwd-rtrack] WARNING: EVALUATION_GUARD headroom below 2x: containerItems=" + n + " guard=" + EVALUATION_GUARD +
                        " (4 x fwd.maxevals; the count is schedule-dependent at fwd.threads>1)" + (guardTripped ? " TRIPPED" : "");
    }

    /** Phase timers (counters only, no decision reads them): container-drain calls/time, round-boundary time. */
    long drainCalls;
    long drainNs;
    long boundaryCalls;
    long boundaryNs;
    long boundaryReadNs;
    long boundaryResolutions;

    /**
     * Drain to container quiescence. The EVALUATION_GUARD counts all container items of the solve; when it trips, the
     * whole solve is refused globally (every root), never a silent cut ({@link #guardTripped()} is read by the verdict
     * layer).
     */
    void drain() {
        long t0 = System.nanoTime();
        drainCalls++;
        try {
            drainImpl();
        } finally {
            drainNs += System.nanoTime() - t0;
        }
    }

    private void drainImpl() {
        if (parPool != null) {
            drainParallel();
            return;
        }
        drainSerialRounds();
        // Owner decisions only at round boundaries (roundBoundary), never here.
    }

    /**
     * Run one container item and count it toward the EVALUATION_GUARD (refusal wake-ups and tasks of already-refused
     * objects are not counted). Returns true when the guard tripped (the queue is cleared and later enqueues are dropped:
     * a global refusal, never a silent cut).
     */
    private boolean runCounted(Runnable item) {
        ContainerAtoms.MonState ts = ContainerAtoms.threadState();
        long skipped0 = ts.skips;
        item.run();
        if (item instanceof Uncounted) {
            refusalWakeups.incrementAndGet();
            return false;
        }
        if (ts.skips != skipped0) {
            return false; // a task of an already-refused object: no work was done — not counted
        }
        long n = containerItems.incrementAndGet();
        if ((n & PROGRESS_MASK) == 0) {
            System.err.println(progressLine());
        }
        if (n > EVALUATION_GUARD && !guardTripped) {
            synchronized (this) {
                if (!guardTripped) {
                    System.err.println("[sug-fwd-rtrack] EVALUATION GUARD tripped — container queue → global refusal");
                    countRefusal(RTrackRefusal.EVALUATION_GUARD);
                    guardTripped = true;
                }
            }
        }
        if (guardTripped) {
            clearQueues();
            return true;
        }
        return false;
    }

    private void noteSkipped() {
        skippedRefused.incrementAndGet();
        ContainerAtoms.threadState().skips++; // per-thread (the guard's "no work done" test of runCounted)
    }

    // ------------------------------------------------------------------
    // The container queue drained by N threads in rounds (fwd.threads>1, knob fwd.rtrack.parcontainer). A round = every
    // item queued when it starts. Each item's enqueues are filed under the item's batch index; the next batch is their
    // concatenation in batch order (the serial FIFO order at item grain). Nothing mutates the LFG inside a round.
    // ------------------------------------------------------------------
    private volatile java.util.concurrent.ExecutorService parPool;
    private int parThreads;
    long parContainerRounds;
    long parContainerItems;
    long parContainerBatchMax;
    /** {@code fwd.rtrack.parcontainer=0} keeps the driver-serial container drain at fwd.threads>1 (default 1). */
    static final boolean PAR_CONTAINER = Integer.getInteger("svm.stringanalysis.fwd.rtrack.parcontainer", 1) != 0;
    /** Batches smaller than this many items per thread run on the driver alone. */
    static final int PAR_MIN_PER_THREAD = Integer.getInteger("svm.stringanalysis.fwd.rtrack.parminbatch", 2);

    void useParallel(java.util.concurrent.ExecutorService pool, int threads) {
        this.parPool = threads > 1 && PAR_CONTAINER ? pool : null;
        this.parThreads = threads;
    }

    /** True while a parallel container round runs (enqueues go to per-thread buffers). */
    private volatile boolean inParallelRound;

    /**
     * The epoch rule: the serial drain runs the parallel drain's rounds (a batch = every item queued at its start, a
     * refusal-only batch first); {@link ContainerTables#ROUND} advances per batch.
     */
    private void drainSerialRounds() {
        while (true) {
            ConcurrentLinkedQueue<Runnable> src = !refusalQueue.isEmpty() ? refusalQueue : queue;
            if (src == refusalQueue) {
                refusalRounds++;
            }
            List<Runnable> batch = new ArrayList<>();
            Runnable item;
            while ((item = src.poll()) != null) {
                batch.add(item);
            }
            queueLen.add(-batch.size());
            if (batch.isEmpty() || guardTripped) {
                return;
            }
            ContainerTables.ROUND++;
            for (Runnable r : batch) {
                if (runCounted(r)) {
                    return; // the guard tripped
                }
            }
        }
    }

    @SuppressWarnings("unchecked")
    private void drainParallel() {
        java.util.concurrent.ExecutorService pool = parPool;
        while (true) {
            List<Runnable> batch = new ArrayList<>(Math.max(16, queueLen.intValue()));
            Runnable item;
            // A pending refusal wake-up makes this a refusal-only round.
            ConcurrentLinkedQueue<Runnable> src = !refusalQueue.isEmpty() ? refusalQueue : queue;
            if (src == refusalQueue) {
                refusalRounds++;
            }
            while ((item = src.poll()) != null) {
                batch.add(item);
            }
            queueLen.add(-batch.size());
            if (batch.isEmpty() || guardTripped) {
                return;
            }
            parContainerRounds++;
            ContainerTables.ROUND++; // the epoch rule: a refusal of this round is stop-visible from the next one
            parContainerItems += batch.size();
            parContainerBatchMax = Math.max(parContainerBatchMax, batch.size());
            final int n = batch.size();
            if (n < PAR_MIN_PER_THREAD * parThreads) {
                for (Runnable r : batch) {
                    if (runCounted(r)) {
                        return;
                    }
                }
                continue;
            }
            final Runnable[][] outs = new Runnable[n][];
            final java.util.concurrent.atomic.AtomicInteger next = new java.util.concurrent.atomic.AtomicInteger();
            final Throwable[] failure = new Throwable[1];
            final int chunk = Math.max(1, Math.min(64, n / (parThreads * 8)));
            int workers = Math.min(parThreads, (n + chunk - 1) / chunk);
            java.util.concurrent.CountDownLatch done = new java.util.concurrent.CountDownLatch(workers);
            Runnable task = () -> {
                ContainerAtoms.MonState ts = ContainerAtoms.threadState();
                ArrayList<Runnable> out = new ArrayList<>();
                ts.out = out;
                try {
                    outer: while (failure[0] == null && !guardTripped) {
                        int from = next.getAndAdd(chunk);
                        if (from >= n) {
                            break;
                        }
                        int to = Math.min(n, from + chunk);
                        for (int i = from; i < to; i++) {
                            boolean tripped = runCounted(batch.get(i));
                            if (!out.isEmpty()) {
                                outs[i] = out.toArray(new Runnable[0]);
                                out.clear();
                            }
                            if (tripped) {
                                break outer;
                            }
                        }
                    }
                } catch (Throwable t) {
                    synchronized (failure) {
                        if (failure[0] == null) {
                            failure[0] = t;
                        }
                    }
                } finally {
                    ts.out = null;
                    done.countDown();
                }
            };
            inParallelRound = true;
            try {
                for (int w = 0; w < workers - 1; w++) {
                    pool.execute(task);
                }
                task.run(); // the driver claims with the workers
                try {
                    done.await();
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    throw new RuntimeException("container round interrupted", e);
                }
            } finally {
                inParallelRound = false;
            }
            if (failure[0] != null) {
                // A container-item failure fails the solve loudly, never swallowed.
                throw new RuntimeException("[sug-fwd-rtrack] container-round worker failed", failure[0]);
            }
            if (guardTripped) {
                clearQueues();
                return;
            }
            // The canonical merge: the next batch in batch-index order.
            for (int i = 0; i < n; i++) {
                Runnable[] o = outs[i];
                if (o != null) {
                    for (Runnable r : o) {
                        push(r);
                    }
                    queueLen.add(o.length);
                }
            }
        }
    }

    /** The distribution of atom walk sizes (steps = positions counted against WALK_BUDGET). */
    private String stepsHistogram() {
        int[] lim = {1, 4, 16, 64, 256, 1024, 2048, 4096, Integer.MAX_VALUE};
        long[] h = new long[lim.length];
        long sum = 0;
        for (RAtom a : atoms.values()) {
            int st = a.steps.get();
            sum += Math.min(st, WALK_BUDGET + 1);
            for (int i = 0; i < lim.length; i++) {
                if (st <= lim[i]) {
                    h[i]++;
                    break;
                }
            }
        }
        StringBuilder sb = new StringBuilder("steps{sum=").append(sum);
        String[] lab = {"<=1", "<=4", "<=16", "<=64", "<=256", "<=1024", "<=2048", "<=4096", ">4096"};
        for (int i = 0; i < lim.length; i++) {
            sb.append(' ').append(lab[i]).append(':').append(h[i]);
        }
        return sb.append('}').toString();
    }

    final Map<String, Counter> waitersByKind = new ConcurrentHashMap<>();
    final Map<String, Counter> itemKinds = new ConcurrentHashMap<>();

    /** Retained-structure sizes (the memory investigation's ownership census). */
    private String structureSizes() {
        long atomVisited = 0;
        long entryLists = 0;
        long entries = 0;
        for (RAtom a : atoms.values()) {
            Set<WalkKey> v = a.visited;
            atomVisited += v != null ? v.size() : 0;
            entryLists += a.table.stores.size() + a.table.loads.size() + a.table.entryPaths.size();
        }
        long sinkVisited = 0;
        long sinkAtoms = 0;
        int[] lim = {1, 2, 4, 8, 16, 32, 64, 128, 256, 1024, 4096, Integer.MAX_VALUE};
        long[] h = new long[lim.length];
        for (Sink sk : sinks.values()) {
            sinkVisited += sk.visited.size();
            int n = sk.atomCount();
            sinkAtoms += n;
            for (int i = 0; i < lim.length; i++) {
                if (n <= lim[i]) {
                    h[i]++;
                    break;
                }
            }
        }
        StringBuilder fan = new StringBuilder("sinkFan{");
        String[] lab = {"<=1", "<=2", "<=4", "<=8", "<=16", "<=32", "<=64", "<=128", "<=256", "<=1024", "<=4096", ">4096"};
        for (int i = 0; i < lim.length; i++) {
            fan.append(i > 0 ? " " : "").append(lab[i]).append(':').append(h[i]);
        }
        fan.append("} ");
        return fan + "items" + new TreeMap<>(itemKinds) + " sizes{atomVisited=" + atomVisited + " entryLists=" + entryLists + " sinkVisited=" + sinkVisited + " sinkAtoms=" +
                        sinkAtoms + " crossMemo=" + crossMemo.size() + " detached=" + detached.size() + " frameCfg=" +
                        frameCfgCache.size() + " btHolders=" + buildTimeHolders.size() + " waitersByKind=" + new TreeMap<>(waitersByKind) + "}";
    }

    private String progressLine() {
        // Cost: O(1) counters only; the O(atoms + sinks) structureSizes()/stepsHistogram()
        // scans are printed once, in the final census.
        return "[sug-fwd-rtrack-progress] items=" + containerItems.get() + " refusalWakeups=" + refusalWakeups.get() + " skipped=" + skippedRefused.get() + " atoms=" + atoms.size() + " sinks=" + sinks
                        .size() +
                        " visited=" + censusVisited.get() + " listeners=" + censusListeners.get() + " waiters=" + censusWaiters.get() +
                        " stores=" + censusStoreEntries.get() + " loads=" + censusLoadEntries.get() + " queue=" + queueLen.sum() +
                        " heapUsedMB=" +
                        ((Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()) >> 20);
    }

    String census() {
        if (DUMP) {
            dumpTables();
        }
        System.out.println(closedField.closedFieldCensus()); // print-only
        if (SILENT_CENSUS) {
            silentEndCensus(); // print-only
        }
        holderEnd.holderEndCensus(); // print-only
        // Print-only: the walk-stop rules' counters
        System.out.println("[sug-fwd-rtrack-b] typedStops=" + typedStops.get() +
                        " ownerRetFallbacks=" + ownerRetFallbacks.get() + " jmhblackhole=" + StringAtoms.JMH_BLACKHOLE_SINK + " jmhBlackholeSinks=" +
                        jmhBlackholeSinks.get() + " assertionMessageRefusals=" + assertionMessageRefusals.get() + worldTop.callerPtCensus() +
                        foldCensus() + objectIdentity.objidCensus() + objectReturn.objretCensus());
        Sink.Stats st = new Sink.Stats();
        for (Sink s : sinks.values()) {
            st.record(Math.max(s.peakVisited, s.visited.size()), (int) s.trackDepth.get());
        }
        StringBuilder sb = new StringBuilder("[sug-fwd-rtrack]");
        sb.append(" knobs{ctxk=").append(ContextPolicy.CTXK).append(" pathk=").append(ContextPolicy.PATHK)
                        .append(" pathk.bwd=").append(ContextPolicy.PATHK_BACKWARD).append(" sinkfan=").append(SINK_FAN_CAP)
                        .append(" reversedepth=").append(BACKWARD_BUDGET).append(" walkbudget=").append(WALK_BUDGET)
                        .append(" parcontainer=").append(parPool != null ? 1 : 0).append('}');
        sb.append(" parContainer{rounds=").append(parContainerRounds)
                        .append(" items=").append(parContainerItems).append(" batchMax=").append(parContainerBatchMax).append(" refusalRounds=").append(refusalRounds).append('}');
        sb.append(" boundaryStaleReads=").append(boundaryStaleReads.get());
        sb.append(" atoms=").append(atoms.size());
        sb.append(" staticTables=").append(censusStaticTables.get());
        sb.append(" walksScheduled=").append(censusWalksScheduled.get());
        sb.append(" completeByProof=").append(censusCompleteByProof.get());
        sb.append(" stores=").append(censusStoreEntries.get());
        sb.append(" loads=").append(censusLoadEntries.get());
        sb.append(" entryPaths=").append(censusEntryPaths.get());
        sb.append(" waiters=").append(censusWaiters.get());
        sb.append(" deliveries=").append(censusDeliveries.get());
        sb.append(" containerItems=").append(containerItems.get()).append(" evaluationGuard=").append(EVALUATION_GUARD);
        sb.append(' ').append(stepsHistogram());
        sb.append(' ').append(structureSizes());
        sb.append(" refusalWakeups=").append(refusalWakeups.get());
        sb.append(" skippedRefused=").append(skippedRefused.get());
        sb.append(" guardTripped=").append(guardTripped);
        sb.append(" sinks=").append(st.count.get()).append(" listeners=").append(censusListeners.get());
        sb.append(" sinkRoots=").append(new TreeMap<>(sinkRootsByKind));
        sb.append(" sinkVisitedMax=").append(st.maxVisited.get());
        sb.append(" sinkVisitedSum=").append(st.sumVisited.get());
        sb.append(" sinkVisitedAvg=").append(st.count.get() == 0 ? 0 : st.sumVisited.get() / st.count.get());
        sb.append(" sinkVisitedHist=").append(st.histogram());
        sb.append(" trackDepthMax=").append(st.trackDepthMax.get());
        sb.append(" refusals=").append(new TreeMap<>(refusalsByKind));
        sb.append(" counters={");
        for (int i = 0; i < counters.length; i++) {
            if (i > 0) {
                sb.append(' ');
            }
            long v = i == ContextPolicy.CIDX_PATH_TRUNCATED ? CallPath.PATH_TRUNCATED.get() : counters[i];
            sb.append(ContextPolicy.COUNTER_NAMES[i]).append('=').append(v);
        }
        sb.append('}');
        long multi = 0;
        for (RAtom a : atoms.values()) {
            if (a.mintMctxs.size() > 1) {
                multi++;
            }
        }
        sb.append(" irCallers{built=").append(irCallers != null).append(" sites=").append(irCallerSites.get())
                        .append(" irOnlyUsed=").append(irOnlyCallerSites.get()).append(" problems=").append(irCallerProblems.get())
                        .append(" incompleteFrames=").append(incompleteCallers.size()).append(" ms=").append(irCallerBuildMs).append('}');
        sb.append(" staticWriterUnseen=").append(staticWriterUnseen.get());
        sb.append(" mintCtx{multiMctxAtoms=").append(multi).append('}');
        sb.append(" ownerRounds{rounds=").append(ownerRounds).append(" budget=").append(OWNER_ROUND_BUDGET).append(" perRound=").append(roundLog);
        for (int i = 0; i < OD_NAMES.length; i++) {
            sb.append(' ').append(OD_NAMES[i]).append('=').append(ownerDecisions[i]);
        }
        synchronized (ownerResolutions) {
            sb.append(" pendingAtEnd=").append(ownerResolutions.size());
        }
        sb.append('}');
        sb.append(ownerDeferCensus());
        sb.append(" heapSnapshotPending=").append(heapSnapshotPending.get());
        sb.append(" pendingReferenceFree=").append(pendingReferenceFree.get()); // the pending-snapshot rule's reference-free constants
        sb.append(" recordCommit=").append(recordCommitStores.get()); // record-commit translations of a non-null component
        sb.append(" heapIndex{built=").append(holderIndexBuilt).append(" problem=").append(holderIndexProblem)
                        .append(" objects=").append(heapIndexObjects.get()).append(" slots=").append(heapIndexSlots.get())
                        .append(" edges=").append(heapIndexEdges.get()).append(" pendingRead=").append(heapIndexPendingRead.get())
                        .append(" ms=").append(heapIndexBuildMs.get()).append(" constantsNeedingHolders=")
                        .append(constantsNeedingHolders.get()).append(" holdersScheduled=").append(heapHoldersScheduled.get())
                        .append(' ').append(reverseHeap.holderFanHistogram()).append('}');
        sb.append(" primitiveArrayProofs=").append(primitiveArrayProofs.get());
        sb.append(" unclassified=").append(top(unclassifiedByClass));
        sb.append(" unresolved=").append(top(unresolvedByClass));
        sb.append(" noTarget=").append(top(noTargetBy));
        sb.append(" missingIr=").append(top(missingIrBy));
        sb.append(" deadTargetsDropped=").append(deadTargetsDropped.get()).append(" deadTargets=").append(top(deadTargetsBy));
        sb.append(" exactRecvNarrowed=").append(exactRecvNarrowed.get());
        sb.append(" lazyArgStamps=").append(lazyArgStamps.get()).append(" lazyArgStampsNarrowing=").append(lazyArgStampsNarrowing.get());
        sb.append(" e1{abstractRootSkips=").append(DispatchResolution.ABSTRACT_ROOT_SKIPS.sum())
                        .append(" arrayRootQueries=").append(DispatchResolution.ARRAY_ROOT_QUERIES.sum())
                        .append(" abstractSubSkips=").append(DispatchResolution.ABSTRACT_SUB_SKIPS.sum())
                        .append(" dropCrossings=").append(globalDropCrossings.get())
                        .append(" dropTargets=").append(globalDropTargets.get()).append(" provenOnlyKept=").append(globalDropProvenOnly.get())
                        .append(" mintBlockOwnIdentity=").append(mintBlockAllocSite.get()).append(" mintBlockOther=").append(mintBlockNonAllocSite.get())
                        .append(" otherDiffers=").append(mintBlockDiffers.get())
                        .append(" otherHeadMissesBirthType=").append(mintBlockHeadMissesBirthType.get())
                        .append('}');
        sb.append(threadLocal.tlCensus());
        sb.append(worldTop.e2Census());
        sb.append(" e4{r2=").append(top(r2UnsafeByClass)).append('}');
        sb.append(strackCensus());
        Map<String, Counter> monitorBy = new TreeMap<>();
        monitorObservationsBy.forEach((k, c) -> monitorBy.computeIfAbsent(((ResolvedJavaMethod) k.get(0)).format("%H.%n") + "<-" + frameName((LocalFlowGraph) k.get(1)),
                        x -> new Counter()).addAndGet(c.get()));
        sb.append(" monitorprim{obs=").append(monitorObservations.get()).append(" by=").append(top(monitorBy)).append('}');
        sb.append(" thislessowner{resolutions=").append(thislessOwnerResolutions.get()).append('}');
        sb.append(" lambdaparity{roots=").append(StringAnalysisChildInlining.ROOTS.get()).append('}');
        // folds declined in the child's parse
        sb.append(" nofold{getClass=").append(StringAnalysisChildNoFold.DECLINED_GETCLASS.get()).append(" intern=").append(StringAnalysisChildNoFold.DECLINED_INTERN.get()).append('}');
        if (JdkModelEngine.ON) {
            sb.append(models.census()); // printed only when a family is on
        }
        sb.append(" jnifield{fields=").append(!jniFieldsBuilt ? "unread" : jniFields == null ? "unreadable" : String.valueOf(jniFields.size())).append(" refusals=").append(top(new TreeMap<>(
                        jniFieldRefusalsBy))).append('}');
        sb.append(" armlive{piStops=").append(armPiStops.get()).append('}');
        sb.append(recvSinkCensus());
        sb.append(pointsToRecvCensus());
        sb.append(" pathk{forward=").append(ContextPolicy.PATHK).append(" backward=").append(ContextPolicy.PATHK_BACKWARD).append(" deepPushes=")
                        .append(CallPath.BACKWARD_DEEP_PUSHES.get() - deepPushesAtStart).append('}');
        sb.append(reflBridge().census()).append(" crossings=").append(e3Crossings.get()).append(" resultCases=").append(e3ResultCases.get())
                        .append(" chaCap=").append(e3ChaCap.get()).append(" unresolved=").append(e3Unresolved.get()).append(" narrowedFrames=").append(e2Frames.getOrDefault("E3-NARROWED", Set.of())
                                        .size())
                        .append('}');
        return sb.toString();
    }

    static String top(Map<String, Counter> m) {
        List<Map.Entry<String, Counter>> l = new ArrayList<>(m.entrySet());
        l.sort((a, b) -> {
            int c = Long.compare(b.getValue().get(), a.getValue().get());
            return c != 0 ? c : a.getKey().compareTo(b.getKey());
        });
        StringBuilder sb = new StringBuilder("{");
        for (int i = 0; i < l.size() && i < 16; i++) {
            if (i > 0) {
                sb.append(' ');
            }
            sb.append(l.get(i).getKey()).append('=').append(l.get(i).getValue().get());
        }
        return sb.append('}').toString();
    }

    // ------------------------------------------------------------------
    // Graph identity: the LFG's own instance; else one pinned decode.
    // ------------------------------------------------------------------
    StructuredGraph graphOf(LocalFlowGraph frame) {
        if (frame == null) {
            return null;
        }
        if (frame.irGraph instanceof StructuredGraph g) {
            return g;
        }
        AnalysisMethod m = bridge.methodOf(frame);
        return m != null ? pin(m) : null;
    }

    StructuredGraph graphOfMethod(AnalysisMethod m) {
        LocalFlowGraph f = bridge.frameOf(m);
        return f != null ? graphOf(f) : pin(m);
    }

    private StructuredGraph pin(AnalysisMethod m) {
        return pinnedGraphs.computeIfAbsent(m, k -> {
            try {
                return bridge.decodeIrGraph(k);
            } catch (Throwable t) {
                return null;
            }
        });
    }

    private LocalFlowGraph.LocalVertex lfgVertex(LocalFlowGraph frame, Node n) {
        synchronized (frame.vertexLock()) {
            return frame.vertexForNode(n);
        }
    }

    /** The site identity of a birthplace: the LFG vertex if one exists, else an rtrack-private one. */
    Object siteOf(LocalFlowGraph frame, ValueNode n) {
        LocalFlowGraph.LocalVertex v = lfgVertex(frame, n);
        if (v != null) {
            return v;
        }
        return detached.computeIfAbsent(new NodeId(n), k -> {
            LocalFlowGraph.LocalVertex d = new LocalFlowGraph.LocalVertex(frame, -1, LocalFlowGraph.VertexKind.INTERNAL);
            d.label = n instanceof NewInstanceNode || n instanceof NewInstanceWithExceptionNode || n instanceof AllocatedObjectNode ||
                            n instanceof ObjectClone || n instanceof DynamicNewInstanceNode ? "new-instance" : "new-array";
            d.irNode = n;
            d.declaredType = exactTypeOf(n);
            return d;
        });
    }

    static AnalysisType exactTypeOf(ValueNode n) {
        Object t = null;
        if (n instanceof NewInstanceNode nin) {
            t = nin.instanceClass();
        } else if (n instanceof NewInstanceWithExceptionNode niwe) {
            t = niwe.instanceClass();
        } else if (n instanceof NewArrayWithExceptionNode nawe) {
            t = nawe.elementType() != null ? nawe.elementType().getArrayClass() : null;
        } else if (n instanceof NewArrayNode nan) {
            t = nan.elementType() != null ? nan.elementType().getArrayClass() : null;
        } else if (n instanceof AllocatedObjectNode aon) {
            t = aon.getVirtualObject().type();
        }
        return t instanceof AnalysisType at ? at : null;
    }

    /**
     * The INVOKE_CALLSITE identity of an IR invoke: the LFG vertex when it exists and carries its callee (the string
     * layer fills {@code calleeMethod} only for the invokes it models; a null callee would stop every atom with
     * NO_TARGET); otherwise a private descriptor with the callee resolved from the IR (never registered in the LFG).
     *
     * <p>Arg-position stamps for detached calls: Phase A attaches stamps to the LFG's INVOKE_CALLSITE vertices, but the
     * node-keyed registry maps an invoke node to its "invoke-return" vertex, and an invoke the string layer never walked
     * has no vertex, so without a stamp an argument-position crossing would fan over the full CHA cone. Every detached
     * call descriptor gets the stamp Phase A computes for that invoke ({@code ArgStampResolution.stampOfUnregisteredInvoke}),
     * so the ordinary dispatch filters hold at every crossing.
     */
    LocalFlowGraph.LocalVertex callVertexOf(LocalFlowGraph frame, Invoke inv) {
        Node node = inv.asNode();
        LocalFlowGraph.LocalVertex v = lfgVertex(frame, node);
        if (v != null && v.calleeMethod != null) {
            return v;
        }
        return detached.computeIfAbsent(new NodeId(node), k -> {
            LocalFlowGraph.LocalVertex d = new LocalFlowGraph.LocalVertex(frame, -1, LocalFlowGraph.VertexKind.INVOKE_CALLSITE);
            d.irNode = node;
            d.bci = StringAnalysisChildInlining.pointsToBci(inv);
            d.calleeMethod = inv.callTarget() != null ? bridge.resolveMethod(inv.callTarget().targetMethod()) : null;
            // Phase A's arg-position stamp, recomputed for the descriptor (copying from the LFG vertex would give ⊤:
            // the node-keyed registry maps an invoke to its "invoke-return" vertex, not the call-site vertex).
            d.argStamp = bridge.argStampOfUnregistered(inv);
            lazyArgStamps.incrementAndGet();
            if (d.argStamp != null) {
                lazyArgStampsNarrowing.incrementAndGet();
            }
            return d;
        });
    }

    /**
     * The position of the walked value at a crossing (part of the crossing memo's key): RECEIVER = the forward walk at
     * argument 0; ARGUMENT = at another argument; RESULT = the backward invoke-result lookup.
     */
    enum Crossing {
        RECEIVER,
        ARGUMENT,
        RESULT
    }

    private record CrossKey(LocalFlowGraph.LocalVertex call, Crossing position, ForwardFixpoint.Block block) {
        @Override
        public boolean equals(Object o) {
            return o instanceof CrossKey k && call == k.call && position == k.position && Objects.equals(block, k.block);
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(call) * 31 + position.ordinal() + Objects.hashCode(block) * 7;
        }
    }

    private final Map<CrossKey, List<DispatchResolution.ResolvedTarget>> crossMemo = new ConcurrentHashMap<>();

    private List<DispatchResolution.ResolvedTarget> targetsOf(LocalFlowGraph frame, LocalFlowGraph.LocalVertex call,
                    Crossing position, ForwardFixpoint.Block block) {
        boolean receiverPosition = position == Crossing.RECEIVER;
        ForwardFixpoint.Block b = receiverPosition && block != null && !block.isTop() ? block : null;
        return crossMemo.computeIfAbsent(new CrossKey(call, position, b), k -> {
            List<DispatchResolution.ResolvedTarget> t = bridge.resolveCrossing(bridge.methodOf(frame), call, receiverPosition, b);
            if (!receiverPosition && t.size() > 1) {
                t = pointsToReceiverNarrow(frame, call, position, t); // inside the memo: once per call vertex and position
            }
            // The proven override drop, inside the memoised crossing (its key carries
            // the block), never per walk position; a receiver-position crossing with a non-TOP block only.
            return b != null ? globalDrop(t, b) : t;
        });
    }

    /**
     * The ARGUMENT- and RESULT-position source of the receiver-aware dispatch rule
     * ({@code DispatchResolution.receiverDispatchTargets}). The atom is not the call's receiver, so the receiver types
     * come from the analysis child's points-to fixpoint: the exact types of the receiver flow's final state (the string
     * analysis runs in the child's {@code afterAnalysis}). Soundness is child-side: the points-to receiver set
     * over-approximates the exact type of every receiver the program can pass at this call, each dispatches to its type's
     * resolution, and the rule keeps every one of them. The parent runs a separate points-to analysis, so this is not
     * the image's own devirtualisation; the reps are absent from the child's hierarchy exactly as for the committed CHA
     * dispatch, so no rep premise is added. Any doubt keeps the committed fan: no or several matching invoke flows, a
     * direct/static callee, a non-virtual or saturated invoke flow, a missing, disabled, saturated or all-instantiated
     * receiver flow, an empty state, a type that resolves to nothing or outside the fan, or an exception. At RESULT the
     * same facts narrow the backward lookup first; {@link #receiverSinkDispatch} then narrows per context.
     * Deterministic: a pure function of the final points-to state, memoised per (call vertex, position).
     */
    private List<DispatchResolution.ResolvedTarget> pointsToReceiverNarrow(LocalFlowGraph frame, LocalFlowGraph.LocalVertex call, Crossing position,
                    List<DispatchResolution.ResolvedTarget> t) {
        (position == Crossing.RESULT ? ptResultCases : ptArgCases).incrementAndGet();
        String[] reason = {"other"};
        List<AnalysisType> types;
        try {
            types = bridge.pointsToReceiverTypes(bridge.methodOf(frame), call, r -> reason[0] = r);
        } catch (Throwable ex) {
            types = null;
            reason[0] = "exception";
        }
        List<DispatchResolution.ResolvedTarget> n = types != null ? DispatchResolution.receiverDispatchTargets(types, call.calleeMethod, t) : null;
        if (n == null) {
            if (types != null) {
                reason[0] = "noGain";
                for (AnalysisType r : types) {
                    if (DispatchResolution.receiverDispatchTarget(r, call.calleeMethod, t) == null) {
                        reason[0] = "typeOutsideFan";
                        break;
                    }
                }
            }
            ptFallbacks.computeIfAbsent(reason[0], k -> new Counter()).incrementAndGet();
            return t;
        }
        (position == Crossing.RESULT ? ptResultNarrowed : ptArgNarrowed).incrementAndGet();
        ptDropped.addAndGet(t.size() - n.size());
        if (n.size() == 1) {
            ptExact1.incrementAndGet();
        }
        if (t.size() > CHA_CAP && n.size() <= CHA_CAP) {
            ptFromOverCap.incrementAndGet();
        }
        return n;
    }

    /** Census of {@link #pointsToReceiverNarrow}: cases and narrowings per position, dropped targets, fallback reasons. */
    private final Counter ptArgCases = new Counter();
    private final Counter ptResultCases = new Counter();
    private final Counter ptArgNarrowed = new Counter();
    private final Counter ptResultNarrowed = new Counter();
    private final Counter ptExact1 = new Counter();
    private final Counter ptDropped = new Counter();
    private final Counter ptFromOverCap = new Counter();
    private final Map<String, Counter> ptFallbacks = new ConcurrentHashMap<>();

    private String pointsToRecvCensus() {
        StringBuilder sb = new StringBuilder(" recvPointsTo{arg=").append(ptArgNarrowed.get()).append('/').append(ptArgCases.get()).append(" result=")
                        .append(ptResultNarrowed.get()).append('/').append(ptResultCases.get()).append(" exact1=").append(ptExact1.get()).append(" dropped=")
                        .append(ptDropped.get()).append(" fromOverCap=").append(ptFromOverCap.get()).append(" fallbacks=[");
        List<String> keys = new ArrayList<>(ptFallbacks.keySet());
        java.util.Collections.sort(keys);
        for (int i = 0; i < keys.size(); i++) {
            sb.append(i == 0 ? "" : ",").append(keys.get(i)).append('=').append(ptFallbacks.get(keys.get(i)).get());
        }
        return sb.append("]}").toString();
    }

    /** Override-drop census (print-only): crossings the drop narrowed, targets it dropped. */
    private final Counter globalDropCrossings = new Counter();
    private final Counter globalDropTargets = new Counter();
    /** Override-drop census: targets whose drop is proven although no other target of the set overrides them (kept). */
    private final Counter globalDropProvenOnly = new Counter();
    /** Override-drop census: allocation atoms whose mint-fixed block comes from a site vertex that is not an allocation-labelled one. */
    private final Counter mintBlockNonAllocSite = new Counter();
    private final Counter mintBlockAllocSite = new Counter();

    private List<DispatchResolution.ResolvedTarget> globalDrop(List<DispatchResolution.ResolvedTarget> targets, ForwardFixpoint.Block b) {
        if (targets.size() <= 1) {
            return targets;
        }
        List<AnalysisMethod> methods = new ArrayList<>(targets.size());
        for (DispatchResolution.ResolvedTarget t : targets) {
            methods.add(t.method());
        }
        List<AnalysisMethod> kept = DispatchResolution.provenOverrideDrop(methods, b.types);
        for (AnalysisMethod m : kept) {
            if (m != null && !DispatchResolution.overriddenInSet(m, methods) && ForwardFixpoint.overrideDropProven(true, b.types, m)) {
                globalDropProvenOnly.incrementAndGet();
            }
        }
        if (kept.size() == methods.size()) {
            return targets;
        }
        globalDropCrossings.incrementAndGet();
        globalDropTargets.addAndGet(methods.size() - kept.size());
        Set<AnalysisMethod> keep = new java.util.HashSet<>(kept);
        List<DispatchResolution.ResolvedTarget> out = new ArrayList<>(kept.size());
        for (DispatchResolution.ResolvedTarget t : targets) {
            if (keep.contains(t.method())) {
                out.add(t);
            }
        }
        return out;
    }

    // ------------------------------------------------------------------
    // Minting and scheduling (UNBUILT → BUILDING exactly once).
    // ------------------------------------------------------------------
    RAtomKey internKey(Object site, HeapContext ctx) {
        RAtomKey fresh = new RAtomKey(site, ctx);
        RAtomKey interned = atomIntern.putIfAbsent(fresh, fresh);
        return interned != null ? interned : fresh;
    }

    /** Schedule the table's build exactly once. */
    void schedule(RAtom atom) {
        Table t = atom.table;
        if (t.completeByProof) {
            return;
        }
        List<MethodContext> mintSnap;
        ContainerAtoms.enterMon(t.monitor);
        try {
            synchronized (t.monitor) {
                if (t.buildScheduled) {
                    return;
                }
                t.buildScheduled = true;
                // The minting contexts known at the moment the build is
                // scheduled, linearised with mintInto's add-then-check (same monitor), so
                // every context is walked exactly by one of the two sides.
                mintSnap = atom.mintMctxs.isEmpty() ? List.of() : new ArrayList<>(atom.mintMctxs);
            }
        } finally {
            ContainerAtoms.exitMon(t.monitor);
        }
        censusWalksScheduled.incrementAndGet();
        if (threadLocal.atomMayBeThread(atom)) {
            // The singleton's walk, and every Thread-typed atom's, starts at every current-thread read site
            threadLocal.walkFromCurrentThreadReads(atom);
        }
        if (atom.kind == AtomKind.CURRENT_THREAD) {
            return;
        }
        if (atom.kind == AtomKind.CONSTANT) {
            Object csite = constantSiteOf(atom); // a heap-birth query atom's constant
            if (!isNamedQuery(atom)) {
                buildTimeStores(atom); // a heap-birth query tracks the identity only (no contents, no holder records)
            }
            registerBuildTimeEscapes(atom);
            reverseHeap.scheduleHeapHolders(atom);
            if (argStampIndex == null) {
                refuse(t, RTrackRefusal.MISSING_IR);
                return;
            }
            for (AnalysisMethod m : argStampIndex.rtrackConstantMethods(csite)) {
                LocalFlowGraph frame = bridge.frameOf(m);
                StructuredGraph g = graphOfMethod(m);
                if (frame == null || g == null) {
                    refuse(t, RTrackRefusal.MISSING_IR);
                    continue;
                }
                for (Node cn : g.getNodes()) {
                    if (cn instanceof ConstantNode c && isConstantOf(c, csite)) {
                        enqueueWalk(atom, frame, c, null, MethodContext.UNKNOWN);
                    }
                }
            }
            return;
        }
        ValueNode birth = atom.birthNode;
        if (birth instanceof NewMultiArrayNode nma && nma.dimensionCount() > 1) {
            // The inner arrays are allocated implicitly (no IR birthplace of
            // their own): their stores into the outer array are not modelled —
            // a named refusal on the outer table, never a silent gap.
            refuse(t, RTrackRefusal.UNRESOLVED_VALUE);
        }
        if (birth instanceof ObjectClone oc) {
            // clone.m = src.m for every member, seeded lazily per member list,
            // one entry per minting method context.
            LocalFlowGraph bf = atom.birthFrame;
            t.implicitStore = m -> {
                List<StoreEntry> out = new ArrayList<>(1);
                for (MethodContext mm : atom.mintMctxs) {
                    out.add(new StoreEntry(bf, oc, new DesugaredLoad((ValueNode) oc, m), null, mm));
                }
                return out;
            };
        }
        for (MethodContext mm : mintSnap) {
            startBirthWalk(atom, mm); // idempotent per context (walk-position + entry dedup)
        }
    }

    // ------------------------------------------------------------------
    // STRING atoms (StringAtoms).
    // ------------------------------------------------------------------
    /** The adapter to the verdict layer's usage sites (set by {@code ForwardFixpoint.solve}; null only in fixtures that build the engine directly). */
    volatile StringAtoms.Sites strSites;
    /** The STRING atoms in seed order (the emit adapter's population). */
    final Map<StringAtoms.StringSeed, RAtom> stringAtoms = java.util.Collections.synchronizedMap(new java.util.LinkedHashMap<>());

    void strackSites(StringAtoms.Sites sites) {
        this.strSites = sites;
    }

    /**
     * Mint the seed's STRING atom (context EMPTY) and start its walk at every birth invoke, with no path and the UNKNOWN
     * (merged) method context. An unwalkable seed is refused by name (never a silent pass).
     */
    RAtom mintString(StringAtoms.StringSeed seed) {
        RAtomKey key = internKey(seed, HeapContext.EMPTY);
        RAtom atom = atoms.computeIfAbsent(key, k -> new RAtom(k, seed, seed.block != null ? seed.block : strSites != null ? strSites.stringBlock() : null));
        stringAtoms.put(seed, atom);
        atom.table.buildScheduled = true;
        censusWalksScheduled.incrementAndGet();
        if (seed.unwalkable != null) {
            refuse(atom.table, seed.unwalkable);
            return atom;
        }
        for (ValueNode b : seed.births) {
            enqueueWalk(atom, seed.frame, b, null, MethodContext.UNKNOWN);
        }
        return atom;
    }

    /**
     * Mint an ELEM seed's STRING atom and place it as the element of the fresh container its call returns: per birth
     * invoke, the atom escapes (parking on the container's loads of the member and inheriting its refusals) into the
     * member that {@link JdkModelEngine#mintElementSource} mints at the invoke (a stream head's {@code <elem>}, an array's
     * {@code []}). The atom has no walk of its own. The placement does not mark the atom stored: a stream is
     * factory-owned; an array row's pieces are stored iff the fresh array escapes ({@link #elementContainerStored}) or a
     * piece does. A stream row needs the stream model family active (otherwise nothing would load the abstract slot):
     * refused by name otherwise.
     */
    RAtom mintElementString(StringAtoms.StringSeed seed, ElementSources.Kind kind) {
        RAtomKey key = internKey(seed, HeapContext.EMPTY);
        RAtom atom = atoms.computeIfAbsent(key, k -> new RAtom(k, seed, seed.block != null ? seed.block : strSites != null ? strSites.stringBlock() : null));
        stringAtoms.put(seed, atom);
        atom.table.buildScheduled = true;
        censusWalksScheduled.incrementAndGet();
        if (seed.unwalkable != null) {
            refuse(atom.table, seed.unwalkable);
            return atom;
        }
        Object member = models.elementMember(kind);
        if (kind == null || member == null || !models.elementSourceActive(kind)) {
            refuse(atom.table, RTrackRefusal.JDK_MODEL_UNMODELLED);
            return atom;
        }
        for (ValueNode b : seed.births) {
            if (!(b instanceof Invoke inv)) {
                refuse(atom.table, RTrackRefusal.MISSING_IR);
                continue;
            }
            LocalFlowGraph frame = seed.frame;
            Object receiverKey = List.of("elem-source", seed, b);
            internSink("escape", new SinkRoot(frame, receiverKey, MethodContext.UNKNOWN, null), s -> models.mintElementSource(frame, inv, kind, atom, s),
                            escapeListener(atom, frame, b, member, null));
        }
        return atom;
    }

    /** A usage of a STRING atom, unless the arm-liveness filter proves the use dead for σ.block. */
    void strUsage(RAtom atom, LocalFlowGraph frame, Node anchor, ValueNode observed, SugVertex site, UsageRole role, int index) {
        strUsage(atom, frame, anchor, observed, site, role, index, null);
    }

    /** {@code dispatchOwner}: see {@link #accDispatchOwner}. */
    void strUsage(RAtom atom, LocalFlowGraph frame, Node anchor, ValueNode observed, SugVertex site, UsageRole role, int index, String dispatchOwner) {
        if (site == null) {
            return;
        }
        if (strSites.armDead(frame, anchor, observed, atom.siteBlock)) {
            strArmSkips.incrementAndGet();
            silentEnd(atom, frame, anchor, "arm-dead-usage:" + site.getLabel());
            return;
        }
        if ("getClass".equals(site.getMethodName()) && StringAtoms.isClassNameOnlyGetClass(anchor)) {
            // A getClass whose Class is used only for its name is not a usage (class-name observation is
            // out of scope); one place for every heuristic's usage facts
            strClassNameOnly.incrementAndGet();
            bump(strClassNameOnlySites, classNameOnlySiteKey(frame, anchor));
            silentEnd(atom, frame, anchor, "classname-only-getClass");
            return;
        }
        atom.strUsages.add(new TransferFacts.UsageFact(site, role, index, dispatchOwner));
    }

    /** Census (print-only): receiver usages of tracked accumulators recorded with a dispatched owner. */
    final Counter accDispatched = new Counter();
    final Counter accDispatchFailed = new Counter();
    private final Map<List<Object>, String> accDispatchMemo = new ConcurrentHashMap<>();

    /**
     * The receiver usage of a tracked accumulator atom (an ACC seed: one allocation of exact class {@code T}) at a call
     * declared by a wider owner is the method the JVM selects for {@code declared} on {@code T}
     * ({@link AccumulatorWhitelist#dispatchedOwner}). Null for any other atom and for a site that already names a table
     * class.
     */
    String accDispatchOwner(RAtom atom, SugVertex site, jdk.vm.ci.meta.ResolvedJavaMethod declared) {
        if (atom.seed == null || !"ACC".equals(atom.seed.heuristics) || site == null || declared == null ||
                        AccumulatorWhitelist.isTableDeclaring(site.getDeclaringClass()) || atom.seed.vertex.getJavaType() == null) {
            return null;
        }
        jdk.vm.ci.meta.ResolvedJavaType exactType = atom.seed.vertex.getJavaType();
        String siteDeclaring = site.getDeclaringClass();
        String owner = accDispatchMemo.computeIfAbsent(java.util.Arrays.asList(exactType, declared, String.valueOf(siteDeclaring)), k -> {
            try {
                Class<?> exact = com.oracle.graal.pointsto.infrastructure.OriginalClassProvider.getJavaClass(exactType);
                java.lang.reflect.Executable e = com.oracle.graal.pointsto.infrastructure.OriginalMethodProvider.getJavaMethod(declared);
                String o = e instanceof java.lang.reflect.Method m ? AccumulatorWhitelist.dispatchedOwner(siteDeclaring, exact, m) : null;
                return o != null ? o : "";
            } catch (Throwable t) {
                // Conservative (no dispatch = the site's declared owner), but counted and logged
                accDispatchFailed.incrementAndGet();
                System.out.println("[string-analysis] acc.dispatch lookup failed (no dispatch) for " + exactType.toJavaName() + " / " + declared.format("%H.%n(%p)") + ": " + t);
                return "";
            }
        });
        if (owner.isEmpty()) {
            return null;
        }
        accDispatched.incrementAndGet();
        return owner;
    }

    private void strUnclassified(RAtom atom, Node u) {
        bump(strUnclassifiedByClass, u.getClass().getSimpleName());
        refuse(atom.table, RTrackRefusal.UNCLASSIFIED_ACCESS);
    }

    final Counter strArmSkips = new Counter();
    final Counter strTerminals = new Counter();
    final Counter strListContinuations = new Counter();
    final Counter strFieldUsages = new Counter();
    final Counter strClassChecks = new Counter();
    /**
     * Census, print-only: getClass usages dropped as class-name-only ({@link StringAtoms#isClassNameOnlyGetClass}), of
     * both anchor forms (the {@code GetClassNode} form is also counted in {@code classChecks=}).
     */
    final Counter strClassNameOnly = new Counter();
    /** Census, print-only: the class-name-only drops per site ({@code user:|jdk:<Class.method>@<bci>}). */
    final Map<String, Counter> strClassNameOnlySites = new ConcurrentHashMap<>();

    /** The {@link #strClassNameOnlySites} key of a dropped getClass at {@code anchor} in {@code frame}. */
    private String classNameOnlySiteKey(LocalFlowGraph frame, Node anchor) {
        AnalysisMethod m = frame != null ? bridge.methodOf(frame) : null;
        int bci = anchor != null && anchor.getNodeSourcePosition() != null ? anchor.getNodeSourcePosition().getBCI() : -1;
        if (bci < 0 && anchor instanceof Invoke inv) {
            bci = inv.bci();
        }
        if (bci < 0) {
            // a GetClassNode carries no position: the bci of its (first) name call
            bci = StringAtoms.classNameCallBci(StringAtoms.getClassResult(anchor));
        }
        if (m == null) {
            return "unknown:" + frameName(frame) + "@" + bci;
        }
        return (isJdk(m) ? "jdk:" : "user:") + m.format("%H.%n") + "@" + bci;
    }

    /** The census's user/JDK split: by declaring-class prefix (the census label only). */
    private static boolean isJdk(ResolvedJavaMethod m) {
        String c = m.getDeclaringClass().toJavaName(true);
        return c.startsWith("java.") || c.startsWith("javax.") || c.startsWith("jdk.") || c.startsWith("sun.") || c.startsWith("com.sun.") ||
                        c.startsWith("com.oracle.") || c.startsWith("org.graalvm.");
    }

    final Counter strConcatOperands = new Counter();
    final Counter strConcatDesugared = new Counter();
    /** Print-only: container atoms reaching the concat crossing, and the (atom, site) pairs. */
    final Counter containerConcatCrossings = new Counter();
    final Set<String> containerConcatSites = ConcurrentHashMap.newKeySet();
    final Counter strConcatUnrecognised = new Counter();
    final Counter strPhaseAUsages = new Counter();
    /** Print-only census: terminal equals-argument usages, and the ones refused for lack of a Phase-A site. */
    final Counter eqArgTerminals = new Counter();
    final Counter eqArgNoSite = new Counter();
    final Counter cmpArgTerminals = new Counter(); // compareTo arguments: the site-keyed rows TERMINAL and BRIDGE
    final Counter cmpArgBridge = new Counter(); // compareTo mirror: arguments recorded at the bridge's internal site
    final Counter cmpArgNoSite = new Counter(); // compareTo mirror: COMPARETO_ARG_NO_SITE refusals
    final Counter cmpBridgeRecv = new Counter(); // compareTo mirror: receivers recorded at the bridge's internal site
    /**
     * Equals/compareTo arguments at a call with a non-inlined Phase-A vertex that the redirect rule
     * would not mark ({@link EqualsMatrixHeuristic#redirectableArgSite}): refused as NO_SITE instead of TERMINAL
     * (a TERMINAL there would be unsound). Expected 0: a non-zero count flags such a site.
     */
    final Counter argSiteNotRedirectable = new Counter();
    final Counter jmhBlackholeSinks = new Counter(); // StringAtoms.JMH_BLACKHOLE_SINK
    final Counter strContainerConcatOperandArrivals = new Counter();
    final Map<String, Counter> strUnclassifiedByClass = new ConcurrentHashMap<>();

    /**
     * The STRING rows that differ from the container's. Returns true when {@code u} was handled; false falls
     * through to the rows both kinds share (carriers, escapes, returns, observations, the named refusals).
     */
    private boolean stringUsage(RAtom atom, LocalFlowGraph frame, ValueNode n, Node u, CallPath path, MethodContext mctx) {
        StringAtoms.Row row = StringAtoms.rowOf(u, n, u instanceof jdk.graal.compiler.nodes.java.InstanceOfNode ion && ion.type() != null && ion.type().isExact() &&
                        strSites.strictExactInstanceOf(frame, ion));
        switch (row) {
            case FIELD_USAGE -> {
                // a field usage String.value / coder; nothing for hash / hashIsZero; a strict field usage otherwise. STOP.
                LoadFieldNode lfn = (LoadFieldNode) u;
                SugVertex site = strSites.fieldSite(frame, lfn);
                if (site != null) {
                    strFieldUsages.incrementAndGet();
                    strUsage(atom, frame, lfn, n, site, UsageRole.RECEIVER, -1);
                }
                return true;
            }
            case CLASS_CHECK -> {
                strClassChecks.incrementAndGet();
                String label = u instanceof jdk.graal.compiler.nodes.java.InstanceOfNode ? "exact-instanceof" : "getClass";
                strUsage(atom, frame, u, n, strSites.classCheckSite(frame, (ValueNode) u, label), UsageRole.RECEIVER, -1);
                return true;
            }
            case UNCLASSIFIED -> {
                strUnclassified(atom, u); // impossible outside the non-entered terminal bodies
                return true;
            }
            case INVOKE -> {
                invokeUsage(atom, frame, n, (MethodCallTargetNode) u, path, mctx);
                return true;
            }
            default -> {
                if (atom.strTypeChecks != null && u instanceof jdk.graal.compiler.nodes.java.InstanceOfNode ion) {
                    // Type-check site: an observation of the site (not a usage; the shared OBSERVATION row follows)
                    String k = TypeCheckSites.observationKey(ion, n);
                    if (k != null) {
                        atom.strTypeChecks.add(k);
                    }
                }
                if (u instanceof StoreFieldNode sfn && sfn.value() == n && sfn.object() == n && !sfn.field().isStatic()) {
                    // s.f = s (impossible for a String): the escape, and the object role refused
                    escape(atom, frame, sfn, path, mctx);
                    strUnclassified(atom, u);
                    return true;
                }
                if (u instanceof StoreIndexedNode sin && sin.value() == n && sin.array() == n) {
                    escape(atom, frame, sin, path, mctx);
                    strUnclassified(atom, u);
                    return true;
                }
                return false;
            }
        }
    }

    /** Print-only: the string atoms' census line (side-effect free; the per-seed lines are {@link #printStrackSeeds()}). */
    private String strackCensus() {
        List<RAtom> sa = stringAtomsSnapshot();
        long steps = 0;
        long maxSteps = 0;
        long nodes = 0;
        int refusedN = 0;
        int budget = 0;
        int wired = 0;
        long usages = 0;
        long escapesN = 0;
        Map<RTrackRefusal, Integer> byName = new java.util.EnumMap<>(RTrackRefusal.class);
        int[] lim = {16, 64, 256, 1024, 2048, 4096, Integer.MAX_VALUE};
        long[] h = new long[lim.length];
        for (RAtom a : sa) {
            int st = Math.min(a.steps.get(), WALK_BUDGET + 1);
            steps += st;
            maxSteps = Math.max(maxSteps, st);
            nodes += a.strNodes.size();
            for (int i = 0; i < lim.length; i++) {
                if (st <= lim[i]) {
                    h[i]++;
                    break;
                }
            }
            List<RTrackRefusal> rs = a.table.refusalsSnapshot();
            if (!rs.isEmpty()) {
                refusedN++;
            }
            if (rs.contains(RTrackRefusal.WALK_BUDGET)) {
                budget++;
            }
            for (RTrackRefusal r : rs) {
                byName.merge(r, 1, Integer::sum);
            }
            if (a.wiredAnyLoad) {
                wired++;
            }
            usages += a.strUsages.size();
            escapesN += a.strEscapes.get();
        }
        long[] unreadable = strSites != null ? strSites.concatUnreadable() : new long[]{0, 0, 0, 0};
        StringBuilder sb = new StringBuilder(" strack{seeds=").append(sa.size()).append(" refused=").append(refusedN).append(" walkBudget=").append(budget)
                        .append(" positions=").append(steps).append(" maxPositions=").append(maxSteps).append(" distinctNodes=").append(nodes)
                        .append(" multiplicity=").append(nodes == 0 ? "0" : String.format("%.2f", (double) steps / nodes)).append(" hist{");
        String[] lab = {"<=16", "<=64", "<=256", "<=1024", "<=2048", "<=4096", ">4096"};
        for (int i = 0; i < lim.length; i++) {
            sb.append(i == 0 ? "" : " ").append(lab[i]).append(':').append(h[i]);
        }
        sb.append("} refusalsByName=").append(byName).append(" wired=").append(wired).append(" usages=").append(usages).append(" escapes=").append(escapesN)
                        .append(" terminals=").append(strTerminals.get()).append(" listContinuations=").append(strListContinuations.get()).append(" flatHandOffEntries=").append(flatHandOffEntries
                                        .get()).append(" flatHandOffUndelivered=").append(flatHandOffUndelivered.get())
                        .append(" fieldUsages=").append(strFieldUsages.get()).append(" classChecks=").append(strClassChecks.get()).append(" classNameOnly=").append(strClassNameOnly.get()).append(
                                        " classNameOnlySites=").append(top(strClassNameOnlySites))
                        .append(" phaseAUsages=").append(strPhaseAUsages.get()).append(" accDispatched=").append(accDispatched.get()).append(" accDispatchFailed=").append(accDispatchFailed.get())
                        .append(" eqArgTerminals=").append(eqArgTerminals.get())
                        .append(" eqArgNoSite=").append(eqArgNoSite.get()).append(" cmpArgTerminals=").append(cmpArgTerminals.get()).append(" cmpArgBridge=").append(cmpArgBridge.get()).append(
                                        " cmpArgNoSite=").append(cmpArgNoSite.get()).append(" cmpBridgeRecv=").append(cmpBridgeRecv.get()).append(" argSiteNotRedir=").append(argSiteNotRedirectable
                                                        .get()).append(" jmhBlackholeSinks=").append(jmhBlackholeSinks.get()).append(" armSkips=").append(strArmSkips.get())
                        .append(" concatOperands=").append(strConcatOperands.get()).append(" concatDesugared=").append(strConcatDesugared.get())
                        .append(" concatUnrecognised=").append(strConcatUnrecognised.get()).append(" concatReadFailures=").append(unreadable[0])
                        .append(" concatUnreadableRefused=").append(unreadable[1]).append(" concatNonIndyOpcode=").append(unreadable[2])
                        .append(" concatNonIndyRefused=").append(unreadable[3]).append(" containerConcatOperandArrivals=")
                        .append(strContainerConcatOperandArrivals.get()).append(" unclassified=").append(top(strUnclassifiedByClass))
                        .append(" containerConcatCrossings=").append(containerConcatCrossings.get()).append(" containerConcatSites=").append(containerConcatSites.size())
                        .append(" containerConcat=1")
                        .append(" typeSwitchSelectors=").append(strTypeSwitchSelectors.get()).append(" typeSwitchSites=").append(StringAtoms.typeSwitchCensus())
                        .append(" rounds=").append(ContainerTables.ROUND).append(" sameRoundStopTests=").append(ContainerTables.SAME_ROUND_STOP_TESTS.sum()).append('}');
        return sb.toString();
    }

    private List<RAtom> stringAtomsSnapshot() {
        synchronized (stringAtoms) {
            return new ArrayList<>(stringAtoms.values());
        }
    }

    /** Print-only: one sorted {@code [strack-seed]} line per seed. */
    void printStrackSeeds() {
        List<String> lines = new ArrayList<>();
        for (RAtom a : stringAtomsSnapshot()) {
            int st = Math.min(a.steps.get(), WALK_BUDGET + 1);
            lines.add("[strack-seed] " + a.seed.vertex.getSourceLocation() + " heur=" + a.seed.heuristics + " births=" + a.seed.births.size() + " steps=" + st +
                            " nodes=" + a.strNodes.size() + " usages=" + a.strUsages.size() + " escapes=" + a.strEscapes.get() + " wired=" + a.wiredAnyLoad +
                            " refusals=" + a.table.refusalsSnapshot() + " stored=" + a.strStored); // the confinement flag
        }
        for (String cs : new ArrayList<>(containerConcatSites)) {
            lines.add("[strack-cconcat] " + cs);
        }
        java.util.Collections.sort(lines);
        for (String l : lines) {
            System.err.println(l);
        }
    }

    /** The walk from the birthplace under one minting method context (once per context). */
    private void startBirthWalk(RAtom atom, MethodContext mctx) {
        if (models.freshBirth(atom, mctx)) {
            return; // a JDK model's fresh object (its initial stores, its walk from the call's result)
        }
        ValueNode birth = atom.birthNode;
        if (birth instanceof AllocatedObjectNode aon) {
            commitInitialStores(atom, aon, mctx);
        }
        if (birth instanceof ObjectClone && atom.table.implicitStore != null) {
            for (Map.Entry<Object, EntryList<StoreEntry>> e : new ArrayList<>(atom.table.stores.entrySet())) {
                for (StoreEntry se : atom.table.implicitStore.apply(e.getKey())) {
                    e.getValue().append(se, se.dedupKey(), se.nodeKey());
                }
            }
        }
        enqueueWalk(atom, atom.birthFrame, birth, null, mctx);
    }

    private static boolean isConstantOf(ConstantNode cn, Object constantData) {
        return cn.getValue() instanceof ImageHeapConstant ihc && ihc.getConstantData() == constantData;
    }

    // ------------------------------------------------------------------
    // The forward walk: WalkTask over the IR.
    // ------------------------------------------------------------------
    /**
     * A walk position is deduplicated (and counted against WALK_BUDGET) when it is enqueued (the same set as at execution
     * time, so the queue never holds a duplicate position).
     */
    void enqueueWalk(RAtom atom, LocalFlowGraph frame, ValueNode n, CallPath path, MethodContext mctx) {
        if (frame == null || n == null) {
            refuse(atom.table, RTrackRefusal.MISSING_IR);
            return;
        }
        if (atom.table.completeByProof) {
            return;
        }
        if (isRefusedReleasing(atom)) {
            noteSkipped();
            return;
        }
        Set<WalkKey> v = atom.visited;
        if (v == null || !v.add(new WalkKey(frame, n, path, mctx))) {
            return;
        }
        if (atom.steps.incrementAndGet() > WALK_BUDGET) {
            refuse(atom.table, RTrackRefusal.WALK_BUDGET);
            return;
        }
        enqueue(() -> walk(atom, frame, n, path, mctx));
    }

    final Counter skippedRefused = new Counter();

    /** Refused: no position is ever walked again — release the visited set. */
    private boolean isRefusedReleasing(RAtom atom) {
        if (atom.table.stopVisible()) {
            atom.visited = null;
            return true;
        }
        return false;
    }

    void walk(RAtom atom, LocalFlowGraph frame, ValueNode n, CallPath path, MethodContext mctx) {
        if (isRefusedReleasing(atom)) {
            noteSkipped();
            return;
        }
        if (DUMP) {
            walkPos.set(atom.key + " " + frameName(frame) + " " + n + " path=" + path);
            if (DUMP_FOCUS.length > 0 && focused(String.valueOf(atom.key))) {
                // DUMP with a focus only: the focused atom's walk positions, in order (printed as WALK lines)
                dumpWalkLog.computeIfAbsent(atom.key, k -> java.util.Collections.synchronizedList(new ArrayList<>()))
                                .add(cap(frameName(frame) + " " + n + " " + describeNode(n) + " path=" + path + " mctx=" + mctx));
            }
        }
        if (atom.kind == AtomKind.STRING) {
            atom.strNodes.add(new NodeId(n)); // print-only: the path multiplicity's denominator
        }
        List<Node> usages = new ArrayList<>();
        n.usages().forEach(usages::add);
        for (Node u : usages) {
            classifyUsage(atom, frame, n, u, path, mctx);
        }
        if (atom.kind != AtomKind.STRING || SILENT_CENSUS) { // holder-end rule: the holders' quiet nodes too
            String quiet = silentUsesLabel(n, usages);
            if (quiet != null) {
                silentEnd(atom, frame, n, quiet);
            }
        }
    }

    /**
     * The silent-end census (knob {@code fwd.rtrack.silentcensus}, default 1; print-only). A walk that ends with no usage,
     * no refusal and no terminal admits, which is sound only if every such end is a real "the value is dropped" end and
     * not an engine drop. Each STRING atom records the positions where its walk stopped without an effect (a node whose
     * IR usages are only frame states or observations, or none; an argument the callee never reads; a dead target; a Pi
     * or usage in a dead arm); {@link #silentEndCensus} prints them per quiet atom.
     */
    static final boolean SILENT_CENSUS = Integer.getInteger("svm.stringanalysis.fwd.rtrack.silentcensus", 1) != 0;
    static final int SILENT_ENDS_CAP = 16;

    /** The label of a node whose every usage is effect-free for the walk ({@code null}: some usage has an effect). */
    static String silentUsesLabel(ValueNode n, List<Node> usages) {
        if (usages.isEmpty()) {
            return "no-usages";
        }
        java.util.TreeSet<String> kinds = new java.util.TreeSet<>();
        for (Node u : usages) {
            if (u instanceof VirtualState || u instanceof FrameState) {
                kinds.add("state");
            } else if (u instanceof BytecodeExceptionNode ben && !assertionMessageUse(ben, n)) {
                kinds.add("obs:BytecodeException/" + ben.getExceptionKind());
            } else if (!(u instanceof BytecodeExceptionNode) && OBSERVATIONS.contains(u.getClass().getSimpleName())) {
                kinds.add("obs:" + u.getClass().getSimpleName());
            } else {
                return null;
            }
        }
        return String.join("+", kinds);
    }

    void silentEnd(RAtom atom, LocalFlowGraph frame, Node n, String what) {
        if (atom.kind != AtomKind.STRING) {
            holderSilentEnd(atom, frame, n, what); // holder-end rule: every other atom's silent ends, with their cause
            return;
        }
        if (!SILENT_CENSUS || atom.strSilentEnds.size() >= SILENT_ENDS_CAP) {
            return;
        }
        atom.strSilentEnds.add(silentLabel(frame, n, what));
    }

    private String silentLabel(LocalFlowGraph frame, Node n, String what) {
        int bci = n != null && n.getNodeSourcePosition() != null ? n.getNodeSourcePosition().getBCI() : -1;
        return what + " @ " + frameName(frame) + "@" + bci + (n != null ? " " + n.getClass().getSimpleName() : "");
    }

    /** A non-STRING atom's silent end (its cause counted; an unexplained one recorded for the holder-end rule). */
    private void holderSilentEnd(RAtom atom, LocalFlowGraph frame, Node n, String what) {
        HolderLog h = holderEnd.hlog(atom);
        String cause = silentCause(what);
        h.endsByCause.computeIfAbsent(cause, k -> new AtomicInteger()).incrementAndGet();
        boolean sound = soundEndCause(cause);
        if (!sound) {
            h.unexplainedN.incrementAndGet();
        }
        Set<String> into = sound ? h.ends : h.unexplained;
        if (into.size() < SILENT_ENDS_CAP) {
            into.add(silentLabel(frame, n, what));
        }
    }

    /** The cause of a silent-end label (its first token, up to ':' or ' '). */
    static String silentCause(String label) {
        int i = 0;
        while (i < label.length() && label.charAt(i) != ':' && label.charAt(i) != ' ') {
            i++;
        }
        return label.substring(0, i);
    }

    /** The {@code [sug-fwd-silent-end]} lines and their census (see {@link #SILENT_CENSUS}). */
    private void silentEndCensus() {
        List<String> lines = new ArrayList<>();
        TreeMap<String, Integer> byCause = new TreeMap<>();
        int quiet = 0;
        for (RAtom a : atoms.values()) {
            if (a.kind != AtomKind.STRING || !a.strUsages.isEmpty() || a.table.refused() || a.wiredAnyLoad) {
                continue;
            }
            quiet++;
            List<String> ends = new ArrayList<>(a.strSilentEnds);
            java.util.Collections.sort(ends);
            java.util.TreeSet<String> causes = new java.util.TreeSet<>();
            for (String e : ends) {
                causes.add(silentCause(e));
            }
            if (a.strEscapes.get() > 0) {
                causes.add("escape-no-load");
            }
            if (causes.isEmpty()) {
                causes.add("no-recorded-end");
            }
            for (String c : causes) {
                byCause.merge(c, 1, Integer::sum);
            }
            lines.add("[sug-fwd-silent-end] " + a.key + " steps=" + a.steps.get() + " nodes=" + a.strNodes.size() + " escapes=" + a.strEscapes.get() +
                            " causes=" + causes + " ends=" + ends + (ends.size() >= SILENT_ENDS_CAP ? "(capped)" : ""));
        }
        java.util.Collections.sort(lines);
        for (String l : lines) {
            System.out.println(l);
        }
        System.out.println("[sug-fwd-silent-end] census atoms=" + quiet + " byCause=" + byCause);
    }

    // ------------------------------------------------------------------
    // The holder-end rule's state (the rule: HolderEndRule).
    // ------------------------------------------------------------------

    /** The rule's refusals (print-only: the census lists them; they are no longer quiet at census time). */
    final Set<String> holderEndRefused = ConcurrentHashMap.newKeySet();

    /**
     * The {@code AssertionError(Object)} case: SVM's {@code ImplicitAssertionsPhase} replaces {@code new AssertionError(o)}
     * + its constructor call by one {@code BytecodeExceptionNode(ASSERTION_ERROR_OBJECT, o)}, which at run time calls
     * {@code ImplicitExceptions.createAssertionErrorObject(o)} = {@code new AssertionError(o)}: {@code o} becomes the
     * detail message ({@code String.valueOf(o)}). So for this kind the argument is exception flow, not an observation,
     * and is refused by name like a thrown {@code new IllegalStateException(s)}. Every other kind's arguments are ints or
     * are read only through {@code getClass()} (CLASS_CAST, ARRAY_STORE): observations. Pure; pinned by JUnit.
     */
    static boolean assertionMessageUse(BytecodeExceptionNode ben, Node n) {
        return ben.getExceptionKind() == BytecodeExceptionNode.BytecodeExceptionKind.ASSERTION_ERROR_OBJECT && ben.getArguments().contains(n);
    }

    /** A STRING atom seeded at a String literal ({@link StringAtoms#SB_LITERAL_SEED}). */
    static boolean isLiteralAtom(RAtom atom) {
        return atom.kind == AtomKind.STRING && atom.seed != null && atom.seed.vertex.getNodeType() == SugNodeType.STRING_LITERAL;
    }

    /** The IR nodes that observe an object's identity (pure; the monitor op slot is in invokeUsage). */
    static boolean identityObservation(Node u) {
        String c = u.getClass().getSimpleName();
        return c.equals("ObjectEqualsNode") || c.equals("PointerEqualsNode") || c.equals("IdentityHashCodeNode") || c.equals("MonitorEnterNode") ||
                        c.equals("MonitorExitNode") || c.equals("RawMonitorEnterNode") || c.equals("MonitorIdNode");
    }

    /** Census: {@code AssertionError(Object)} messages refused ({@link #assertionMessageUse}). */
    final Counter assertionMessageRefusals = new Counter();

    /** DUMP with a focus only: the walk positions of each focused atom. */
    private final Map<RAtomKey, List<String>> dumpWalkLog = new ConcurrentHashMap<>();

    /** DUMP only: where each refused table got its first refusal (the walk position or the source). */
    private final Map<Table, String> refusalOrigin = new ConcurrentHashMap<>();
    /**
     * The DUMP's provenance cursors are per thread, so at fwd.threads>1 a refusal is never labelled with another worker's
     * position. Print-only.
     */
    private final ThreadLocal<String> walkPos = ThreadLocal.withInitial(() -> "");

    void refuse(Table t, RTrackRefusal r) {
        boolean first = DUMP && !t.refused();
        if (t.refuse(r)) {
            countRefusal(r);
            if (DUMP) {
                recordProv(t, r, "W " + walkPos.get());
            }
            if (first) {
                refusalOrigin.putIfAbsent(t, cap(r + "@" + walkPos.get()));
            }
        }
    }

    void refuse(Sink sink, RTrackRefusal r) {
        if (DUMP && !sink.refused()) {
            sinkRefusalOrigin.putIfAbsent(sink, cap(r + "@" + walkPos.get()));
        }
        if (sink.refuse(r)) {
            countRefusal(r);
            if (DUMP) {
                recordProv(sink, r, "B " + bwPos.get());
            }
        }
    }

    // DUMP only (print-only): the first-arrival provenance of every
    // (table | sink, refusal) pair: the source object it was inherited from (and along which
    // list kind), or the minting position (walk / backward). Printed as chains by dumpTables.
    private record Prov(Object src, String via, String site) {
    }

    private final Map<Object, Map<RTrackRefusal, Prov>> prov = java.util.Collections.synchronizedMap(new IdentityHashMap<>());
    private final ThreadLocal<Object> inhSrc = new ThreadLocal<>();
    private final ThreadLocal<String> inhVia = new ThreadLocal<>();
    private final ThreadLocal<String> bwPos = ThreadLocal.withInitial(() -> "");

    private void recordProv(Object target, RTrackRefusal r, String directSite) {
        Object s = inhSrc.get();
        Map<RTrackRefusal, Prov> m;
        synchronized (prov) {
            m = prov.computeIfAbsent(target, k -> new java.util.EnumMap<>(RTrackRefusal.class));
        }
        synchronized (m) {
            // The labels are capped (print-only; bounds the DUMP's heap at lifted budgets)
            m.putIfAbsent(r, new Prov(s, s != null ? cap(inhVia.get()) : null, s != null ? null : cap(directSite)));
        }
    }

    static String cap(String s) {
        return s == null || s.length() <= 700 ? s : s.substring(0, 700) + "…";
    }

    /** Run {@code body} with the inheritance source set (DUMP only). */
    private void inheriting(Object src, String via, Runnable body) {
        Object ps = inhSrc.get();
        String pv = inhVia.get();
        inhSrc.set(src);
        inhVia.set(via);
        try {
            body.run();
        } finally {
            inhSrc.set(ps);
            inhVia.set(pv);
        }
    }

    private String provLabel(Object o) {
        if (o instanceof Table t) {
            return "T " + t.owner + (t.owner instanceof RAtomKey k && atoms.get(k) != null ? " steps=" + atoms.get(k).steps.get() : "");
        }
        if (o instanceof Sink s) {
            return "S " + describeRoot(s.rootKey) + " atoms=" + s.atomCount();
        }
        return String.valueOf(o);
    }

    String provChain(Object o, RTrackRefusal r) {
        StringBuilder b = new StringBuilder();
        Set<Object> seen = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        for (int hop = 0; o != null && hop < 80; hop++) {
            if (!seen.add(o)) {
                b.append(" <CYCLE>");
                break;
            }
            b.append(hop == 0 ? "" : " <-").append(" [").append(provLabel(o)).append("]");
            Map<RTrackRefusal, Prov> m = prov.get(o);
            Prov p;
            if (m == null) {
                p = null;
            } else {
                synchronized (m) {
                    p = m.get(r);
                }
            }
            if (p == null) {
                b.append(" <no-prov>");
                break;
            }
            if (p.src() == null) {
                b.append(" MINT@").append(p.site());
                break;
            }
            b.append(" via ").append(p.via());
            o = p.src();
        }
        return b.toString();
    }

    /** DUMP only: where each refused sink got its first refusal. */
    private final Map<Sink, String> sinkRefusalOrigin = new ConcurrentHashMap<>();

    /** Print-only, DUMP only: a waiter/listener key as a short readable label. */
    private String dumpKey(Object key) {
        if (key instanceof List<?> kl) {
            StringBuilder b = new StringBuilder("[");
            for (int i = 0; i < kl.size(); i++) {
                Object o = kl.get(i);
                b.append(i == 0 ? "" : ", ");
                if (o instanceof LocalFlowGraph f) {
                    b.append(frameName(f));
                } else if (o instanceof StoreFieldNode || o instanceof LoadFieldNode) {
                    b.append(o).append(' ').append(describeNode(o));
                } else if (o instanceof AnalysisField af) {
                    b.append(memberName(af));
                } else {
                    String t = String.valueOf(o);
                    b.append(t.length() > 240 ? t.substring(0, 240) + "…" : t);
                }
            }
            return b.append(']').toString();
        }
        return String.valueOf(key);
    }

    /**
     * The pure observations of the reference: they neither move nor observe the object's members. An explicit list of
     * exact node classes, never a package/suffix pattern (a prefix match would let value-carrying nodes such as
     * {@code ConditionalNode} and {@code FixedValueAnchorNode} through as "observations": a silent cut).
     *
     * <p>The observation list also matches subclasses, so SVM's SubstrateIdentityHashCodeNode, a subclass of the listed
     * IdentityHashCodeNode (a pure observation of the reference: the header hash, no member), does not fall through to
     * UNCLASSIFIED_ACCESS.
     */
    private static final Set<String> OBSERVATIONS = Set.of(
                    "IsNullNode", "InstanceOfNode", "InstanceOfDynamicNode", "ObjectEqualsNode", "PointerEqualsNode",
                    "ArrayLengthNode", "MonitorEnterNode", "MonitorExitNode", "RawMonitorEnterNode", "MonitorIdNode",
                    "LoadHubNode", "LoadHubOrNullNode", "GetClassNode", "IdentityHashCodeNode", "ObjectIsArrayNode",
                    "BytecodeExceptionNode", "ValueAnchorNode", "ReachabilityFenceNode", "FinalFieldBarrierNode",
                    "ClassIsAssignableFromNode", "BlackholeNode",
                    // UnboxNode reads a box's primitive value
                    // (no reference member); EnsureClassInitializedNode observes a class's init state
                    "UnboxNode", "EnsureClassInitializedNode");

    /** {@code u} observes {@code n}'s class object (or clones it). */
    static boolean classEscape(ValueNode n, Node u) {
        if (u instanceof ObjectClone oc) {
            return oc.getObject() == n;
        }
        return classEscapeKind(u.getClass().getSimpleName());
    }

    /** The node kinds that read an object's Class (hub), by exact class name as the {@link #OBSERVATIONS} list. */
    static boolean classEscapeKind(String nodeClass) {
        return nodeClass.equals("GetClassNode") || nodeClass.equals("LoadHubNode") || nodeClass.equals("LoadHubOrNullNode");
    }

    private void classifyUsage(RAtom atom, LocalFlowGraph frame, ValueNode n, Node u, CallPath path, MethodContext mctx) {
        if (atom.kind == AtomKind.STRING && stringUsage(atom, frame, n, u, path, mctx)) {
            return; // the STRING rows of the one table; the shared rows follow
        }
        if (isIdQuery(atom) && classEscape(n, u)) {
            if (isNamedQuery(atom)) {
                // A named query object's Class whose every use is an observation (same method,
                // through Pis) gives no foreign birth; any other use (and a clone) is CLASS_ESCAPE as for any query
                if (!(u instanceof ObjectClone) && u instanceof ValueNode cu && objectReturn.harmlessClassUses(cu, null)) {
                    objretNp5Harmless.incrementAndGet();
                    return;
                }
                objretClassEscapes.incrementAndGet();
                refuse(atom.table, RTrackRefusal.CLASS_ESCAPE);
                return;
            }
            // The instance's Class object escapes (getClass, a hub load, clone): a foreign birth of
            // the class becomes possible, so the birth set is no longer complete; the query falls back
            objidClassEscapes.incrementAndGet();
            refuse(atom.table, RTrackRefusal.CLASS_ESCAPE);
            return;
        }
        if (u instanceof StoreFieldNode sfn) {
            if (sfn.value() == n) {
                escape(atom, frame, sfn, path, mctx);
            }
            if (sfn.object() == n && !sfn.field().isStatic()) {
                AnalysisField f = bridge.resolveField(sfn.field());
                if (f == null) {
                    refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE);
                    return;
                }
                recordStore(atom, frame, sfn, sfn.value(), f, path, mctx);
            }
            return;
        }
        if (u instanceof LoadFieldNode lfn) {
            if (lfn.object() == n && !lfn.field().isStatic()) {
                AnalysisField f = bridge.resolveField(lfn.field());
                if (f == null) {
                    refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE);
                    return;
                }
                recordLoad(atom, frame, lfn, f, path, mctx);
            }
            return; // record and stop
        }
        if (u instanceof StoreIndexedNode sin) {
            if (sin.value() == n) {
                escape(atom, frame, sin, path, mctx);
            }
            if (sin.array() == n) {
                if (atom.length0) {
                    counters[ContextPolicy.CIDX_LENGTH_ZERO_PROOFS]++; // infeasible by proof
                } else if (sin.elementKind() == JavaKind.Object) {
                    recordStore(atom, frame, sin, sin.value(), ARRAY_ELEMENT, path, mctx);
                }
            }
            return;
        }
        if (u instanceof LoadIndexedNode lin) {
            if (lin.array() == n && lin.elementKind() == JavaKind.Object) {
                recordLoad(atom, frame, lin, ARRAY_ELEMENT, path, mctx);
            }
            return; // record and stop
        }
        if (u instanceof BasicArrayCopyNode acn) {
            boolean any = false;
            if (acn.getSource() == n) {
                recordLoad(atom, frame, acn, ARRAY_ELEMENT, path, mctx); // the copy's desugared load
                any = true;
            }
            if (acn.getDestination() == n) {
                any = true;
                if (!atom.length0) {
                    // The desugared store's value is the desugared load of src.
                    recordStore(atom, frame, acn, new DesugaredLoad(acn, ARRAY_ELEMENT), ARRAY_ELEMENT, path, mctx);
                }
            }
            if (!any) {
                unclassified(atom, u);
            }
            return;
        }
        if (u instanceof ObjectClone oc) {
            if (oc.getObject() == n) {
                // Clone: T(src).loads[m] gains the desugared load for every member m.
                ValueNode cloneNode = (ValueNode) u;
                atom.table.addWildcardLoad(m -> new LoadEntry(frame, cloneNode, path, mctx));
            } else {
                unclassified(atom, u);
            }
            return;
        }
        if (u instanceof CommitAllocationNode can) {
            commitValueEscapes(atom, frame, n, can, path, mctx);
            return;
        }
        if (u instanceof VirtualState || u instanceof FrameState) {
            return; // deopt/virtual-state metadata (the materialisation is the commit)
        }
        if (u instanceof MethodCallTargetNode ct) {
            invokeUsage(atom, frame, n, ct, path, mctx);
            return;
        }
        if (u instanceof IndirectCallTargetNode ict && reflectionCrossings.bridgedInvokeUsage(atom, frame, n, ict, path, mctx)) {
            return; // a reflection edge (OUTER / INNER) is a bridged crossing; any other indirect call below
        }
        if (u instanceof ReturnNode ret) {
            if (ret.result() == n) {
                returnCase(atom, frame, path, mctx);
            }
            return;
        }
        if (u instanceof UnwindNode uw) {
            if (uw.exception() == n) {
                refuse(atom.table, RTrackRefusal.EXCEPTION_FLOW_UNMODELLED); // throws lower to Unwind
            }
            return;
        }
        if (isUnsafeFamily(u)) {
            refuse(atom.table, RTrackRefusal.UNSAFE_ACCESS); // the Unsafe family
            return;
        }
        if (u instanceof com.oracle.svm.core.graal.thread.StoreVMThreadLocalNode sv) {
            if (sv.getValue() == n) {
                threadLocal.vmtlEscape(atom, vmtlIdentity(sv)); // a store into the variable's table
            }
            return; // the holder input is an IsolateThread word, never an object
        }
        if (u instanceof com.oracle.svm.core.graal.thread.CompareAndSetVMThreadLocalNode cas) {
            if (cas.getUpdate() == n) {
                threadLocal.vmtlEscape(atom, vmtlIdentity(cas));
            }
            return; // the expected value is a reference comparison (an observation)
        }
        // --- nodes that carry the same object onward ---
        if (u instanceof PiNode pi && pi.getOriginalNode() == n && piArmDead(atom, frame, pi, n)) {
            silentEnd(atom, frame, pi, "pi-arm-dead");
            return; // the Pi lies in an arm no member of the atom's block can take (the arm-liveness table)
        }
        if (u instanceof LimitedValueProxy p && p.getOriginalNode() == n) {
            enqueueWalk(atom, frame, (ValueNode) u, path, mctx);
            return;
        }
        if (u instanceof PhiNode phi && phi.values().contains(n)) {
            enqueueWalk(atom, frame, phi, path, mctx);
            return;
        }
        if (u instanceof ConditionalNode cond && (cond.trueValue() == n || cond.falseValue() == n)) {
            enqueueWalk(atom, frame, cond, path, mctx);
            return;
        }
        if (isLiteralAtom(atom) && identityObservation(u)) {
            // The replaced literal is the pooled SingleByteString, not the interned String
            refuse(atom.table, RTrackRefusal.LITERAL_IDENTITY);
            return;
        }
        if (u instanceof BytecodeExceptionNode ben && assertionMessageUse(ben, n)) {
            // The detail message of an implicit `new AssertionError(o)` (ImplicitAssertionsPhase): exception flow
            assertionMessageRefusals.incrementAndGet();
            refuse(atom.table, RTrackRefusal.EXCEPTION_FLOW_UNMODELLED);
            return;
        }
        if (OBSERVATIONS.contains(u.getClass().getSimpleName()) ||
                        u instanceof jdk.graal.compiler.replacements.nodes.IdentityHashCodeNode) {
            return;
        }
        if (fallbackRefusal(u, n) == RTrackRefusal.UNSAFE_ACCESS) {
            bump(r2UnsafeByClass, u.getClass().getSimpleName()); // the R2 row's name (print-only census)
            refuse(atom.table, RTrackRefusal.UNSAFE_ACCESS);
            return;
        }
        unclassified(atom, u);
    }

    /**
     * An extension of the arm-liveness filter: the walk does not continue at a {@code PiNode} that the guard-feasibility
     * table ({@code ForwardFixpoint.armDeadDirection}, as {@link #strUsage} applies it) proves unreachable for every
     * member of the atom's carried block. The anchor is the Pi's guard (an unguarded Pi anchors at its fixed consumers)
     * and the guards are the real {@code instanceof} tests of the walked value ({@code LocalFlowGraph.guardsForValue}): a
     * Pi's value exists only once its guard has run, so a guard confined to a dead arm carries nothing of this atom
     * onward. The Pi's own stamp is never read. The block is {@link #atomSiteBlock}: a STRING atom's widened String cone,
     * which is {String} in the child. No finality premise is needed: a String that becomes a rep in the parent decides
     * every child-IR test as String does, because the reps add no supertype beyond String's and no rep-typed test exists
     * in the child's IR (the rep plugins register only outside the fork). An allocation atom uses its widened mint block
     * (a superset of its exact type); constants and thread atoms
     * have none (nothing is stopped). Only this continuation stops; the atom's other uses of the node are still walked.
     * Deterministic: a pure function of the IR, the block and the closed-world types.
     */
    private boolean piArmDead(RAtom atom, LocalFlowGraph frame, PiNode pi, ValueNode n) {
        if (strSites == null) {
            return false;
        }
        ForwardFixpoint.Block block = atomSiteBlock(atom);
        if (block == null || block.isTop()) {
            return false;
        }
        Node anchor = pi.getGuard() != null ? pi.getGuard().asNode() : pi;
        int dead = strSites.armFeasibility(frame, anchor, n, block);
        if (dead == 0) {
            return false;
        }
        armPiStops.incrementAndGet();
        if (DUMP && focused(String.valueOf(atom.key))) {
            System.out.println("[rtrack-dump] ARM-PI-STOP atom=" + atom.key + " frame=" + frameName(frame) + " pi=" + pi + " guard=" + anchor +
                            (dead == 1 ? " (vacuous)" : " (never)") + " block=" + block);
        }
        return true;
    }

    /** Census: walk continuations stopped at a dead arm's Pi. */
    final Counter armPiStops = new Counter();

    /**
     * The refusal of a use that reaches the walk's final fallback: {@code UNSAFE_ACCESS} for the R2 row, else
     * {@code UNCLASSIFIED_ACCESS}. Package-private for JUnit.
     *
     * <p>A container atom's use in the lowered raw-memory row R2 ({@link LfgWalk#isRawMemoryUse}) refuses
     * {@link RTrackRefusal#UNSAFE_ACCESS} instead of the generic {@link RTrackRefusal#UNCLASSIFIED_ACCESS} (a name only:
     * every such use is refused either way).
     */
    static RTrackRefusal fallbackRefusal(Node u, Node n) {
        return LfgWalk.isRawMemoryUse(u, n) ? RTrackRefusal.UNSAFE_ACCESS : RTrackRefusal.UNCLASSIFIED_ACCESS;
    }

    final Map<String, Counter> noTargetBy = new ConcurrentHashMap<>();
    /** Census (counter-only): the callee of each crossing refused MISSING_IR (no frame / no graph). */
    final Map<String, Counter> missingIrBy = new ConcurrentHashMap<>();

    void missingIr(String side, ResolvedJavaMethod callee) {
        bump(missingIrBy, side + (callee != null ? callee.format("%H.%n(%p)") : "?"));
    }

    private void noTarget(LocalFlowGraph.LocalVertex cv, ResolvedJavaMethod target, String side) {
        String callee = target != null ? target.format("%H.%n") : "?";
        bump(noTargetBy, side + (cv.id < 0 ? "/det/" : "/lfg/") + (cv.calleeMethod == null ? "nullCallee/" : "") + callee);
    }

    private void unclassified(RAtom atom, Node u) {
        bump(unclassifiedByClass, u.getClass().getSimpleName());
        refuse(atom.table, RTrackRefusal.UNCLASSIFIED_ACCESS); // an unlisted use is refused, never skipped
    }

    /* package-private: also the string side's Unsafe-family test (LfgWalk). */
    static boolean isUnsafeFamily(Node u) {
        return u instanceof RawStoreNode || u instanceof RawLoadNode || u instanceof UnsafeMemoryLoadNode ||
                        u instanceof UnsafeMemoryStoreNode || u instanceof AtomicReadAndWriteNode ||
                        u instanceof AbstractUnsafeCompareAndSwapNode;
    }

    // ------------------------------------------------------------------
    // The thread-local mechanism.
    // ------------------------------------------------------------------
    /** The synthetic member of a thread-local variable (one global slot per variable; threads merged). */
    static final Object TL_VALUE = new Object() {
        @Override
        public String toString() {
            return "<tlvalue>";
        }
    };

    /** The site of the one current-thread singleton atom. */
    static final Object CURRENT_THREAD_SITE = new Object() {
        @Override
        public String toString() {
            return "<currentThread>";
        }
    };

    final Map<ResolvedJavaMethod, TlOp> tlOpMemo = new ConcurrentHashMap<>();

    /**
     * The current-thread variable is matched by its FastThreadLocal location identity
     * ({@code PlatformThreads.currentThread.getLocationIdentity()}), never by name. Unresolvable → null: no access matches
     * and the variable becomes an ordinary per-variable table.
     */
    static volatile Object currentThreadIdentity;
    static volatile boolean currentThreadIdentityLooked;

    // Census (counters only; no decision reads them).
    final Counter tlLoads = new Counter();
    final Counter tlStores = new Counter();
    final Counter tlEscapes = new Counter();
    final Counter tlInitial = new Counter();
    final Counter tlCrossings = new Counter();
    final Counter tlBackwardLoads = new Counter();
    final Counter tlCurrentThreadResolutions = new Counter();
    final Counter tlVmtlLoads = new Counter();
    final Counter tlVmtlEscapes = new Counter();
    final Map<String, Counter> tlUnmodelledBy = new ConcurrentHashMap<>();

    volatile AnalysisType[] tlTypes;

    /** A JDK (boot loader) class by name as an AnalysisType, or null when unavailable (the thread-local and JDK models). */
    AnalysisType jdkType(String name) {
        try {
            return bridge.lookupJavaType(Class.forName(name, false, Object.class.getClassLoader()));
        } catch (Throwable e) {
            return null;
        }
    }

    /** The instance field {@code name} declared by {@code t}, resolved; null when unavailable. */
    AnalysisField declaredField(AnalysisType t, String name) {
        try {
            for (ResolvedJavaField f : t.getInstanceFields(false)) {
                if (f.getName().equals(name)) {
                    return bridge.resolveField(f);
                }
            }
        } catch (Throwable ignore) {
            // unavailable (t null included): the caller refuses by name
        }
        return null;
    }

    static ResolvedJavaMethod declaredMethod(AnalysisType t, String name, String sig) {
        if (t == null) {
            return null;
        }
        try {
            for (ResolvedJavaMethod m : t.getDeclaredMethods(false)) {
                if (m.getName().equals(name) && m.getSignature().toMethodDescriptor().equals(sig)) {
                    return m;
                }
            }
        } catch (Throwable ignore) {
            // unavailable: the caller refuses by name
        }
        return null;
    }

    /** The exact type of an atom's object, or null when the birthplace does not fix it. */
    AnalysisType atomExactType(RAtom a) {
        if (a.kind == AtomKind.CONSTANT) {
            return a.constant != null ? a.constant.getType() : null;
        }
        if (models.isFresh(a)) {
            return models.freshExactType(a); // a model's fresh object (null: inexact)
        }
        return a.birthNode != null ? exactTypeOf(a.birthNode) : null;
    }

    final AtomicLong typedStops = new AtomicLong();

    /** The root of a type-only operand sink (wraps the operand; never equal to an identity root). */
    record TypedRecvKey(Object operand) {
    }

    /** A sink "atom" that stands for "some instance of {@code type} (or null)". */
    record TypeToken(AnalysisType type) {
    }

    /**
     * The final stamp type of {@code n} a typed sink stops at, or null. {@code String} counts as final: it
     * is not final in the builder JDK (the custom reps subclass it), but its analysed cone in the child is {String} and the
     * reps are the runtime replacement of a String.
     *
     * <p>Typed receiver selection. A model callback's per-receiver
     * selection ({@code JdkModelEngine.perReceiverAtom}) needs only the receivers' classes. Its operand sink gets its own
     * root ({@link TypedRecvKey}) and its backward walk stops at the first visited value whose stamp type is a final class
     * or {@code String} (this test): that value is an instance of that class (or null) whatever its origin,
     * so one {@link TypeToken} replaces the atoms behind it (and their refusals: the identity is not needed). Also used
     * for a plain receiver whose CHA fan would refuse anyway. Sound: every value the sink visits is a value of the
     * receiver, and a final stamp bounds its run-time class; a non-final stamp continues as before.
     */
    static AnalysisType typedStopType(ValueNode n) {
        try {
            jdk.vm.ci.meta.ResolvedJavaType t = jdk.graal.compiler.nodes.type.StampTool.typeOrNull(n.stamp(jdk.graal.compiler.nodes.NodeView.DEFAULT));
            if (t instanceof AnalysisType at && !at.isInterface() && !at.isArray() && !at.isAbstract() &&
                            (at.isFinalFlagSet() || "java.lang.String".equals(at.toJavaName(true)))) {
                return at;
            }
        } catch (Throwable e) {
            return null;
        }
        return null;
    }

    static boolean typedSink(Sink sink) {
        return sink.rootKey instanceof SinkRoot sr && sr.node() instanceof TypedRecvKey;
    }

    /** The String-cone block of a STRING atom key (its fixed site block, else TOP), or null. */
    ForwardFixpoint.Block stringAtomBlockOf(Object key) {
        RAtom a = atoms.get(key);
        return a != null && a.kind == AtomKind.STRING ? (a.siteBlock != null ? a.siteBlock : ForwardFixpoint.Block.TOP) : null;
    }

    /** The exact type of the atom with key {@code key} (a sink's atom), or null. */
    AnalysisType atomExactTypeOf(Object key) {
        RAtom a = atoms.get(key);
        return a == null || a.kind == AtomKind.STRING ? null : atomExactType(a); // a String's class is never exact (custom reps)
    }

    final Set<RAtomKey> tlVariables = ConcurrentHashMap.newKeySet();
    volatile int heapThreadLocalMaps = -2;

    volatile Boolean tlInternalsReflective;

    // --- the current thread: one singleton aliasing every Thread-typed atom ---
    volatile List<Object[]> currentThreadReads;
    volatile List<Object[]> threadSites;

    /** Every current-thread read site outside the accessor methods: {frame, node} (image-wide, deterministic order). */
    synchronized List<Object[]> currentThreadReads() {
        if (currentThreadReads != null) {
            return currentThreadReads;
        }
        List<Object[]> out = new ArrayList<>();
        for (AnalysisMethod m : threadLocal.tlIndexedMethods()) {
            if (threadLocal.tlOp(m) == TlOp.CURRENT_THREAD) {
                continue; // the accessors' results are the singleton (their callers' invokes are read sites)
            }
            LocalFlowGraph frame = bridge.frameOf(m);
            StructuredGraph g = frame != null ? graphOf(frame) : null;
            if (g == null) {
                continue;
            }
            for (Node node : g.getNodes()) {
                if (node instanceof com.oracle.svm.core.graal.thread.LoadVMThreadLocalNode && isCurrentThreadVmtl(vmtlIdentity(node)) ||
                                node instanceof Invoke inv && inv.callTarget() != null && threadLocal.tlOp(inv.callTarget().targetMethod()) == TlOp.CURRENT_THREAD) {
                    out.add(new Object[]{frame, node});
                }
            }
        }
        currentThreadReads = out;
        return out;
    }

    /** Every allocation site whose object may be a Thread: {frame, node}. */
    synchronized List<Object[]> threadSites() {
        if (threadSites != null) {
            return threadSites;
        }
        List<Object[]> out = new ArrayList<>();
        AnalysisType threadType = threadLocal.tlTypes()[0];
        for (AnalysisMethod m : threadLocal.tlIndexedMethods()) {
            LocalFlowGraph frame = bridge.frameOf(m);
            StructuredGraph g = frame != null ? graphOf(frame) : null;
            if (g == null) {
                continue;
            }
            for (Node node : g.getNodes()) {
                if (node instanceof ValueNode vn && mayBeThreadNode(vn, threadType)) {
                    out.add(new Object[]{frame, vn});
                }
            }
        }
        threadSites = out;
        return out;
    }

    // --- SVM VM thread-locals other than the current thread: one global table per variable ---
    final Map<Object, Table> vmtlTables = new ConcurrentHashMap<>();

    // ------------------------------------------------------------------
    // Materialisation = allocation + the initial stores of the commit.
    // ------------------------------------------------------------------
    private static int commitOffset(CommitAllocationNode can, VirtualObjectNode vo) {
        int pos = 0;
        for (VirtualObjectNode v : can.getVirtualObjects()) {
            if (v == vo) {
                return pos;
            }
            pos += v.entryCount();
        }
        return -1;
    }

    /**
     * The birth index's hole fix: the committed virtual instances of {@code can} without their own
     * {@link AllocatedObjectNode} in this commit (they live only as slot values of another committed object, e.g. a
     * varargs element): real births no walk can start from.
     */
    static List<VirtualInstanceNode> unwalkableInstances(CommitAllocationNode can) {
        List<VirtualInstanceNode> out = new ArrayList<>();
        for (VirtualObjectNode vo : can.getVirtualObjects()) {
            if (vo instanceof VirtualInstanceNode vin && allocatedOf(can, vo) == null) {
                out.add(vin);
            }
        }
        return out;
    }

    private static AllocatedObjectNode allocatedOf(CommitAllocationNode can, VirtualObjectNode vo) {
        for (Node user : can.usages()) {
            if (user instanceof AllocatedObjectNode aon && aon.getVirtualObject() == vo) {
                return aon;
            }
        }
        return null;
    }

    private Object memberOfVirtual(VirtualObjectNode vo, int idx) {
        if (vo instanceof VirtualInstanceNode vin) {
            ResolvedJavaField rf = vin.field(idx);
            return rf != null ? bridge.resolveField(rf) : null;
        }
        return vo instanceof VirtualArrayNode ? ARRAY_ELEMENT : null;
    }

    /** O's own table: the commit's value slots of O are its initial member stores. */
    private void commitInitialStores(RAtom atom, AllocatedObjectNode aon, MethodContext mctx) {
        CommitAllocationNode can = aon.getCommit();
        VirtualObjectNode vo = aon.getVirtualObject();
        int off = can != null ? commitOffset(can, vo) : -1;
        if (off < 0) {
            refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE);
            return;
        }
        List<ValueNode> values = can.getValues();
        for (int i = 0; i < vo.entryCount(); i++) {
            ValueNode v = values.get(off + i);
            if (v == null || v.getStackKind() != JavaKind.Object) {
                continue;
            }
            Object member = memberOfVirtual(vo, i);
            if (member == null) {
                refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE);
                continue;
            }
            JdkModels.Slot rec = models.recordSlot(member);
            if (rec != null) {
                // An inlined record constructor's component (a collector record): a store of its slot
                if (!v.isNullConstant()) {
                    recordCommitStores.incrementAndGet(); // the translations, not the memo fills
                    recordStore(atom, atom.birthFrame, new CommitStore(can, vo, i), v, rec, null, mctx);
                }
                continue;
            }
            JdkModels.Slot rep = models.representationSlot(member, "commit-rep");
            if (rep != null) {
                // An inlined constructor's initial store of a representation field: the slot gets the elements
                recordStore(atom, atom.birthFrame, new CommitStore(can, vo, i), models.repElements(v), rep, null, mctx);
                continue;
            }
            if (v.isNullConstant() && models.abstracted(member)) {
                continue; // a node representation's initial null (LinkedList.first): no reference is stored
            }
            recordStore(atom, atom.birthFrame, new CommitStore(can, vo, i), v, member, null, mctx);
        }
        // O referenced from another committed object's slot (a VirtualObjectNode value):
        // an initial store of O into that object, O's escape.
        int pos = 0;
        for (VirtualObjectNode other : can.getVirtualObjects()) {
            for (int i = 0; i < other.entryCount(); i++) {
                if (values.get(pos + i) == vo) {
                    commitEscape(atom, atom.birthFrame, can, other, i, null, mctx);
                }
            }
            pos += other.entryCount();
        }
    }

    /** n (the atom's value) is a slot value of a committed object: the escape into O.m. */
    private void commitValueEscapes(RAtom atom, LocalFlowGraph frame, ValueNode n, CommitAllocationNode can, CallPath path,
                    MethodContext mctx) {
        int pos = 0;
        boolean any = false;
        List<ValueNode> values = can.getValues();
        for (VirtualObjectNode vo : can.getVirtualObjects()) {
            for (int i = 0; i < vo.entryCount(); i++) {
                if (values.get(pos + i) == n) {
                    any = true;
                    commitEscape(atom, frame, can, vo, i, path, mctx);
                }
            }
            pos += vo.entryCount();
        }
        if (!any) {
            unclassified(atom, can); // e.g. a lock input; never a silent pass
        }
    }

    private void commitEscape(RAtom atom, LocalFlowGraph frame, CommitAllocationNode can, VirtualObjectNode vo, int idx,
                    CallPath path, MethodContext mctx) {
        AllocatedObjectNode target = allocatedOf(can, vo);
        Object member = memberOfVirtual(vo, idx);
        JdkModels.Slot rec = models.recordSlot(member);
        member = rec != null ? rec : member; // a record component escapes into its slot
        if (target == null || member == null) {
            refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE);
            return;
        }
        escapeInto(atom, frame, new CommitStore(can, vo, idx), target, member, path, mctx);
    }

    // ------------------------------------------------------------------
    // Table entries.
    // ------------------------------------------------------------------
    private static boolean primitiveMember(Object member) {
        return member instanceof AnalysisField f && f.getJavaKind() != JavaKind.Object;
    }

    void recordStore(RAtom atom, LocalFlowGraph frame, Object node, Object value, Object member, CallPath path,
                    MethodContext mctx) {
        if (primitiveMember(member) || (value instanceof ValueNode vn && vn.getStackKind() != JavaKind.Object)) {
            return; // no reference can flow through a primitive member (nothing to connect)
        }
        if (models.fieldRule(atom.table, member, "field-store")) {
            return; // the IR writes a representation field
        }
        EntryList<StoreEntry> list = atom.table.stores(member);
        StoreEntry e = new StoreEntry(frame, node, value, path, mctx);
        if (list.append(e, e.dedupKey(), e.nodeKey()) >= 0) {
            censusStoreEntries.incrementAndGet();
            if (list.distinctNodeCount() > STORE_FAN_CAP) {
                refuse(atom.table, RTrackRefusal.STORE_FAN_CAP);
            }
            checkReflectiveField(atom.table, member);
        }
    }

    void recordLoad(RAtom atom, LocalFlowGraph frame, Object node, Object member, CallPath path,
                    MethodContext mctx) {
        if (primitiveMember(member)) {
            return;
        }
        if (models.fieldRule(atom.table, member, "field-load")) {
            return; // the IR reads a representation field
        }
        EntryList<LoadEntry> list = atom.table.loads(member);
        LoadEntry e = new LoadEntry(frame, node, path, mctx);
        if (list.append(e, e.dedupKey()) >= 0) {
            censusLoadEntries.incrementAndGet();
            checkReflectiveField(atom.table, member);
        }
    }

    /**
     * A member the analysis flags reflectively/Unsafe/JNI accessed refuses the table.
     * JNI registration sets neither the Unsafe flag nor an access reason ({@code JNIAccessFeature.addField} registers
     * the field as read/written only), so the JNI registry is consulted too ({@link #jniRegistered}).
     */
    private void checkReflectiveField(Table t, Object member) {
        if (member instanceof AnalysisField f) {
            boolean flagged;
            try {
                flagged = f.isUnsafeAccessed();
                if (!flagged && jniRegistered(f)) {
                    flagged = true;
                    bump(jniFieldRefusalsBy, f.format("%H.%n")); // print-only census: jnifield{...}
                }
            } catch (Throwable ignore) {
                flagged = true; // metadata unreadable: refuse (never assume clean)
            }
            if (flagged) {
                refuse(t, RTrackRefusal.REFLECTIVE_FIELD);
            }
        }
    }

    /** Print-only: the reflective-access refusals that only the JNI registry flags, per field (census {@code jnifield{...}}). */
    final Map<String, Counter> jniFieldRefusalsBy = new ConcurrentHashMap<>();

    /** "declaringClass.name" of every JNI-registered field (built once, after the fixpoint); null = unreadable (fail closed). */
    private volatile Set<String> jniFields;
    private volatile boolean jniFieldsBuilt;

    /**
     * The field is registered for JNI access ({@code JNIReflectionDictionary}: native code may read
     * or write it behind the analysis). A registry that cannot be read answers true (fail closed).
     */
    boolean jniRegistered(AnalysisField f) {
        if (!jniFieldsBuilt) {
            synchronized (this) {
                if (!jniFieldsBuilt) {
                    jniFields = readJniFields();
                    jniFieldsBuilt = true;
                }
            }
        }
        Set<String> s = jniFields;
        if (s == null) {
            return true;
        }
        try {
            return !s.isEmpty() && s.contains(f.getDeclaringClass().toJavaName(true) + "." + f.getName());
        } catch (Throwable t) {
            return true;
        }
    }

    private static Set<String> readJniFields() {
        try {
            if (!org.graalvm.nativeimage.ImageSingletons.contains(com.oracle.svm.core.jni.access.JNIReflectionDictionary.class)) {
                return Set.of(); // no JNI support in this image: nothing is JNI-accessed
            }
            Set<String> out = new java.util.HashSet<>();
            for (com.oracle.svm.core.jni.access.JNIAccessibleClass c : com.oracle.svm.core.jni.access.JNIReflectionDictionary.currentLayer().getClasses()) {
                if (c == null || c.isNegative() || c.getClassObject() == null) {
                    continue;
                }
                var cur = c.getFields();
                while (cur.advance()) {
                    out.add(c.getClassObject().getName() + "." + cur.getKey());
                }
            }
            return out;
        } catch (Throwable t) {
            return null;
        }
    }

    // ------------------------------------------------------------------
    // RETURN: matched returns, birth-method exits, the merge fallback.
    // ------------------------------------------------------------------
    static MethodContext restored(Object callerMctx) {
        return callerMctx instanceof MethodContext mc ? mc : MethodContext.UNKNOWN;
    }

    /**
     * RETURN out of {@code frame}: a non-empty path returns to its top call and restores the caller's method context
     * carried on the link. With an empty path the invocation context decides: STATIC(call, caller) → back to exactly
     * that call, continuing with {@code caller} (the whole static chain is kept); OWNER(Y) → a waiter on
     * T(Y).entryPaths[frame] (see {@link #ownerRetFallbacks}); otherwise (merged / truncated / unknown) → every caller,
     * capped.
     */
    private void returnCase(RAtom atom, LocalFlowGraph frame, CallPath path, MethodContext mctx) {
        if (path != null && path.call instanceof DesugaredCall dc) {
            concatOperandArrival(atom, dc); // the implicit toString()'s result
            return;
        }
        if (models.returnArrival(atom, path)) {
            return; // a model callback's result
        }
        if (path != null && path.isFold()) {
            returnAlongFold(atom, frame, path); // the recursion fold
            return;
        }
        if (path != null) {
            List<ValueNode> invs = invokesOf(path);
            if (invs.isEmpty()) {
                refuse(atom.table, RTrackRefusal.MISSING_IR);
                return;
            }
            for (ValueNode inv : invs) {
                enqueueWalk(atom, path.callerFrame, inv, path.next, restored(path.callerMctx));
            }
            return;
        }
        if (mctx != null && mctx.isStatic()) {
            ContextElement e = mctx.call;
            LocalFlowGraph caller = bridge.frameOf(e.method);
            List<ValueNode> invs = caller != null ? invokesByBci(caller, e.bci) : List.of();
            if (invs.isEmpty()) {
                refuse(atom.table, RTrackRefusal.MISSING_IR);
                return;
            }
            MethodContext callerCtx = mctx.caller != null ? mctx.caller : MethodContext.UNKNOWN;
            for (ValueNode inv : invs) {
                enqueueWalk(atom, caller, inv, null, callerCtx);
            }
            return;
        }
        if (mctx != null && mctx.isOwner()) {
            RAtom owner = atoms.get(internKey(mctx.ownerSite, mctx.ownerCtx));
            if (owner != null) {
                if (worldTop.outsideCaller(frame)) {
                    // A return with an empty path: OWNER(Y) does not tell this
                    // invocation from an outside invocation on the same receiver, and T(Y).entryPaths lists only the
                    // analysed calls -- the outside caller is refused (a STATIC context is one call: exact, no refusal).
                    e2OwnerRetWorldTop.incrementAndGet();
                    worldTop.e2Note("WTX-owner", frame);
                    refuse(atom.table, RTrackRefusal.WORLD_TOP_EXIT);
                }
                // A monotone waiter on T(owner).entryPaths[frame]; it stays registered after the fallback (a pure
                // union, see ownerRetFallbacks).
                EntryList<CallPath> list = owner.table.entryPaths(frame);
                // Holder-end rule: a wait that never delivers (and never falls back) is an unexplained end of this walk
                WaitRec wr = holderEnd.waitRec(atom, "ownerret", frame, owner.key);
                Consumer<Integer> ownerCont = idx -> {
                    if (wr != null) {
                        wr.delivered.set(true);
                    }
                    objectIdentity.returnAtEntry(atom, frame, list.get(idx)); // the factored continuation
                };
                AtomicBoolean fell = new AtomicBoolean();
                register(list, List.of("ownerret-fb", atom.key, frame), ownerCont, null, r -> {
                    if (wr != null) {
                        wr.fell.set(true);
                    }
                    if (fell.compareAndSet(false, true)) {
                        ownerRetFallbacks.incrementAndGet();
                        returnAllCallers(atom, frame);
                    }
                }, null, atom.table); // the owner waiter widens T(atom): ID-DEP travels to it
                return;
            }
        }
        if (OBJRET_ON && objectReturn.objretReturn(atom, frame)) {
            return; // rule U delivered (objret=1); the census alone (objret=0) never returns true
        }
        if (objectIdentity.idReturn(atom, frame)) {
            return; // the identity caller set of a qualifying class (its first refusal adds the fan below, once)
        }
        // MERGED / unknown / an exhausted path: the merge, every caller,
        // capped (the truncated rule).
        returnAllCallers(atom, frame);
    }

    /**
     * The owner-return fallback. A return under OWNER(Y)
     * waits on {@code T(Y).entryPaths(frame)}, the calls of this frame on Y; it needs only those callers, not Y's
     * contents. T(Y)'s first refusal (one-shot) adds the merged rule {@link #returnAllCallers} (every
     * caller of the frame, capped, with its own named refusals) to the deliveries instead of inheriting the refusal.
     * Soundness is a pure union, nothing is removed: the owner waiter ({@code ownerCont}) stays registered and keeps
     * delivering every existing and future entry of the list, including entry paths {@code callersOf} cannot enumerate (a
     * desugared {@code toString()} crossing → {@code concatOperandArrival}, the thread-local {@code initialValue()}
     * crossing). "The merged rule is a superset of the calls on Y" is not the argument: some owner-rule deliveries are not
     * calls of the frame at all, and they survive only because the registration stays. Dropping the owner registration at
     * the switch would open a hole. Same shape as the closed-field fallback. Counts the fallbacks taken.
     */
    final AtomicLong ownerRetFallbacks = new AtomicLong();

    void returnAllCallers(RAtom atom, LocalFlowGraph frame) {
        if (containerCallersIncomplete(frame)) {
            refuse(atom.table, RTrackRefusal.MISSING_IR); // a caller the index cannot enumerate: never a silent miss
            return;
        }
        List<ForwardFixpoint.CallerSite> callers = worldTop.fanCallersOf(frame); // the receiver-typed caller filter
        // An outside caller refuses WORLD_TOP_EXIT (the direct callers are still fanned
        // over); no caller at all refuses NO_CALLER_EXIT, so an empty list never ends silently.
        int nCallers = callers == null ? 0 : callers.size();
        RTrackRefusal rx = returnExitRefusal(worldTop.outsideCaller(frame), nCallers);
        if (rx != null) {
            (rx == RTrackRefusal.WORLD_TOP_EXIT ? e2WorldTopExit : e2NoCallerExit).incrementAndGet();
            worldTop.e2Note(rx == RTrackRefusal.WORLD_TOP_EXIT ? (nCallers == 0 ? "WTX-empty" : "WTX-fan") : "NCX", frame);
            refuse(atom.table, rx);
        }
        if (nCallers == 0) {
            return; // no analysed caller (refused NO_CALLER_EXIT or WORLD_TOP_EXIT above)
        }
        if (callers.size() > RETURN_FAN_CAP) {
            refuse(atom.table, RTrackRefusal.RETURN_FAN_CAP);
            return;
        }
        for (ForwardFixpoint.CallerSite c : callers) {
            LocalFlowGraph callerFrame = c.call() != null ? c.call().owner : null;
            List<ValueNode> invs = c.call() != null ? invokesOfVertex(callerFrame, c.call()) : List.of();
            if (callerFrame == null || invs.isEmpty()) {
                refuse(atom.table, RTrackRefusal.MISSING_IR);
                return;
            }
            for (ValueNode inv : invs) {
                enqueueWalk(atom, callerFrame, inv, null, MethodContext.UNKNOWN);
            }
        }
    }

    // ------------------------------------------------------------------
    // Lambda object-identity tracking's state (the rule: ObjectIdentityRule).
    // ------------------------------------------------------------------

    final Map<Object, IdSite> idSites = new ConcurrentHashMap<>();

    final Map<AnalysisType, IdQuery> idQueries = new ConcurrentHashMap<>();
    /** Census (print-only). */
    final AtomicLong objidFrames = new AtomicLong();
    final AtomicLong objidReturns = new AtomicLong();
    final AtomicLong objidFallbacks = new AtomicLong();
    final AtomicLong objidDeliveries = new AtomicLong();
    final AtomicLong objidContra = new AtomicLong();
    final AtomicLong objidContraUnchecked = new AtomicLong();
    final Set<String> objidContraSeen = ConcurrentHashMap.newKeySet();
    final AtomicLong objidClassEscapes = new AtomicLong();
    final Map<String, Counter> objidFellBy = new ConcurrentHashMap<>();
    /** The frames whose path-less return / parameter took the identity caller set (the OBJID-DROP census, print-only). */
    final Set<LocalFlowGraph> objidHookedFrames = ConcurrentHashMap.newKeySet();
    final AtomicLong objidDrops = new AtomicLong();

    final AtomicLong objidParams = new AtomicLong();
    final AtomicLong objidParamFallbacks = new AtomicLong();

    // ------------------------------------------------------------------
    // The uniform object-return rule (rule U) for named classes, the census half (fwd.rtrack.objret.census=1): at a
    // path-less return or parameter of an instance frame of a non-hidden class C whose ordinary rule would refuse, it
    // computes C's query (ObjRetRules) and prints whether the caller set would come out precise. It delivers nothing.
    // The rule: ObjectReturnRule; its knobs and state stay here.
    // ------------------------------------------------------------------
    /**
     * Knob {@code fwd.rtrack.objret} (default 1): 1 = rule U delivers: at a path-less return / parameter of an instance
     * frame of a named class whose ordinary rule would refuse, the class's precise caller set (the named object-identity
     * query under the conditional premise) is delivered instead; every admit that reads such a delivery is marked ID-DEP
     * and loses to a non-ID-DEP admit in every cross-candidate pass (equals / compareTo conflict, receiver cap, nested
     * concat), and a child whose run trips the EVALUATION_GUARD with a usable delivery reruns once at objret=0. 0 = off
     * (no named query, no delivery, no ID-DEP flag).
     */
    static final int OBJRET = Integer.getInteger("svm.stringanalysis.fwd.rtrack.objret", 1);
    static final boolean OBJRET_CENSUS = Integer.getInteger("svm.stringanalysis.fwd.rtrack.objret.census", 0) != 0;
    /** objret=1 = rule U delivers (the named hooks become the rule). */
    static final boolean OBJRET_DELIVER = OBJRET != 0;
    /** The named query machinery runs (census or delivery); off = no named query at all (objret=0, no census). */
    static final boolean OBJRET_ON = OBJRET_CENSUS || OBJRET_DELIVER;

    final AtomicLong objretNp5Harmless = new AtomicLong();
    final AtomicLong objretClassEscapes = new AtomicLong();
    final AtomicLong objretHiddenNest = new AtomicLong();
    final AtomicLong objretEvents = new AtomicLong();
    final Map<Object, IdSite> namedSites = new ConcurrentHashMap<>();
    /** Heap births: the instance's ConstantData -> its query atom. */
    final Map<Object, RAtom> heapTwins = new ConcurrentHashMap<>();
    /** A named query atom -> the queries whose cone holds its birth (one birth may be in several cones). */
    final Map<RAtomKey, Set<NamedQuery>> namedAtomOwners = new ConcurrentHashMap<>();
    final Map<AnalysisType, NamedQuery> namedQueries = new ConcurrentHashMap<>();
    final Map<List<Object>, TriggerRec> objretTriggers = new ConcurrentHashMap<>();

    final List<ObjretHook> objretHooks = new ArrayList<>();
    final AtomicLong objretDelivered = new AtomicLong();
    final AtomicLong objretDeliveries = new AtomicLong();
    final AtomicLong objretFallbacks = new AtomicLong();
    final AtomicLong objretEmptyFallbacks = new AtomicLong();

    /** The lookahead: memo (frame, depth) -> the witness ("" = none). Pure function of fixed post-analysis facts. */
    final Map<List<Object>, String> lookaheadMemo = new ConcurrentHashMap<>();
    final AtomicLong objretLookaheadFrames = new AtomicLong();

    volatile NavCensus navCensus;

    volatile NavIndex navIndex;

    volatile Map<Object, AnalysisType> companionOwners;

    volatile SelfSlotImage selfSlotImage;
    volatile Map<AnalysisType, ImageHeapConstant> hubObjects;
    /** Census: per class, the discounted self slots, or the first refusal reason of a slot that matched (sole|pending|reader|mode). */
    final Map<AnalysisType, String> selfSlotOutcome = new ConcurrentHashMap<>();

    volatile InlinedIndex inlinedIndex;
    final Map<AnalysisMethod, Boolean> inlinedOk = new ConcurrentHashMap<>();
    /** Census: per INLINED_ONLY method asked, {@code callers=n ok|FAIL}. */
    final Map<String, String> inlinedOnlyLines = new ConcurrentHashMap<>();

    /** The image-level wildcard verdict (memoised; the first failing wildcard caller for the census). */
    volatile Boolean wildcardsOk;
    volatile String wildcardFail;
    /** Census: the size of the closed wildcard set (-1 = the closure failed, or not computed). */
    volatile int wildcardsClosed = -1;

    /**
     * The CLINIT exception: {@code c} is a class initializer that never
     * runs at run time. (1) a class initializer; (2) not implementation-invoked, not a root; (3) its hub's
     * ClassInitializationInfo is non-null, initialized, with no initializer pointer; (4) the hosted state agrees
     * (initialized at build time or simulated); (5) a closed-world, non-layered build without run-time class loading
     * ({@link ClosedFieldEscape#closedWorldGuard}) and no run-time-compiled variant. Anything unreadable = false (fail closed).
     */
    final Map<AnalysisMethod, Boolean> deadClinitMemo = new ConcurrentHashMap<>();

    volatile Map<AnalysisType, List<AnalysisMethod>> reachableByType;

    volatile Set<Class<?>> metadataClasses;
    volatile boolean metadataDone;

    volatile String metadataProblem;

    volatile NamedPremise namedPremise;

    static final Set<ObjRetRules.GuardFailN> NAV_OR_UNFRAMED = java.util.EnumSet.of(ObjRetRules.GuardFailN.NEST_EXPOSED, ObjRetRules.GuardFailN.CONE_ARRAY,
                    ObjRetRules.GuardFailN.CLASS_HOLDER, ObjRetRules.GuardFailN.UNFRAMED_METHOD, ObjRetRules.GuardFailN.UNFRAMED_BIRTH);

    // ------------------------------------------------------------------
    // The pending slots' and the conditional premise's state (the rules: ObjectIdentityRule).
    // ------------------------------------------------------------------

    final Map<String, PendingSlot> pendingSlots = new ConcurrentHashMap<>();

    volatile IdPremise idPremise;

    volatile Map<AnalysisType, Object> hubConstants;
    /** Set when the hub snapshot could not be read completely (every class then counts one holder: fail closed). */
    volatile boolean hubConstantsFailed;

    volatile Set<Class<?>> serializationTargets;
    volatile boolean serializationDone;

    volatile Set<String> forNameNames;

    volatile IdBirthIndex idBirthIndex;

    List<ValueNode> invokesOf(CallPath p) {
        return invokesOfCall(p.callerFrame, p.call);
    }

    /** The invokes of a call identity in {@code frame} (a path link's or a fold edge's); empty = unresolvable (the caller refuses). */
    List<ValueNode> invokesOfCall(LocalFlowGraph frame, Object call) {
        if (call instanceof Invoke inv) {
            return List.of(inv.asNode() instanceof ValueNode vn ? vn : null);
        }
        if (call instanceof LocalFlowGraph.LocalVertex cv) {
            return invokesOfVertex(frame, cv);
        }
        return List.of();
    }

    // ------------------------------------------------------------------
    // Recursion folding. A forward plain-call push whose callee frame is already a caller
    // frame further up the path replaces the cycle with one fold link F(root, rootMctx, owner, next)
    // (ContextPolicy.CallPath.foldPush); every removed link and the new call is registered in the owner's grow-only edge
    // registry (Table.foldEdges(root, target)) before the folded position is enqueued. A return under F continues at
    // every registered edge into the returning frame (still under F, with the edge's caller mctx) and, out of the root
    // frame, also exits through F.next with rootMctx. A static callee of a folding push gets STATIC(c, null). Backward
    // under F is path-less (the full caller fan with the caller-index filter). Every other path reader is fail-safe.
    // ------------------------------------------------------------------
    final AtomicLong foldPushesA = new AtomicLong();
    final AtomicLong foldPushesB = new AtomicLong();
    final AtomicLong foldPushesC = new AtomicLong();
    final AtomicLong foldEdgesRegistered = new AtomicLong();
    final AtomicLong foldReturns = new AtomicLong();
    final AtomicLong foldReturnDeliveries = new AtomicLong();
    final AtomicLong foldRootExits = new AtomicLong();
    final AtomicLong foldBackwardPathless = new AtomicLong();
    final AtomicLong foldNoEdge = new AtomicLong();
    final Map<String, Counter> foldRootsBy = new ConcurrentHashMap<>();

    /**
     * The folding push of one crossing into {@code calleeFrame}, or null (then the caller keeps the plain push). On a
     * fold the edges are registered here, before the caller enqueues the folded position.
     */
    ContextPolicy.FoldPush foldedPush(RAtom atom, LocalFlowGraph frame, Object call, MethodContext mctx, CallPath path, LocalFlowGraph calleeFrame) {
        ContextPolicy.FoldPush fp = CallPath.foldPush(frame, call, mctx, path, calleeFrame, atom.table, ContextPolicy.PATHK);
        if (fp == null) {
            return null;
        }
        (fp.kind() == 'A' ? foldPushesA : fp.kind() == 'B' ? foldPushesB : foldPushesC).incrementAndGet();
        if (fp.kind() == 'A') {
            bump(foldRootsBy, frameName(fp.fold().root));
        }
        Table owner = (Table) fp.fold().owner;
        // registration order = the list order L(last) … L0, new (CallPath.foldPush)
        for (int i = 0; i < fp.edges().size(); i++) {
            ContextPolicy.FoldEdge e = fp.edges().get(i);
            if (owner.foldEdges(fp.fold().root, fp.targets().get(i)).append(e, e) >= 0) {
                foldEdgesRegistered.incrementAndGet();
            }
        }
        return fp;
    }

    /** The callee mctx of a crossing: {@link #enter}, except a static callee of a folding push gets STATIC(c, null). */
    MethodContext enterMaybeFolded(ContextPolicy.FoldPush fp, MethodContext mctx, LocalFlowGraph frame, Invoke inv, AnalysisMethod callee,
                    boolean receiverIsTracked, RAtom atom) {
        if (fp != null && callee.isStatic()) {
            return MethodContext.staticCtx(new ContextElement(bridge.methodOf(frame), StringAnalysisChildInlining.pointsToBci(inv)), null);
        }
        return enter(mctx, frame, inv, callee, receiverIsTracked, atom);
    }

    /**
     * RETURN out of {@code frame} under the fold link {@code f}: (1) a waiter on the owner's registered edges into
     * {@code frame}: every existing and future edge continues at its call in its caller frame, still under {@code f};
     * (2) out of the root frame also the ordinary return on {@code f.next}. The waiter takes no refusals (the registry
     * is crossings, not contents).
     */
    void returnAlongFold(RAtom atom, LocalFlowGraph frame, CallPath f) {
        ContextPolicy.FoldInfo fi = f.fold();
        foldReturns.incrementAndGet();
        EntryList<ContextPolicy.FoldEdge> list = ((Table) fi.owner).foldEdges(fi.root, frame);
        register(list, List.of("foldret", atom.key, frame, f), idx -> {
            ContextPolicy.FoldEdge e = list.get(idx);
            foldReturnDeliveries.incrementAndGet();
            List<ValueNode> invs = invokesOfCall(e.callerFrame(), e.call());
            if (invs.isEmpty()) {
                refuse(atom.table, RTrackRefusal.MISSING_IR);
                return;
            }
            for (ValueNode inv : invs) {
                enqueueWalk(atom, e.callerFrame(), inv, f, restored(e.callerMctx()));
            }
        }, null, (Consumer<RTrackRefusal>) null, atom.table);
        if (frame != fi.root && list.size() == 0) {
            // A non-root position under F always has its entering edge registered before it was enqueued; an empty
            // list would be a silent end, so it is refused by name (expected 0). Checked after the waiter is
            // registered, so an edge appended meanwhile counts.
            foldNoEdge.incrementAndGet();
            refuse(atom.table, RTrackRefusal.MISSING_IR);
        }
        if (frame == fi.root) {
            foldRootExits.incrementAndGet();
            returnCase(atom, frame, f.next, restored(fi.rootMctx));
        }
    }

    String foldCensus() {
        return " foldPushes=" + (foldPushesA.get() + foldPushesB.get() + foldPushesC.get()) + " foldA=" + foldPushesA.get() +
                        " foldB=" + foldPushesB.get() + " foldC=" + foldPushesC.get() + " foldEdges=" + foldEdgesRegistered.get() + " foldReturns=" +
                        foldReturns.get() + " foldReturnDeliveries=" + foldReturnDeliveries.get() + " foldExits=" + foldRootExits.get() +
                        " foldBackwardPathless=" + foldBackwardPathless.get() + " foldNoEdge=" + foldNoEdge.get() + " foldRoots=" + top(foldRootsBy);
    }

    List<ValueNode> invokesOfVertex(LocalFlowGraph frame, LocalFlowGraph.LocalVertex cv) {
        if (cv.irNode instanceof Invoke inv && inv.asNode() instanceof ValueNode vn && vn.graph() == graphOf(frame)) {
            return List.of(vn);
        }
        return invokesByBci(frame, cv.bci);
    }

    /** Every invoke with that bci (a bci is not guaranteed unique; the fan is the sound reading). */
    List<ValueNode> invokesByBci(LocalFlowGraph frame, int bci) {
        StructuredGraph g = graphOf(frame);
        if (g == null || bci < 0) {
            return List.of();
        }
        List<ValueNode> out = new ArrayList<>(1);
        for (Node node : g.getNodes()) {
            if (node instanceof Invoke inv && StringAnalysisChildInlining.pointsToBci(inv) == bci && node instanceof ValueNode vn) {
                out.add(vn);
            }
        }
        return out;
    }

    // ------------------------------------------------------------------
    // ESCAPE: the atom's value is the value of a store into X.m.
    // ------------------------------------------------------------------
    private void escape(RAtom atom, LocalFlowGraph frame, Node storeNode, CallPath path, MethodContext mctx) {
        markStored(atom); // before the UNRESOLVED_VALUE early returns
        if (atom.kind == AtomKind.STRING) {
            atom.strEscapes.incrementAndGet(); // a store of the string is the container's escape
        }
        if (storeNode instanceof StoreFieldNode sfn && sfn.field().isStatic()) {
            AnalysisField f = bridge.resolveField(sfn.field());
            if (f == null) {
                refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE);
                return;
            }
            escapeIntoStatic(atom, staticTable(f), f);
            return;
        }
        ValueNode receiver = storeNode instanceof StoreFieldNode sfn ? sfn.object()
                        : storeNode instanceof StoreIndexedNode sin ? sin.array() : null;
        Object member = storeNode instanceof StoreFieldNode sfn2 ? bridge.resolveField(sfn2.field()) : ARRAY_ELEMENT;
        if (receiver == null || member == null) {
            refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE);
            return;
        }
        escapeInto(atom, frame, storeNode, receiver, member, path, mctx);
    }

    /**
     * The stack-confinement flag's one setter ({@link RAtom#strStored}). Called at the top of every heap-escape route,
     * before any early return: {@link #escape}, {@link #escapeIntoStatic}, {@link #escapeInto}, {@link ClosedFieldEscape#escapeIntoKey},
     * {@link ThreadLocalModel#vmtlEscape}, {@link #buildTimeEscape} and {@code JdkModelEngine.escapeInto}.
     */
    static void markStored(RAtom atom) {
        if (atom.kind == AtomKind.STRING) {
            if (!atom.strStored) {
                atom.strStored = true;
            }
        } else if (!atom.containerStored) {
            // A container's heap event, read only by elementContainerStored (the
            // confinement flag stays STRING-only)
            atom.containerStored = true;
        }
    }

    /**
     * The fresh containers of each ARRAY-row ELEM seed's STRING atom (recorded at birth). Their pieces are stored iff such
     * an array had a heap-escape event itself ({@link #markStored} on the container atom) or a piece did. Read at emit.
     */
    private final Map<RAtomKey, Set<RAtom>> elementContainers = new ConcurrentHashMap<>();

    void elementContainer(Object strAtomKey, RAtom container) {
        if (strAtomKey instanceof RAtomKey k) {
            elementContainers.computeIfAbsent(k, x -> ConcurrentHashMap.newKeySet()).add(container);
        }
    }

    /** Some fresh array of the ARRAY-row ELEM seed atom {@code a} escaped into the heap. */
    boolean elementContainerStored(RAtom a) {
        Set<RAtom> cs = elementContainers.get(a.key);
        if (cs != null) {
            for (RAtom c : cs) {
                if (c.containerStored) {
                    return true;
                }
            }
        }
        return false;
    }

    /** ESCAPE into a static field: the continuation is at every load of the static table (inheriting its refusals). */
    private void escapeIntoStatic(RAtom atom, Table st, AnalysisField f) {
        markStored(atom);
        holderEnd.escRec(atom, List.of("static", f), EscKind.STATIC, f.format("%H.%n"), 0); // holder-end rule: holder-free (the runtime-code static table)
        EntryList<LoadEntry> list = st.loads(f);
        register(list, List.of("esc-static", atom.key), idx -> continueAt(atom, list.get(idx), f), null, atom.table);
    }

    /**
     * ESCAPE into {@code receiver.member}: resolve the receiver backward; for each receiver atom X park on the loads the
     * store's pools open in T(X), and inherit T(X)'s refusals.
     */
    void escapeInto(RAtom atom, LocalFlowGraph frame, Object storeNode, ValueNode receiver, Object member,
                    CallPath path, MethodContext mctx) {
        markStored(atom); // every caller (escape, commitEscape, ThreadLocal.set, arraycopy/clone, the models), before the fieldRule return
        if (DUMP && models.abstracted(member)) {
            System.out.println("[rtrack-dump] JDKMODEL-FIELD field-escape " + memberName(member) + " at " + frameName(frame) + " node=" + storeNode + " atom=" + atom.key);
        }
        if (models.fieldRule(atom.table, member, "field-escape")) {
            return; // the IR stores a value into a representation field
        }
        if ((atom.kind == AtomKind.STRING || isIdQuery(atom)) && member instanceof AnalysisField f && !f.isStatic()) { // also the query atoms
            List<FieldLoadSite> loads = closedField.closedFieldLoads(f);
            if (loads != null) {
                // A closed field: the identity route first, its first refusal switches to the field's load sites
                EscRec rec = holderEnd.escRec(atom, List.of("closed", f), EscKind.CLOSED, f.format("%H.%n"), loads.size());
                attach("escape", frame, receiver, mctx, path, closedField.closedFieldEscapeListener(atom, frame, storeNode, f, loads, path, rec));
                return;
            }
        }
        attach("escape", frame, receiver, mctx, path, escapeListener(atom, frame, storeNode, member, path));
    }

    // ------------------------------------------------------------------
    // The closed-field escape's and the field-held receivers' state (the rules: ClosedFieldEscape).
    // ------------------------------------------------------------------

    /** Per field: its load sites (a {@code List<FieldLoadSite>}, closed) or its {@link FieldOpen} reason. */
    final Map<AnalysisField, Object> closedFieldMemo = new ConcurrentHashMap<>();
    final AtomicLong closedFieldEscapes = new AtomicLong();
    final AtomicLong closedFieldFallbacks = new AtomicLong();
    final Map<String, Counter> closedFieldOpenBy = new ConcurrentHashMap<>();
    /** Census (print-only): per fallen-back field ("D.f loads=N"), the number of escapes that fell back to its load sites. */
    final Map<String, Counter> closedFieldFallbackSites = new ConcurrentHashMap<>();
    /** The image's IR loads of reference instance fields, built once (every framed graph; universe order). */
    volatile FieldReadIndex fieldReadIndex;
    final Object closedFieldIndexLock = new Object();

    volatile FieldWriteIndex fieldWriteIndex;
    final Object fieldWriteIndexLock = new Object();
    /** Per field: its store sites (a {@code List<FieldStoreSite>}) or the reason (a String) it is not store-closed. */
    final Map<AnalysisField, Object> fieldStoreMemo = new ConcurrentHashMap<>();

    /** The escape's listener: for each receiver atom X park on the loads the store's pools open in T(X), inherit T(X)'s refusals. */
    Listener escapeListener(RAtom atom, LocalFlowGraph frame, Object storeNode, Object member, CallPath path) {
        return escapeListener("esc", atom, frame, storeNode, member, path, null, holderEnd.escRec(atom, List.of("id", member), EscKind.IDENTITY, memberName(member), 0));
    }

    /**
     * The escape listener: for each receiver atom X, park on {@code T(X).loads(member)}. {@code fallback} null = refusal
     * inheritance (the route's refusals go to {@code atom.table}, which is also the waiters' stop target); non-null (the
     * closed field) = every refusal of the route goes to {@code fallback} instead, with no stop target.
     */
    Listener escapeListener(String tag, RAtom atom, LocalFlowGraph frame, Object storeNode, Object member, CallPath path, Consumer<RTrackRefusal> fallback,
                    EscRec rec) {
        return new Listener(List.of(tag, atom.key, storeNode, member), x -> {
            RAtom xAtom = atoms.get(x);
            if (DUMP && focused(String.valueOf(atom.key))) {
                System.out.println("[rtrack-dump] ESC-RECV atom=" + atom.key + " store=" + frameName(frame) + " " + storeNode + " member=" + memberName(member) +
                                " path=" + path + " X=" + x + " len0=" + xAtom.length0);
            }
            if (xAtom.length0 && member == ARRAY_ELEMENT) {
                counters[ContextPolicy.CIDX_LENGTH_ZERO_PROOFS]++;
                if (rec != null) {
                    rec.len0Skipped.set(true); // the one sound way to deliver no holder
                }
                return; // infeasible store (a length-0 array): no continuation
            }
            if (rec != null) {
                rec.holders.add(x); // holder-end rule: the claim "no load of member" rests on X's walk (unless holder-free)
            }
            Table xt = xAtom.table;
            // The reflective-access check at the escape itself: a reflectively/Unsafe/JNI-accessed member refuses
            // T(X) (inherited below) even when X's own forward walk never reaches the store (recordStore's check)
            checkReflectiveField(xt, member);
            EntryList<LoadEntry> list = xt.loads(member);
            Consumer<Integer> cont = idx -> continueAt(atom, list.get(idx), member);
            IntPredicate filter = idx -> xt.pools(member).connected(frame, storeNode, list.get(idx).frame(), list.get(idx).node());
            if (fallback == null) {
                register(list, List.of(tag, atom.key, frame, storeNode), cont, filter, atom.table);
            } else {
                register(list, List.of(tag, atom.key, frame, storeNode), cont, filter, fallback, null, atom.table);
            }
        }, fallback == null ? r -> refuse(atom.table, r) : fallback, fallback == null ? atom.table : null, atom.table); // (the escape feeds T(atom) either way)
    }

    /**
     * "Continue at a load": the position is the load node itself, with the load entry's path. A desugared load (a copy
     * or clone) continues by escaping into the copy's destination / the clone object's same member.
     */
    void continueAt(RAtom atom, LoadEntry l, Object member) {
        if (atom.kind == AtomKind.STRING) {
            atom.wiredAnyLoad = true; // an escape waiter delivered a load entry
        }
        MethodContext lm = l.mctx() instanceof MethodContext mc ? mc : MethodContext.UNKNOWN;
        if (models.loadArrival(atom, l, lm)) {
            return; // a model load (its mark says what the loaded value is)
        }
        if (l.node() instanceof BasicArrayCopyNode acn) {
            if (acn.getDestination() == null) {
                refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE);
                return;
            }
            escapeInto(atom, l.frame(), acn, acn.getDestination(), ARRAY_ELEMENT, l.path(), lm);
            return;
        }
        if (l.node() instanceof ObjectClone && l.node() instanceof ValueNode cloneNode) {
            escapeInto(atom, l.frame(), cloneNode, cloneNode, member, l.path(), lm);
            return;
        }
        if (!(l.node() instanceof ValueNode vn)) {
            refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE);
            return;
        }
        enqueueWalk(atom, l.frame(), vn, l.path(), lm);
    }

    /** Register a waiter whose refusals go to {@code target} (a table or a sink): refusal inheritance. */
    boolean register(EntryList<?> on, Object key, Consumer<Integer> continuation, IntPredicate filter,
                    ContainerTables.Refusable target) {
        return register(on, key, continuation, filter, r -> {
            if (DUMP) {
                walkPos.set("INHERITED from table " + on.table.owner + " via " + on.kind + " {tableFirst=" + refusalOrigin.get(on.table) + "}");
                // Print-only, DUMP only: the edge label carries the waiter's key
                // (who parked on this list, at which store/frame) so a PROV hop names the connecting edge
                inheriting(on.table, on.kind + "|" + dumpKey(key), () -> refuseAny(target, r));
                return;
            }
            refuseAny(target, r);
        }, target);
    }

    void refuseAny(ContainerTables.Refusable target, RTrackRefusal r) {
        if (target instanceof Table t) {
            refuse(t, r);
        } else if (target instanceof Sink s) {
            refuse(s, r);
        }
    }

    boolean register(EntryList<?> on, Object key, Consumer<Integer> continuation, IntPredicate filter,
                    Consumer<RTrackRefusal> onRefusal, ContainerTables.Refusable target) {
        return register(on, key, continuation, filter, onRefusal, target, target);
    }

    /**
     * {@code depTarget}: the object the continuation feeds (ID-DEP travels to it along this
     * waiter); the refusal target when there is one, given explicitly for the waiters whose refusals run a fallback.
     */
    boolean register(EntryList<?> on, Object key, Consumer<Integer> continuation, IntPredicate filter,
                    Consumer<RTrackRefusal> onRefusal, ContainerTables.Refusable target, ContainerTables.Refusable depTarget) {
        Waiter w = new Waiter(key, idx -> {
            if (target instanceof Table t && t.stopVisible() || target instanceof Sink sk && sk.stopVisible()) {
                noteSkipped();
                return;
            }
            censusDeliveries.incrementAndGet();
            continuation.accept(idx);
        }, filter, onRefusal, target, depTarget);
        boolean fresh = on.register(w);
        if (fresh) {
            censusWaiters.incrementAndGet();
            if (key instanceof List<?> kl && !kl.isEmpty()) {
                bump(waitersByKind, String.valueOf(kl.get(0)));
            }
        }
        return fresh;
    }

    // ------------------------------------------------------------------
    // The invoke crossing: dispatch via the engine's existing
    // resolution (its dispatch filters), into the callee's ParameterNodes.
    // ------------------------------------------------------------------
    private void invokeUsage(RAtom atom, LocalFlowGraph frame, ValueNode n, MethodCallTargetNode ct, CallPath path,
                    MethodContext mctx) {
        Invoke inv = ct.invoke();
        if (inv == null || ct.targetMethod() == null) {
            refuse(atom.table, RTrackRefusal.NO_TARGET);
            return;
        }
        if (strSites != null && concatCrossing(atom, frame, n, ct, inv, path, mctx)) {
            return; // a recognised makeConcat-family concat, or an unrecognised one (refused)
        }
        boolean str = atom.kind == AtomKind.STRING;
        boolean staticCall = ct.targetMethod().isStatic();
        LocalFlowGraph.LocalVertex callVertex = callVertexOf(frame, inv);
        boolean receiverPosition = !staticCall && !ct.arguments().isEmpty() && ct.arguments().get(0) == n;
        // String.concat(String) (f4): its argument (slot 1) is a concat operand, never entered
        boolean f4 = str && StringAtoms.isStringConcat(ct.targetMethod());
        SugVertex phaseA = str ? strSites.phaseACallSite(frame, inv) : null;
        // The equals-argument terminal needs a Phase-A key the parent computes too; an invoke
        // from a parse-time-inlined scope is keyed on the root method and bci, the parent on the inlinee: no site
        boolean eqArgSite = phaseA != null && !StringAnalysisChildInlining.isFromInlinedScope(inv);
        // The argument terminal also needs a vertex the redirect rule marks (EqualsMatrixHeuristic)
        boolean eqRedirectSite = eqArgSite && EqualsMatrixHeuristic.redirectableArgSite(phaseA, false);
        boolean cmpRedirectSite = eqArgSite && EqualsMatrixHeuristic.redirectableArgSite(phaseA, true);
        if (str) {
            stringCallAdapter(atom, frame, n, ct, inv, receiverPosition, phaseA, f4);
        }
        List<DispatchResolution.ResolvedTarget> targets = targetsOf(frame, callVertex, receiverPosition ? Crossing.RECEIVER : Crossing.ARGUMENT, atomSiteBlock(atom));
        if (receiverPosition && targets.size() > 1) {
            List<DispatchResolution.ResolvedTarget> exact = exactReceiverTargetsOf(atom, ct.targetMethod(), targets);
            if (exact != null) {
                exactRecvNarrowed.incrementAndGet();
                targets = exact;
            }
        }
        if (DUMP && focused(String.valueOf(atom.key))) {
            StringBuilder tn = new StringBuilder();
            for (int i = 0; i < targets.size() && i < 6; i++) {
                tn.append(i == 0 ? "" : ",").append(targets.get(i).method().format("%H.%n"));
            }
            System.out.println("[rtrack-dump] CROSS atom=" + atom.key + " at " + frameName(frame) + "@" + inv.bci() + " callee=" +
                            ct.targetMethod().format("%H.%n") + " recvPos=" + receiverPosition + " lfgVertex=" + (lfgVertex(frame, inv.asNode()) != null) +
                            " argStamp=" + callVertex.argStamp + " targets=" + targets.size() + " [" + tn + (targets.size() > 6 ? ",…" : "") + "]");
        }
        if (targets.isEmpty()) {
            noTarget(callVertex, ct.targetMethod(), "fwd");
            refuse(atom.table, RTrackRefusal.NO_TARGET);
            return;
        }
        if (targets.size() > CHA_CAP && models.collapsedCount(targets) > CHA_CAP) {
            refuse(atom.table, RTrackRefusal.CHA_FAN_CAP);
            return;
        }
        CallPath pushed = CallPath.push(frame, callVertex, mctx, path);
        Set<String> jdkApplied = null; // the collapse keys applied at this crossing
        // Builder-append mirror: the mirrorable site of this invoke (AppendMirror.mirrorSite), computed once
        boolean mirrorOn = str && AppendMirror.on();
        SugVertex mirrorV = mirrorOn ? AppendMirror.mirrorSite(phaseA, inv) : null;
        for (DispatchResolution.ResolvedTarget t : targets) {
            if (mirrorOn && mirrorArgument(atom, ct, n, t.method(), mirrorV)) {
                continue; // the string slot of a builder entry point: terminal at the mirrored site, or refused; never entered
            }
            TargetCheck tc = targetCheck(t.method()); // the shared per-target rules
            if (tc.rule() == TargetRule.THREAD_LOCAL) {
                // A translated thread-local operation: never entered
                threadLocal.tlInvokeUsage(atom, frame, n, ct, inv, callVertex, tc.tl(), path, mctx, pushed);
                continue;
            }
            if (tc.rule() == TargetRule.MODEL && !(receiverPosition && StringAtoms.isTerminalTarget(t.method()))) {
                // A modelled JDK target: never entered; targets with one collapse key are one application.
                // Never for the receiver of a terminal target (a stringy class's instance method: the
                // AbstractStringBuilder.append model covers the string argument): the terminal rule / the IR below
                jdkApplied = jdkApplied != null ? jdkApplied : new java.util.HashSet<>();
                if (models.firstOfKey(jdkApplied, tc.op())) {
                    models.invokeUsage(atom, frame, n, ct, inv, t.method(), tc.op(), path, mctx, pushed, 0);
                }
                continue;
            }
            if (tc.rule() == TargetRule.CLOSED) {
                models.refuseUnlisted(atom.table, tc.closed(), t.method(), "fwd");
                continue;
            }
            // MonitorPrimitive: at a monitor operation the object slot is an observation, never entered;
            // any other slot holding the atom (the MonitorSupport singleton, doRelockObject's lock data) is entered below
            boolean monitorOp = tc.rule() == TargetRule.MONITOR;
            if (monitorOp) {
                boolean other = false;
                for (int slot = 0; slot < ct.arguments().size(); slot++) {
                    if (ct.arguments().get(slot) == n) {
                        if (slot == MonitorPrimitive.OBJECT_SLOT) {
                            monitorObservations.incrementAndGet();
                            monitorObservationsBy.computeIfAbsent(java.util.Arrays.asList(t.method(), frame), x -> new Counter()).incrementAndGet();
                        } else {
                            other = true;
                        }
                    }
                }
                if (isLiteralAtom(atom) && !other) {
                    refuse(atom.table, RTrackRefusal.LITERAL_IDENTITY); // a monitor on the literal
                    continue;
                }
                if (!other) {
                    silentEnd(atom, frame, inv.asNode(), "monitor-obs:" + t.method().format("%H.%n"));
                    continue;
                }
            }
            // Slot 0 of a call into a stringy-declared resolved target is a TERMINAL usage of a STRING
            // atom: the body is not entered; the other slots holding the string are (the self-argument rule)
            boolean terminal = str && receiverPosition && StringAtoms.isTerminalTarget(t.method());
            boolean flatEnter = false;
            if (terminal) {
                stringTerminal(atom, frame, n, inv, callVertex, t.method(), phaseA, f4, path, mctx);
                cmpBridgeReceiver(atom, frame, inv.asNode(), n, t.method());
                flatEnter = flatHandOffEnters(atom, t.method());
                if (!flatEnter && !otherSlotHolds(ct, n, f4)) {
                    continue;
                }
            }
            LocalFlowGraph calleeFrame = bridge.frameOf(t.method());
            StructuredGraph g = calleeFrame != null ? graphOf(calleeFrame) : null;
            if (calleeFrame == null && dropDeadTarget(t.method(), "fwd")) {
                silentEnd(atom, frame, inv.asNode(), "dead-target:" + t.method().format("%H.%n"));
                continue;
            }
            if (calleeFrame == null || g == null) {
                missingIr("fwd-callee" + (calleeFrame == null ? "/noLfg/" : "/noGraph/"), t.method());
                if (DUMP && focused(String.valueOf(atom.key))) {
                    System.out.println("[rtrack-dump] MISSING-IR-CALLEE atom=" + atom.key + " at " + frameName(frame) + " callee=" +
                                    t.method().format("%H.%n(%p)") + (calleeFrame == null ? " (no LFG frame)" : " (no graph)"));
                }
                refuse(atom.table, RTrackRefusal.MISSING_IR);
                continue;
            }
            ContextPolicy.FoldPush fp = null; // recursion fold: this target's folding push (computed at the first entered slot)
            boolean fpDone = false;
            for (int slot = 0; slot < ct.arguments().size(); slot++) {
                if (ct.arguments().get(slot) != n) {
                    continue;
                }
                if (monitorOp && slot == MonitorPrimitive.OBJECT_SLOT) {
                    continue; // the monitor operation's object slot (counted above)
                }
                if (flatSlotRow(slot, terminal, flatEnter, f4) != StringAtoms.SlotRow.ENTER) {
                    continue; // the terminal's receiver slot / the String.concat operand (recorded by stringCallAdapter)
                }
                StringAtoms.EqArgRow eqRow = StringAtoms.equalsArgRow(str, slot, StringAtoms.isStringEquals(t.method()), eqRedirectSite);
                if (eqRow == StringAtoms.EqArgRow.NO_SITE && eqArgSite) {
                    argSiteNotRedirectable.incrementAndGet(); // a Phase-A vertex the redirect rule would not mark
                }
                if (eqRow == StringAtoms.EqArgRow.TERMINAL) {
                    eqArgTerminals.incrementAndGet(); // the PARAMETER usage at the Phase-A site (stringCallAdapter)
                    continue;
                }
                if (eqRow == StringAtoms.EqArgRow.NO_SITE) {
                    eqArgNoSite.incrementAndGet(); // no SUG site the equals matrix could redirect
                    refuse(atom.table, RTrackRefusal.EQUALS_ARG_NO_SITE);
                    continue;
                }
                if (StringAtoms.jmhBlackholeSinkSlot(StringAtoms.JMH_BLACKHOLE_SINK, str, slot, t.method().isStatic(), StringAtoms.isJmhBlackholeSink(t.method()))) {
                    // Knob sink.jmhblackhole (see StringAtoms.JMH_BLACKHOLE_SINK): the JMH Blackhole's Object
                    // argument is a terminal PARAMETER usage at the target's site (positive evidence through
                    // TransferFacts.isSafeSinkMethod); the Blackhole body (consumeFull's WeakReference store into obj1) is not entered
                    jmhBlackholeSinks.incrementAndGet();
                    strUsage(atom, frame, inv.asNode(), n, strSites.targetSite(frame, callVertex, t.method()), UsageRole.PARAMETER, slot);
                    continue;
                }
                if (eqArgSite && !cmpRedirectSite && StringAtoms.compareToArgRow(str, slot,
                                StringAtoms.isStringCompareToString(t.method()), StringAtoms.isStringCompareToBridge(t.method()), true) == StringAtoms.CmpArgRow.TERMINAL) {
                    argSiteNotRedirectable.incrementAndGet(); // a Phase-A vertex the redirect rule would not mark
                }
                if (cmpArgument(atom, frame, inv.asNode(), n, t.method(), str, slot, cmpRedirectSite)) {
                    continue; // site-keyed: recorded at the redirectable site or refused; never entered
                }
                boolean receiverSlot = receiverPosition && slot == 0 && !t.method().isStatic();
                ParameterNode param = receiverSlot ? null : g.getParameter(slot);
                if (!receiverSlot && param == null) {
                    // An argument the callee never reads (no ParameterNode): nothing can flow.
                    silentEnd(atom, frame, inv.asNode(), "unread-param:" + t.method().format("%H.%n") + "#" + slot);
                    continue;
                }
                if (!fpDone) {
                    fp = foldedPush(atom, frame, callVertex, mctx, path, calleeFrame);
                    fpDone = true;
                }
                CallPath tpushed = fp != null ? fp.path() : pushed;
                if (receiverSlot) {
                    enterReceiver(atom, calleeFrame, g, tpushed, enterMaybeFolded(fp, mctx, frame, inv, t.method(), true, atom));
                    continue;
                }
                enqueueWalk(atom, calleeFrame, param, tpushed, enterMaybeFolded(fp, mctx, frame, inv, t.method(), false, atom));
            }
        }
    }

    /**
     * Builder-append mirror ({@link StringAtoms#mirrorArgRow}): the row of the resolved target {@code t} for the STRING
     * atom {@code n} in the entry's string slot. TERMINAL: the PARAMETER usage at the mirrorable site was recorded by the
     * adapter ({@link AppendMirror#recordTerminal}); NO_SITE: refused {@code MIRROR_ARG_NO_SITE}. Returns true when the
     * target is consumed (never entered); NONE returns false (the ordinary rules). The atom can sit in no other slot of
     * an entry (the receiver is a builder, the remaining parameters are ints).
     */
    private boolean mirrorArgument(RAtom atom, MethodCallTargetNode ct, ValueNode n, AnalysisMethod t, SugVertex mirrorV) {
        int entrySlot = AppendMirror.stringSlot(t);
        if (entrySlot < 0 || entrySlot >= ct.arguments().size() || ct.arguments().get(entrySlot) != n) {
            return false;
        }
        switch (StringAtoms.mirrorArgRow(true, atom.kind == AtomKind.STRING, entrySlot, entrySlot, mirrorV != null)) {
            case TERMINAL:
                AppendMirror.recordTerminal(mirrorV, ct.targetMethod());
                return true;
            case NO_SITE:
                AppendMirror.recordNoSite(t);
                refuse(atom.table, RTrackRefusal.MIRROR_ARG_NO_SITE);
                return true;
            default:
                return false;
        }
    }

    final Counter flatHandOffEntries = new Counter();

    /**
     * Flat delivery gate: the walk enters the hand-off body only when no value-null kind the atom is also seeded for
     * (SV: {@link StringViewWhitelist}, LC: {@link LazyConcatWhitelist}) whitelists the member: then that kind's verdict
     * already rejects at the terminal, so the entered body cannot change it (an SB-only seed always enters). A hand-off
     * that stays undelivered is recorded per member ({@link #FLAT_UNDELIVERED}); the profile carries the members for the
     * admitted SINGLE_BYTE seeds ({@link #flatUndeliveredProfileLines}) so a consumer that needs complete flat delivery
     * (the type-check IC's flat closure) can restrict its conservative rule to exactly them.
     */
    static boolean flatHandOffGate(String heuristics, String declaringClass, String name, String signature) {
        java.util.List<String> hs = java.util.Arrays.asList(heuristics.split("\\+"));
        if (!hs.contains("SB")) {
            return false;
        }
        if (hs.contains("SV") && StringViewWhitelist.isWhitelistedUsage(name, declaringClass, signature)) {
            return false;
        }
        return !(hs.contains("LC") && LazyConcatWhitelist.isWhitelisted(name, declaringClass, signature));
    }

    /** Undelivered flat hand-offs: member {@code name(signature)} to the SB seed sites whose walk did not enter it. */
    static final Map<String, Set<String>> FLAT_UNDELIVERED = new java.util.concurrent.ConcurrentHashMap<>();
    final Counter flatHandOffUndelivered = new Counter();

    /** {@link #flatHandOffDecision}: not a flat hand-off of an SB seed (the terminal stays a terminal, nothing recorded). */
    static final int FH_NONE = 0;
    /** {@link #flatHandOffDecision}: the walk enters the hand-off body at the receiver. */
    static final int FH_ENTER = 1;
    /** {@link #flatHandOffDecision}: an SB seed's hand-off the gate does not enter (recorded in {@link #FLAT_UNDELIVERED}). */
    static final int FH_UNDELIVERED = 2;

    /**
     * The walk-side decision of {@link #flatHandOffEnters}, pure: only an SB seed at a flat hand-off is considered; the
     * gate ({@link #flatHandOffGate}) then decides between entering and recording it as undelivered.
     */
    static int flatHandOffDecision(String heuristics, String declaringClass, String name, String signature) {
        if (heuristics == null || declaringClass == null || !java.util.Arrays.asList(heuristics.split("\\+")).contains("SB") ||
                        !StringTerminalHandList.isFlatHandOff(declaringClass, name, signature) || sbsDeclares(name, signature)) {
            return FH_NONE;
        }
        return flatHandOffGate(heuristics, declaringClass, name, signature) ? FH_ENTER : FH_UNDELIVERED;
    }

    /**
     * A String member the SB rep class itself declares (the JVM's selection {@link TerminalBodyKinds#selectedDeclaration})
     * is not a flat hand-off for an SB seed: the rep's own body runs, and {@code RepEscapeTest} pins that no rep body
     * hands {@code this} to non-rep code or runs an inherited String body on it. So the walk does not enter String's body
     * there and nothing is recorded as undelivered (pinned by {@code SingleByteHandOffClosureTest}).
     */
    static boolean sbsDeclares(String name, String signature) {
        return SBS_DECLARES.computeIfAbsent(name + "(" + signature + ")", k -> {
            Class<?> sbs = InlineCacheRegistry.getRepClass("SBS");
            for (java.lang.reflect.Method m : String.class.getDeclaredMethods()) {
                if (m.getName().equals(name) && !java.lang.reflect.Modifier.isStatic(m.getModifiers()) && TerminalBodyKinds.usageSignature(m).equals(signature)) {
                    java.lang.reflect.Method d = TerminalBodyKinds.selectedDeclaration(sbs, m);
                    return d != null && d.getDeclaringClass() != String.class;
                }
            }
            return false;
        });
    }

    private static final Map<String, Boolean> SBS_DECLARES = new java.util.concurrent.ConcurrentHashMap<>();

    /**
     * The slot row at a call target: a terminal's receiver slot is entered (not a terminal) exactly when the flat
     * hand-off decision entered it; every other slot follows {@link StringAtoms#invokeSlotRow}.
     */
    static StringAtoms.SlotRow flatSlotRow(int slot, boolean terminal, boolean flatEnter, boolean f4) {
        return StringAtoms.invokeSlotRow(slot, terminal && !(flatEnter && slot == 0), f4);
    }

    /**
     * Flat delivery: at a flat hand-off terminal
     * ({@link StringTerminalHandList#isFlatHandOff}) of an atom that may become a value-carrying rep (an SB seed), the
     * walk also enters the String body at its receiver, after recording the terminal usage. The body hands {@code this}
     * to walked code or returns it in a container, so the downstream sites get the atom's receiver tags and their
     * INLINE_CACHE (and EQUALS_MATRIX) entries list the flat kind; a rejecting usage there rejects it too.
     */
    private boolean flatHandOffEnters(RAtom atom, AnalysisMethod t) {
        if (atom.seed == null || atom.seed.heuristics == null || t.getDeclaringClass() == null) {
            return false;
        }
        String cls = t.getDeclaringClass().toJavaName(true);
        String sig = SiteKeys.formatSignature(t);
        int d = flatHandOffDecision(atom.seed.heuristics, cls, t.getName(), sig);
        if (d == FH_NONE) {
            return false;
        }
        if (d == FH_UNDELIVERED) {
            flatHandOffUndelivered.incrementAndGet();
            FLAT_UNDELIVERED.computeIfAbsent(t.getName() + "(" + sig + ")", k -> java.util.concurrent.ConcurrentHashMap.newKeySet())
                            .add(String.valueOf(atom.seed.vertex.getSourceLocation()));
            return false;
        }
        flatHandOffEntries.incrementAndGet();
        return true;
    }

    /**
     * The profile comment lines {@code # FLAT_HANDOFF_UNDELIVERED <member> <n>} (n = the admitted SINGLE_BYTE seeds whose
     * walk did not enter that hand-off), sorted, and the census line; the loader skips comment lines.
     */
    static List<String> flatUndeliveredProfileLines(Set<String> admittedSbSites) {
        List<String> out = new ArrayList<>();
        for (Map.Entry<String, Set<String>> e : new java.util.TreeMap<>(FLAT_UNDELIVERED).entrySet()) {
            long n = e.getValue().stream().filter(admittedSbSites::contains).count();
            if (n > 0) {
                out.add("# FLAT_HANDOFF_UNDELIVERED " + e.getKey() + " " + n);
            }
        }
        return out;
    }

    static String flatUndeliveredCensus() {
        StringBuilder sb = new StringBuilder("[sug-flat-handoff] undelivered members=");
        new java.util.TreeMap<>(FLAT_UNDELIVERED).forEach((k, v) -> sb.append(' ').append(k).append('=').append(v.size()));
        return sb.toString();
    }

    /** Does a slot other than the terminal's receiver slot (and the String.concat operand) hold {@code n}? */
    private static boolean otherSlotHolds(MethodCallTargetNode ct, ValueNode n, boolean f4) {
        for (int slot = 1; slot < ct.arguments().size(); slot++) {
            if (ct.arguments().get(slot) == n && StringAtoms.invokeSlotRow(slot, true, f4) == StringAtoms.SlotRow.ENTER) {
                return true;
            }
        }
        return false;
    }

    /**
     * The interface adapter: a Phase-A usage site at the call records the usage the string walk recorded there: RECEIVER
     * at the receiver slot, a PARAMETER usage (with the slot) at an argument slot; at {@code a.concat(b)} the operand
     * usages on the CONCAT_EXPRESSION site.
     */
    private void stringCallAdapter(RAtom atom, LocalFlowGraph frame, ValueNode n, MethodCallTargetNode ct, Invoke inv, boolean receiverPosition,
                    SugVertex phaseA, boolean f4) {
        ValueNode anchor = inv.asNode();
        for (int slot = 0; slot < ct.arguments().size(); slot++) {
            if (ct.arguments().get(slot) != n) {
                continue;
            }
            if (f4 && slot <= 1) {
                strConcatOperands.incrementAndGet();
                strUsage(atom, frame, anchor, n, strSites.concatSite(frame, inv), UsageRole.NONE, slot);
            }
            if (phaseA != null) {
                boolean recv = receiverPosition && slot == 0 || SugNameTables.isStrictClassCheckName(phaseA.getMethodName(), phaseA.getDeclaringClass());
                strPhaseAUsages.incrementAndGet();
                // The tracked accumulator as the receiver: recorded as the accumulator's own method
                String owner = receiverPosition && slot == 0 ? accDispatchOwner(atom, phaseA, ct.targetMethod()) : null;
                strUsage(atom, frame, anchor, n, phaseA, recv ? UsageRole.RECEIVER : UsageRole.PARAMETER, recv ? -1 : slot, owner);
            }
        }
    }

    /**
     * The compareTo mirror: the compareTo argument row of one slot ({@link StringAtoms#compareToArgRow}). TERMINAL: the
     * PARAMETER usage at the call's Phase-A site was recorded by the adapter; BRIDGE: recorded at the bridge's internal
     * site ({@link #cmpBridgeSite}) or refused when it has none; NO_SITE: refused {@code COMPARETO_ARG_NO_SITE}. Returns
     * true when the slot is consumed. {@code hasPhaseASite} must mean a redirectable site
     * ({@link EqualsMatrixHeuristic#redirectableArgSite}; the callers check it).
     */
    boolean cmpArgument(RAtom atom, LocalFlowGraph frame, Node anchor, ValueNode n, AnalysisMethod t, boolean str, int slot, boolean hasPhaseASite) {
        StringAtoms.CmpArgRow row = StringAtoms.compareToArgRow(str, slot, StringAtoms.isStringCompareToString(t),
                        StringAtoms.isStringCompareToBridge(t), hasPhaseASite);
        switch (row) {
            case NONE:
                return false;
            case TERMINAL:
                cmpArgTerminals.incrementAndGet();
                return true;
            case BRIDGE: {
                SugVertex bs = cmpBridgeSite(t);
                if (bs != null) {
                    cmpArgTerminals.incrementAndGet();
                    cmpArgBridge.incrementAndGet();
                    strUsage(atom, frame, anchor, n, bs, UsageRole.PARAMETER, 1);
                    return true;
                }
                break;
            }
            default:
                break;
        }
        cmpArgNoSite.incrementAndGet();
        refuse(atom.table, RTrackRefusal.COMPARETO_ARG_NO_SITE);
        return true;
    }

    /**
     * The compareTo mirror: a STRING receiver of the bridge {@code String.compareTo(Object)} is also recorded as the
     * RECEIVER at the bridge's internal {@code compareTo(String)} site (the call the receiver really makes), where the
     * cross-rep compareTo conflict pass reads it (the tags also subject the bridge site to the receiver-family cap
     * {@code orch.maxreceiverreps}).
     */
    void cmpBridgeReceiver(RAtom atom, LocalFlowGraph frame, Node anchor, ValueNode n, AnalysisMethod t) {
        if (atom.kind != AtomKind.STRING || !StringAtoms.isStringCompareToBridge(t)) {
            return;
        }
        SugVertex bs = cmpBridgeSite(t);
        if (bs != null) {
            cmpBridgeRecv.incrementAndGet();
            strUsage(atom, frame, anchor, n, bs, UsageRole.RECEIVER, -1);
        }
    }

    private final Map<AnalysisMethod, java.util.Optional<SugVertex>> cmpBridgeSites = new ConcurrentHashMap<>();

    /**
     * The compareTo mirror: the Phase-A vertex of the bridge's own {@code invokevirtual compareTo(String)}, the one site
     * every generic {@code Comparable} caller funnels into. Null (the argument is refused) when the bridge has no frame
     * or graph, the invoke is not unique, comes from an inlined scope, or has no Phase-A vertex.
     */
    SugVertex cmpBridgeSite(AnalysisMethod bridgeMethod) {
        return cmpBridgeSites.computeIfAbsent(bridgeMethod, m -> {
            LocalFlowGraph f = bridge.frameOf(m);
            StructuredGraph g = f != null ? graphOf(f) : null;
            if (g == null) {
                return java.util.Optional.empty();
            }
            SugVertex found = null;
            for (Invoke inv : g.getInvokes()) {
                if (inv.callTarget() != null && StringAtoms.isStringCompareToString(inv.callTarget().targetMethod())) {
                    SugVertex v = StringAnalysisChildInlining.isFromInlinedScope(inv) ? null : strSites.phaseACallSite(f, inv);
                    if (v == null || found != null) {
                        return java.util.Optional.empty();
                    }
                    found = v;
                }
            }
            return java.util.Optional.ofNullable(found);
        }).orElse(null);
    }

    /**
     * The terminal usage at slot 0 (the Phase-A site's RECEIVER usage, else the resolved target's usage site) and, for a
     * hand-list terminal that may return {@code this}, the walk continues at the call's result.
     */
    void stringTerminal(RAtom atom, LocalFlowGraph frame, ValueNode n, Invoke inv, LocalFlowGraph.LocalVertex callVertex, AnalysisMethod t,
                    SugVertex phaseA, boolean f4, CallPath path, MethodContext mctx) {
        strTerminals.incrementAndGet();
        if (phaseA == null) {
            SugVertex ts = strSites.targetSite(frame, callVertex, t);
            // As in the adapter (the resolved target's site; dispatched on the declared method)
            strUsage(atom, frame, inv.asNode(), n, ts, UsageRole.RECEIVER, -1, accDispatchOwner(atom, ts, inv.callTarget().targetMethod()));
        }
        if (StringAtoms.continuesAtResult(t)) {
            strListContinuations.incrementAndGet();
            enqueueWalk(atom, frame, inv.asNode(), path, mctx);
        }
    }

    // ------------------------------------------------------------------
    // The concat as a terminal; the desugared implicit toString() and its synthetic result.
    // ------------------------------------------------------------------
    /**
     * The desugared implicit call {@code operand.toString()} of a recognised concat, as a call-path link (no IR invoke
     * is behind it). A return along a link whose top is this call arrives at the synthetic node
     * {@code ConcatOperand(concat, k)}.
     */
    static final class DesugaredCall {
        final LocalFlowGraph frame;
        final Invoke concat;
        final int operand;
        final LocalFlowGraph.LocalVertex descriptor;

        DesugaredCall(LocalFlowGraph frame, Invoke concat, int operand, LocalFlowGraph.LocalVertex descriptor) {
            this.frame = frame;
            this.concat = concat;
            this.operand = operand;
            this.descriptor = descriptor;
        }

        ValueNode operandNode() {
            var args = concat.callTarget().arguments();
            return operand < args.size() ? args.get(operand) : null;
        }

        @Override
        public String toString() {
            return "desugared-toString[" + concat.bci() + "#" + operand + "]";
        }
    }

    private final Map<List<Object>, DesugaredCall> desugaredCalls = new ConcurrentHashMap<>();
    private final Map<List<Object>, List<DispatchResolution.ResolvedTarget>> desugaredMemo = new ConcurrentHashMap<>();

    private DesugaredCall desugaredCall(LocalFlowGraph frame, Invoke inv, int k) {
        return desugaredCalls.computeIfAbsent(List.of(new NodeId(inv.asNode()), k), key -> {
            LocalFlowGraph.LocalVertex d = new LocalFlowGraph.LocalVertex(frame, -1, LocalFlowGraph.VertexKind.INVOKE_CALLSITE);
            d.bci = StringAnalysisChildInlining.pointsToBci(inv);
            d.calleeMethod = strSites.objectToString();
            d.label = "desugared-toString";
            return new DesugaredCall(frame, inv, k, d);
        });
    }

    /**
     * The walked value is an argument of an invoke at a {@code StringConcatFactory} indy site: a String-declared operand
     * slot gets the operand usage (STRING atoms), a non-String reference operand gets the desugared {@code n.toString()}
     * crossing; the appendix slot is the ordinary crossing. An unrecognised SCF site is refused by name. Returns false
     * when nothing of the call was handled here.
     */
    private boolean concatCrossing(RAtom atom, LocalFlowGraph frame, ValueNode n, MethodCallTargetNode ct, Invoke inv, CallPath path, MethodContext mctx) {
        StringAtoms.Concat c = strSites.concatAt(frame, inv);
        if (c == null || c.kind() == StringAtoms.ConcatKind.NONE) {
            return false;
        }
        if (c.kind() == StringAtoms.ConcatKind.TYPESWITCH) {
            return typeSwitchCrossing(atom, frame, n, ct, inv);
        }
        if (atom.kind != AtomKind.STRING) {
            // Print-only census: a container atom at a recognised (or refused) concat site
            containerConcatCrossings.incrementAndGet();
            containerConcatSites.add(atom.key + " at " + frameName(frame) + "@" + inv.bci() + " " + c.kind());
        }
        RTrackRefusal unrecognised = StringAtoms.concatRefusal(c);
        if (unrecognised != null) {
            strConcatUnrecognised.incrementAndGet();
            refuse(atom.table, unrecognised);
            return true;
        }
        boolean appendix = false;
        for (int slot = 0; slot < ct.arguments().size(); slot++) {
            if (ct.arguments().get(slot) != n) {
                continue;
            }
            switch (StringAtoms.concatSlot(c, slot, atom.kind == AtomKind.STRING)) {
                case APPENDIX -> appendix = true;
                case OPERAND_USAGE -> concatOperandUsage(atom, frame, inv, slot, n);
                case DESUGARED_TO_STRING -> desugaredToString(atom, frame, inv, slot, c.operandTypes()[slot], n, path, mctx);
                case NOTHING -> {
                }
            }
        }
        return !appendix;
    }

    /** Print-only: STRING-atom selectors crossed by the typeSwitch model. */
    final Counter strTypeSwitchSelectors = new Counter();

    /**
     * The typeSwitch model ({@link StringAtoms#TYPESWITCH}): a STRING atom in the selector slot 0 of a modelled
     * {@code SwitchBootstraps.typeSwitch} site is only null-tested and instanceof-tested against rep-invariant Class
     * labels: no usage, no escape, the generated switch is not entered (a silent end). Any other slot and every container
     * atom take the ordinary crossing (returns false).
     */
    private boolean typeSwitchCrossing(RAtom atom, LocalFlowGraph frame, ValueNode n, MethodCallTargetNode ct, Invoke inv) {
        if (atom.kind != AtomKind.STRING) {
            return false;
        }
        for (int slot = 1; slot < ct.arguments().size(); slot++) {
            if (ct.arguments().get(slot) == n) {
                return false;
            }
        }
        if (ct.arguments().isEmpty() || ct.arguments().get(0) != n) {
            return false;
        }
        strTypeSwitchSelectors.incrementAndGet();
        silentEnd(atom, frame, inv.asNode(), "typeswitch-selector");
        return true;
    }

    /** The usage "argument of the concat": role NONE, operand index k, on the CONCAT_EXPRESSION site. */
    private void concatOperandUsage(RAtom atom, LocalFlowGraph frame, Invoke inv, int k, ValueNode observed) {
        strConcatOperands.incrementAndGet();
        strUsage(atom, frame, inv.asNode(), observed, strSites.concatSite(frame, inv), UsageRole.NONE, k);
    }

    /**
     * The desugared receiver call {@code o.toString()} at the concat, dispatched and walked by the ordinary rules (a
     * String's toString is the listed terminal whose result, {@code ConcatOperand}, gets the operand usage).
     */
    private void desugaredToString(RAtom atom, LocalFlowGraph frame, Invoke inv, int k, AnalysisType operandType, ValueNode n, CallPath path, MethodContext mctx) {
        strConcatDesugared.incrementAndGet();
        DesugaredCall dc = desugaredCall(frame, inv, k);
        List<DispatchResolution.ResolvedTarget> targets = desugaredTargets(dc, operandType, atomSiteBlock(atom));
        if (targets == null) {
            refuse(atom.table, StringAtoms.desugaredTargetRefusal(-1, CHA_CAP)); // UNRESOLVED_VALUE
            return;
        }
        if (targets.size() > 1) {
            List<DispatchResolution.ResolvedTarget> exact = exactReceiverTargetsOf(atom, strSites.objectToString(), targets);
            if (exact != null) {
                exactRecvNarrowed.incrementAndGet();
                targets = exact;
            }
        }
        RTrackRefusal targetRefusal = StringAtoms.desugaredTargetRefusal(targets.size(), CHA_CAP);
        if (targetRefusal != null) {
            refuse(atom.table, targetRefusal); // NO_TARGET / CHA_FAN_CAP
            return;
        }
        CallPath pushed = CallPath.push(frame, dc, mctx, path);
        for (DispatchResolution.ResolvedTarget t : targets) {
            AnalysisMethod m = t.method();
            if (atom.kind == AtomKind.STRING && StringAtoms.isTerminalTarget(m)) {
                strTerminals.incrementAndGet();
                strUsage(atom, frame, inv.asNode(), n, strSites.targetSite(frame, dc.descriptor, m), UsageRole.RECEIVER, -1);
                if (StringAtoms.continuesAtResult(m)) {
                    concatOperandUsage(atom, frame, inv, k, n); // the result is the synthetic ConcatOperand(concat, k)
                }
                continue;
            }
            LocalFlowGraph calleeFrame = bridge.frameOf(m);
            StructuredGraph g = calleeFrame != null ? graphOf(calleeFrame) : null;
            if (calleeFrame == null && dropDeadTarget(m, "fwd-concat")) {
                continue;
            }
            if (calleeFrame == null || g == null) {
                missingIr("fwd-concat-callee" + (calleeFrame == null ? "/noLfg/" : "/noGraph/"), m);
                refuse(atom.table, RTrackRefusal.MISSING_IR);
                continue;
            }
            enterReceiver(atom, calleeFrame, g, pushed, enter(mctx, frame, inv, m, true, atom));
        }
    }

    /**
     * The desugared call's targets: the CHA of {@code Object.toString()} over the operand's declared type, the block
     * filter, then the proven override drop. Memoised per (call, block). Null = unresolvable (refused by name).
     */
    private List<DispatchResolution.ResolvedTarget> desugaredTargets(DesugaredCall dc, AnalysisType operandType, ForwardFixpoint.Block block) {
        AnalysisMethod ts = strSites.objectToString();
        return ts == null ? null : chaTargets(ts, operandType != null ? operandType : ts.getDeclaringClass(), block);
    }

    /**
     * The targets of a call with no IR invoke of its own (the desugared {@code toString()}, a JDK model's callback): the
     * CHA of {@code declared} over {@code root}, the block filter, then the proven override drop. Memoised (pure).
     */
    List<DispatchResolution.ResolvedTarget> chaTargets(AnalysisMethod declared, AnalysisType root, ForwardFixpoint.Block block) {
        ForwardFixpoint.Block b = block != null && !block.isTop() ? block : null;
        return desugaredMemo.computeIfAbsent(java.util.Arrays.asList(declared, root, b == null ? "TOP" : b), key -> {
            List<AnalysisMethod> cha = DispatchResolution.computeDeterministicChaTargets(declared, root);
            List<DispatchResolution.ResolvedTarget> out = new ArrayList<>(cha.size());
            for (AnalysisMethod m : cha) {
                if (b != null && m.getDeclaringClass() != null && !intersects(b, m.getDeclaringClass())) {
                    continue;
                }
                out.add(new DispatchResolution.ResolvedTarget(m, bridge.frameOf(m), null, m.isStatic(),
                                m.getDeclaringClass() != null ? m.getDeclaringClass().toJavaName(true) : ""));
            }
            return b != null ? globalDrop(out, b) : out;
        });
    }

    /** The block test ({@code ForwardFixpoint.blockIntersects}). */
    private static boolean intersects(ForwardFixpoint.Block block, AnalysisType declaring) {
        for (AnalysisType type : block.types) {
            if (declaring.equals(type) || declaring.isAssignableFrom(type) || type.isAssignableFrom(declaring)) {
                return true;
            }
        }
        return false;
    }

    /**
     * A return arriving along a desugared call link: the value is the implicit {@code toString()}'s result, the
     * synthetic node {@code ConcatOperand(concat, k)}, whose only row is the operand usage for a STRING atom (STOP). A
     * container atom cannot be a {@code toString()} result (it is a String); it stops too (counted).
     */
    void concatOperandArrival(RAtom atom, DesugaredCall dc) {
        if (atom.kind == AtomKind.STRING) {
            ValueNode op = dc.operandNode();
            concatOperandUsage(atom, dc.frame, dc.concat, dc.operand, op);
        } else {
            strContainerConcatOperandArrivals.incrementAndGet();
        }
    }

    /**
     * The forward entry of a tracked receiver into an instance frame, for every crossing (call, bridged, desugared
     * {@code toString()}, thread-local {@code initialValue()}). It records the entry path whether or not the frame's IR
     * reads {@code this} (the receiver-entry invariant), then walks
     * {@code ParameterNode(0)} when it exists. Returns whether a walk was enqueued.
     */
    boolean enterReceiver(RAtom atom, LocalFlowGraph calleeFrame, StructuredGraph g, CallPath pushed, MethodContext calleeMctx) {
        ParameterNode self = g.getParameter(0);
        recordEntryPath(atom, calleeFrame, pushed);
        if (self == null) {
            return false; // the body never reads `this`: nothing to walk, the entry is recorded (the owner return)
        }
        enqueueWalk(atom, calleeFrame, self, pushed, calleeMctx);
        return true;
    }

    /** Record how the owner's walk entered the method (receiver crossings; only through {@link #enterReceiver}). */
    private void recordEntryPath(RAtom atom, LocalFlowGraph calleeFrame, CallPath pushed) {
        if (atom.kind == AtomKind.STRING) {
            return; // strings write no entryPaths (receiverIsTracked = false)
        }
        EntryList<CallPath> list = atom.table.entryPaths(calleeFrame);
        if (list.append(pushed, pushed == null ? "null" : pushed) >= 0) {
            censusEntryPaths.incrementAndGet();
        }
    }

    MethodContext enter(MethodContext callerCtx, LocalFlowGraph frame, Invoke inv, AnalysisMethod callee,
                    boolean receiverIsTracked, RAtom atom) {
        if (callee.isStatic()) {
            return MethodContext.staticCtx(new ContextElement(bridge.methodOf(frame), StringAnalysisChildInlining.pointsToBci(inv)), callerCtx);
        }
        if (receiverIsTracked && atom != null && atom.kind != AtomKind.STRING) {
            // (the callee mctx is enter(…, receiverIsTracked = false) for string atoms)
            return MethodContext.owner(atom.key.site, atom.key.context);
        }
        return MethodContext.UNKNOWN;
    }

    /**
     * The targets of a receiver-position crossing narrowed to the exact-type resolution (the exact receiver rule), or null
     * (keep the fan) when the atom's birthplace stamp is not exact, the resolution fails, or matches none of the targets.
     * The receiver-position case of the receiver-aware dispatch rule ({@code DispatchResolution.receiverDispatchTargets}).
     *
     * <p>The exact receiver rule: a receiver-position crossing of an atom whose birthplace stamp is an exact object type T
     * dispatches only to T's concrete resolution of the target (an object allocated as exactly T runs T's
     * implementation). Without it, an atom keyed by an IR node (no LFG vertex) has no site block, so the crossing would
     * take the whole CHA fan.
     */
    List<DispatchResolution.ResolvedTarget> exactReceiverTargetsOf(RAtom atom, ResolvedJavaMethod targetMethod, List<DispatchResolution.ResolvedTarget> targets) {
        if (targetMethod == null) {
            return null;
        }
        AnalysisType exactType;
        if (models.isFresh(atom)) {
            exactType = models.freshExactType(atom); // a model's fresh object: its site's class (null: inexact)
            if (exactType == null) {
                return null;
            }
        } else {
            ValueNode b = atom.birthNode;
            if (b == null || !(b.stamp(NodeView.DEFAULT) instanceof jdk.graal.compiler.core.common.type.ObjectStamp os) || !os.isExactType() ||
                            !(os.type() instanceof AnalysisType et)) {
                return null;
            }
            exactType = et;
        }
        // The receiver-aware dispatch rule with the one exact type (its fallbacks are exactly the ones above)
        return DispatchResolution.receiverDispatchTargets(List.of(exactType), targetMethod, targets);
    }

    ForwardFixpoint.Block atomSiteBlock(RAtom atom) {
        // (a STRING atom's block is σ.block, the widened String cone; an allocation atom's its mint block)
        return atom.siteBlock; // fixed at mint
    }

    /** The labels whose local block is the site's own identity type widened (no LFG edge is read: pure in the key). */
    private static final Set<String> OWN_IDENTITY_LABELS = Set.of("string-constant", "new-instance", "container-instance", "new-array", "invoke-array",
                    "invoke-return");

    /** Census (print-only): non-own-identity sites whose plain siteBlockOf block differs from / misses the widened birth type. */
    private final Counter mintBlockDiffers = new Counter();
    private final Counter mintBlockHeadMissesBirthType = new Counter();

    /**
     * The block of an atom key's site, computed once at mint.
     *
     * <p>The block of an allocation atom whose site vertex is an LFG passthrough vertex (e.g. {@code AllocatedObjectNode}
     * after a commit carrying a walked value) is the widened exact birth type, not the plain {@code siteBlockOf} for such
     * a vertex (the union of its in-edge blocks, not the allocation's own type).
     */
    private ForwardFixpoint.Block siteBlockOfKey(RAtomKey key, ValueNode birthNode) {
        Object ks = key.site instanceof IdSite id ? id.site : key.site; // a query atom's block is its birth site's
        if (!(ks instanceof LocalFlowGraph.LocalVertex v)) {
            return null;
        }
        if (v.kind == LocalFlowGraph.VertexKind.INTERNAL && OWN_IDENTITY_LABELS.contains(v.label)) {
            mintBlockAllocSite.incrementAndGet();
            try {
                return bridge.siteBlockOf(v.owner, v);
            } catch (Throwable t) {
                return null;
            }
        }
        mintBlockNonAllocSite.incrementAndGet();
        ForwardFixpoint.Block head;
        try {
            head = bridge.siteBlockOf(v.owner, v);
        } catch (Throwable t) {
            head = null;
        }
        AnalysisType exact = birthNode != null ? exactTypeOf(birthNode) : null;
        ForwardFixpoint.Block birth;
        try {
            birth = bridge.widenedBlockOf(exact);
        } catch (Throwable t) {
            birth = null;
        }
        boolean headTop = head == null || head.isTop();
        boolean birthTop = birth == null || birth.isTop();
        if (headTop != birthTop || !headTop && !head.equals(birth)) {
            mintBlockDiffers.incrementAndGet();
            if (!headTop && exact != null && !head.types.contains(exact)) {
                mintBlockHeadMissesBirthType.incrementAndGet();
                if (mintBlockHeadMissesBirthType.get() <= 8) {
                    System.out.println("[rtrack-e1] HEAD site block misses the birth type: " + key + " label=" + v.label + " birth=" +
                                    exact.toJavaName(true) + " headBlock=" + head);
                }
            }
        }
        return birth;
    }

    // ------------------------------------------------------------------
    // Backward tracking over the IR; sinks interned by root.
    // ------------------------------------------------------------------
    /**
     * Attach a consumer to the interned sink of {@code (frame, n, mctx, path)} (created on first use). An unresolvable
     * root delivers UNRESOLVED_VALUE to the listener.
     */
    private Sink attach(String kind, LocalFlowGraph frame, ValueNode n, MethodContext mctx, CallPath path, Listener l) {
        if (frame == null || n == null) {
            countRefusal(RTrackRefusal.UNRESOLVED_VALUE);
            Consumer<RTrackRefusal> onRef = l.onRefusal();
            if (onRef != null) {
                enqueue(() -> onRef.accept(RTrackRefusal.UNRESOLVED_VALUE));
            }
            return null;
        }
        MethodContext m = mctx != null ? mctx : MethodContext.UNKNOWN;
        return internSink(kind, new SinkRoot(frame, n, m, path), sink -> backward(frame, n, m, path, sink), l);
    }

    /**
     * The receiver sink of an instance frame whose IR has no {@code this} ParameterNode (the receiver-entry invariant): slot 0
     * at the entering call, resolved by the parameter case of slot 0 as for a present node. Its root has no node, so the
     * key is distinct from every {@link #attach} key.
     */
    private Sink attachReceiverOf(String kind, LocalFlowGraph frame, CallPath path, Listener l) {
        return internSink(kind, new SinkRoot(frame, null, MethodContext.UNKNOWN, path), sink -> parameterIndexCase(frame, 0, MethodContext.UNKNOWN, path, sink), l);
    }

    /**
     * A listener on the interned sink of a model operand {@code key} (a member chain or a callback temp, a value
     * record), whose root task {@code rootTask} resolves it (the engine's backward operand case).
     */
    Sink attachOperandSink(String kind, LocalFlowGraph frame, Object key, Consumer<Sink> rootTask, MethodContext mctx, CallPath path, Object listenerKey,
                    Consumer<Object> onAtom, Consumer<RTrackRefusal> onRefusal, ContainerTables.Refusable target) {
        MethodContext m = mctx != null ? mctx : MethodContext.UNKNOWN;
        return internSink(kind, new SinkRoot(frame, key, m, path), rootTask, new Listener(listenerKey, onAtom, onRefusal, target));
    }

    /** {@link #attachOperandSink} with an explicit ID-DEP dependent (the refusal target stays {@code target}). */
    Sink attachOperandSink(String kind, LocalFlowGraph frame, Object key, Consumer<Sink> rootTask, MethodContext mctx, CallPath path, Object listenerKey,
                    Consumer<Object> onAtom, Consumer<RTrackRefusal> onRefusal, ContainerTables.Refusable target, ContainerTables.Refusable depTarget) {
        MethodContext m = mctx != null ? mctx : MethodContext.UNKNOWN;
        return internSink(kind, new SinkRoot(frame, key, m, path), rootTask, new Listener(listenerKey, onAtom, onRefusal, target, depTarget));
    }

    /** The interned sink of {@code root} (created + {@code rootTask} enqueued on first use) with {@code l} attached. */
    Sink internSink(String kind, SinkRoot root, Consumer<Sink> rootTask, Listener l) {
        LocalFlowGraph frame = root.frame();
        Object n = root.node() != null ? root.node() : "receiver(slot 0)";
        CallPath path = root.path();
        MethodContext m = root.mctx();
        if (DUMP && path == null && !m.isOwner() && !m.isStatic() && focused(frameName(frame))) {
            System.out.println("[rtrack-dump] PATHLESS-ATTACH kind=" + kind + " root=" + describeRoot(root) + " listener=" + l.key());
        }
        if (DUMP && l.onRefusal() != null) {
            Consumer<RTrackRefusal> inner = l.onRefusal();
            String src = "INHERITED from sink " + kind + " " + frameName(frame) + " " + n;
            SinkRoot rootForDump = root;
            Object lkeyForDump = l.key();
            l = new Listener(l.key(), l.onAtom(), r -> {
                Sink origin = sinks.get(rootForDump);
                walkPos.set(src + " {sinkFirst=" + (origin != null ? sinkRefusalOrigin.get(origin) : "?") + "}");
                inheriting(origin, "sink:" + kind + "|" + dumpKey(lkeyForDump), () -> inner.accept(r));
            }, l.refusalTarget(), l.depTarget());
        }
        Sink s = sinks.get(root);
        if (s == null) {
            Sink fresh = new Sink(root, BACKWARD_BUDGET, TRACK_DEPTH_CAP);
            s = sinks.putIfAbsent(root, fresh);
            if (s == null) {
                s = fresh;
                bump(sinkRootsByKind, kind);
                Sink sink = fresh;
                enqueue(() -> rootTask.accept(sink));
            }
        }
        if (l.refusalTarget() != null && l.onAtom() != null) {
            ContainerTables.Refusable tgt = l.refusalTarget();
            Consumer<Object> inner = l.onAtom();
            l = new Listener(l.key(), a -> {
                if (tgt.stopVisible()) {
                    noteSkipped();
                    return;
                }
                inner.accept(a);
            }, l.onRefusal(), tgt, l.depTarget());
        }
        if (s.addListener(l)) {
            censusListeners.incrementAndGet();
        }
        return s;
    }

    void backward(LocalFlowGraph frame, ValueNode n, MethodContext mctx, CallPath path, Sink sink) {
        if (n == null) {
            refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
            return;
        }
        if (sink.stopVisible()) {
            if (!sink.visited.isEmpty()) {
                sink.peakVisited = Math.max(sink.peakVisited, sink.visited.size());
                sink.visited.clear(); // never explored again: release (exact under the stop rule)
            }
            noteSkipped();
            return;
        }
        if (!sink.visit(frame, n, path, mctx)) { // two contexts at one position are two routes (full mctx key)
            return;
        }
        if (typedSink(sink)) {
            AnalysisType tt = typedStopType(n);
            if (tt != null) {
                typedStops.incrementAndGet();
                addAtomTo(sink, new TypeToken(tt)); // typedrecv: a type-only sink stops at a final stamp type
                return;
            }
        }
        if (DUMP) {
            bwPos.set(frameName(frame) + " " + n + " path=" + path);
        }
        censusVisited.incrementAndGet();
        if (sink.visited.size() > sink.backwardBudget) {
            refuse(sink, RTrackRefusal.BACKWARD_BUDGET); // a set-size measure
            return;
        }
        if (n instanceof LimitedValueProxy p) {
            backward(frame, p.getOriginalNode(), mctx, path, sink);
            return;
        }
        if (n instanceof PhiNode phi) {
            for (ValueNode in : phi.values()) {
                backward(frame, in, mctx, path, sink);
            }
            return;
        }
        if (n instanceof ConditionalNode cond) {
            backward(frame, cond.trueValue(), mctx, path, sink);
            backward(frame, cond.falseValue(), mctx, path, sink);
            return;
        }
        if (n instanceof BoxNode && !boxMembersPrimitive(n)) {
            // A box whose type has a reference-typed instance field is
            // not justified by type: refused by name (impossible for JVM boxes;
            // the general rule).
            bump(unresolvedByClass, "BoxNode(reference-member)");
            refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
            return;
        }
        if (isBirthplace(n)) {
            contextsAndMint(frame, n, mctx, path, sink);
            return;
        }
        if (n instanceof ConstantNode cn) {
            if (cn.getValue() instanceof ImageHeapConstant ihc) {
                addAtomTo(sink, constantAtom(ihc).key);
            } else if (!JavaConstant.NULL_POINTER.equals(cn.getValue())) {
                unresolved(sink, n);
            }
            return; // null is not an object
        }
        if (n instanceof ParameterNode p) {
            parameterCase(frame, p, mctx, path, sink);
            return;
        }
        if (n instanceof Invoke inv) {
            if (inv.callTarget() instanceof IndirectCallTargetNode && reflectionCrossings.bridgedResultCase(frame, inv, mctx, path, sink)) {
                return; // the result of a bridged reflection edge
            }
            invokeResultCase(frame, inv, mctx, path, sink);
            return;
        }
        if (n instanceof LoadFieldNode lfn) {
            if (lfn.field().isStatic()) {
                staticLoadCase(frame, lfn, sink);
            } else {
                Object member = bridge.resolveField(lfn.field());
                loadCase(frame, lfn, lfn.object(), member, sink, mctx, path);
            }
            return;
        }
        if (n instanceof LoadIndexedNode lin) {
            loadCase(frame, lin, lin.array(), ARRAY_ELEMENT, sink, mctx, path);
            return;
        }
        if (n instanceof ExceptionObjectNode || n.getClass().getSimpleName().equals("BytecodeExceptionNode")) {
            refuse(sink, RTrackRefusal.EXCEPTION_FLOW_UNMODELLED); // an implicit exception object is exception flow too
            return;
        }
        if (isUnsafeFamily(n)) {
            refuse(sink, RTrackRefusal.UNSAFE_ACCESS);
            return;
        }
        if (n instanceof com.oracle.svm.core.graal.thread.LoadVMThreadLocalNode) {
            threadLocal.vmtlLoadCase(n, sink); // a VM thread-local load
            return;
        }
        unresolved(sink, n);
    }

    void addAtomTo(Sink sink, Object atomKey) {
        if (sink.addAtom(atomKey) && SINK_FAN_CAP > 0 && sink.atomCount() > SINK_FAN_CAP) {
            refuse(sink, RTrackRefusal.SINK_ATOM_FAN);
        }
    }

    private void unresolved(Sink sink, Node n) {
        bump(unresolvedByClass, n.getClass().getSimpleName());
        refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
    }

    /** The birthplace node set. */
    static boolean isBirthplace(ValueNode n) {
        // (+ the exception-edge forms of the same allocations, which this IR also carries)
        return n instanceof NewInstanceNode || n instanceof NewArrayNode ||
                        n instanceof NewInstanceWithExceptionNode || n instanceof NewArrayWithExceptionNode ||
                        n instanceof DynamicNewInstanceNode || n instanceof DynamicNewArrayNode ||
                        n instanceof NewMultiArrayNode || n instanceof AllocatedObjectNode || n instanceof ObjectClone ||
                        n instanceof BoxNode; // justified by type: boxMembersPrimitive
    }

    /**
     * A box allocation is a birthplace justified by its type, never by a class name: every instance field of the boxed
     * type is primitive, so its table is empty by construction and two sites sharing a cached instance at run time cannot
     * lose a connection. Such an atom is complete by proof (like a primitive array), never walked.
     */
    static boolean boxMembersPrimitive(ValueNode n) {
        jdk.vm.ci.meta.ResolvedJavaType t = jdk.graal.compiler.nodes.type.StampTool.typeOrNull(n.stamp(NodeView.DEFAULT));
        if (t == null) {
            return false;
        }
        for (ResolvedJavaField f : t.getInstanceFields(true)) {
            if (f.getJavaKind() == JavaKind.Object) {
                return false;
            }
        }
        return true;
    }

    /** The stored value of an element-source container's initial element store: the STRING atom of the ELEM seed. */
    record ElementValue(Object atomKey) {
    }

    /** Resume backward from a store entry's VALUE (the load case's continuation). */
    void resumeValue(StoreEntry s, Sink sink) {
        bump(itemKinds, "resume");
        MethodContext mc = s.mctx() instanceof MethodContext m ? m : MethodContext.UNKNOWN;
        Object v = s.value();
        if (v instanceof InitialValue iv) {
            // The initial store's value = the returns of the variable's exact-type
            // initialValue() under OWNER(variable): `this` inside it is the variable
            StructuredGraph g = graphOf(iv.frame());
            if (g == null) {
                refuse(sink, RTrackRefusal.MISSING_IR);
                return;
            }
            for (ReturnNode ret : g.getNodes(ReturnNode.TYPE)) {
                if (ret.result() != null) {
                    ValueNode r = ret.result();
                    enqueue(() -> backward(iv.frame(), r, mc, null, sink));
                }
            }
            return;
        }
        if (v instanceof ImageHeapConstant ihc) {
            addAtomTo(sink, constantAtom(ihc).key); // a build-time value
            return;
        }
        if (v instanceof ElementValue ev) {
            addAtomTo(sink, ev.atomKey()); // the element-source container's initial element (an ELEM seed's STRING atom)
            return;
        }
        if (v instanceof JdkModelEngine.OperandValue) {
            // A model operand (the elements of a representation array's initial value; a copied member chain)
            LocalFlowGraph f = s.frame();
            enqueue(() -> models.resumeStored(v, f, mc, s.path(), sink));
            return;
        }
        if (v instanceof DesugaredLoad dl) {
            // A copy/clone: the stored value is the load src[·] / src.m, the ordinary load case on src.
            ValueNode src = dl.src();
            LocalFlowGraph f = s.frame();
            enqueue(() -> loadCase(f, dl.node(), src, dl.member(), sink, mc, s.path()));
            return;
        }
        if (v instanceof VirtualObjectNode vo && s.node() instanceof CommitStore cs) {
            AllocatedObjectNode aon = allocatedOf(cs.commit(), vo);
            if (aon == null) {
                refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
                return;
            }
            enqueue(() -> backward(s.frame(), aon, mc, s.path(), sink));
            return;
        }
        if (v instanceof ValueNode vn && s.frame() != null) {
            enqueue(() -> backward(s.frame(), vn, mc, s.path(), sink));
            return;
        }
        refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
    }

    private void parameterCase(LocalFlowGraph frame, ParameterNode p, MethodContext mctx, CallPath path, Sink sink) {
        parameterIndexCase(frame, p.index(), mctx, path, sink);
    }

    /** The parameter case by slot index (the node is never read; also the receiver sink of a this-less frame). */
    private void parameterIndexCase(LocalFlowGraph frame, int pidx, MethodContext mctx, CallPath path, Sink sink) {
        AnalysisMethod pm = bridge.methodOf(frame);
        if (pidx == 0 && pm != null && !pm.isStatic() && mctx != null && mctx.isOwner()) {
            // OWNER(Y) = the invocation's receiver is Y: `this` resolves to Y exactly.
            RAtomKey owner = internKey(mctx.ownerSite, mctx.ownerCtx);
            if (atoms.containsKey(owner)) {
                addAtomTo(sink, owner);
                return;
            }
        }
        if (path != null && path.isFold()) {
            foldBackwardPathless.incrementAndGet(); // backward under a recursion fold is path-less (the fan below)
        } else if (path != null) {
            // The top link is by construction a call into this frame (pushed
            // when the tracking crossed into it); the belt is the guard.
            if (!beltOk(path, frame)) {
                refuse(sink, RTrackRefusal.BELT); // the genuineness belt
                return;
            }
            if (models.parameterCase(path, pidx, sink)) {
                return; // a model callback's parameter is its operand (an argument, an element, a temp)
            }
            List<ValueNode> args = argumentsAt(path, pidx);
            if (args.isEmpty()) {
                refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
                return;
            }
            for (ValueNode arg : args) {
                // the caller invocation's method context, when the link carries it
                backward(path.callerFrame, arg, restored(path.callerMctx), path.next, sink);
            }
            return;
        }
        if (OBJRET_ON && objectReturn.objretParameter(frame, pidx, mctx, sink)) {
            return; // rule U delivered (objret=1); the census alone (objret=0) never returns true
        }
        if (objectIdentity.idParameter(frame, pidx, mctx, sink)) {
            return; // the identity caller set (its first refusal adds the fan below, once)
        }
        parameterFan(frame, pidx, mctx, sink);
    }

    /** The path-less parameter fan (the argument of every caller the caller-index filter keeps), factored out of {@link #parameterIndexCase}. */
    void parameterFan(LocalFlowGraph frame, int pidx, MethodContext mctx, Sink sink) {
        if (containerCallersIncomplete(frame)) {
            refuse(sink, RTrackRefusal.MISSING_IR); // a caller the index cannot enumerate: never a silent miss
            return;
        }
        List<ForwardFixpoint.CallerSite> callers = worldTop.fanCallersOf(frame); // the receiver-typed caller filter
        // An outside-caller frame refuses WORLD_TOP_ENTRY whatever its direct
        // callers, which are still fanned over.
        int nCallers = callers == null ? 0 : callers.size();
        RTrackRefusal pe = parameterEntryRefusal(worldTop.outsideCaller(frame), nCallers);
        if (pe != null) {
            if (nCallers > 0) {
                e2WorldTopEntryWithCallers.incrementAndGet();
                worldTop.e2Note("WTE-fan", frame);
            }
            refuse(sink, pe);
        }
        if (nCallers == 0) {
            return;
        }
        if (callers.size() > ROOT_FAN_CAP) {
            if (DUMP && focused(frameName(frame) + " " + sink.rootKey)) {
                System.out.println("[rtrack-dump] CALLER_FAN_CAP frame=" + frameName(frame) + " param=" + pidx + " mctx=" + mctx +
                                " callers=" + callers.size() + " sinkRoot=" + describeRoot(sink.rootKey));
            }
            refuse(sink, RTrackRefusal.CALLER_FAN_CAP);
            return;
        }
        counters[ContextPolicy.CIDX_CALLER_FAN_FALLBACK]++; // the no-path caller fan, counted
        for (ForwardFixpoint.CallerSite c : callers) {
            LocalFlowGraph callerFrame = c.call() != null ? c.call().owner : null;
            List<ValueNode> args = c.call() != null ? argumentsOfVertex(callerFrame, c.call(), pidx) : List.of();
            if (callerFrame == null || args.isEmpty()) {
                refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
                return;
            }
            for (ValueNode arg : args) {
                backward(callerFrame, arg, MethodContext.UNKNOWN, null, sink);
            }
        }
    }

    /** The belt: the path's call must genuinely resolve into {@code frame} (callsite grain). */
    boolean beltOk(CallPath path, LocalFlowGraph frame) {
        if (!(path.call instanceof LocalFlowGraph.LocalVertex cv)) {
            return true; // an IR-node-keyed path link: identity-trusted
        }
        List<ForwardFixpoint.CallerSite> callers = callersOf(frame);
        if (callers == null) {
            return false;
        }
        for (ForwardFixpoint.CallerSite ref : callers) {
            LocalFlowGraph.LocalVertex rc = ref.call();
            if (rc == null || rc.owner != path.callerFrame) {
                continue;
            }
            // The call site is one of this frame's resolved callers: the same vertex, the same IR invoke, or the same
            // bci in the same caller frame. (No calleeMethod identity is demanded: detached descriptors resolve the
            // callee from the IR while the caller index's LFG vertex may carry none.)
            if (rc == cv || (cv.irNode != null && rc.irNode == cv.irNode) || rc.bci == cv.bci) {
                return true;
            }
        }
        return false;
    }

    List<ValueNode> argumentsAt(CallPath path, int slot) {
        if (path.call instanceof DesugaredCall dc) {
            // The desugared o.toString()'s only argument is its receiver, the concat operand k
            ValueNode op = slot == 0 ? dc.operandNode() : null;
            return op != null ? List.of(op) : List.of();
        }
        List<ValueNode> out = new ArrayList<>(1);
        for (ValueNode inv : invokesOf(path)) {
            ValueNode a = argOf(inv, slot);
            if (a != null) {
                out.add(a);
            }
        }
        return out;
    }

    private List<ValueNode> argumentsOfVertex(LocalFlowGraph frame, LocalFlowGraph.LocalVertex cv, int slot) {
        List<ValueNode> out = new ArrayList<>(1);
        for (ValueNode inv : invokesOfVertex(frame, cv)) {
            ValueNode a = argOf(inv, slot);
            if (a != null) {
                out.add(a);
            }
        }
        return out;
    }

    static ValueNode argOf(ValueNode invNode, int slot) {
        if (invNode instanceof Invoke inv && inv.callTarget() != null) {
            var args = inv.callTarget().arguments();
            return slot < args.size() ? args.get(slot) : null;
        }
        return null;
    }

    private void invokeResultCase(LocalFlowGraph frame, Invoke inv, MethodContext mctx, CallPath path, Sink sink) {
        LocalFlowGraph.LocalVertex callVertex = callVertexOf(frame, inv);
        List<DispatchResolution.ResolvedTarget> targets = targetsOf(frame, callVertex, Crossing.RESULT, null);
        if (targets.isEmpty()) {
            noTarget(callVertex, inv.callTarget() != null ? inv.callTarget().targetMethod() : null, "bwd");
            refuse(sink, RTrackRefusal.NO_TARGET);
            return;
        }
        if (targets.size() > CHA_CAP && models.collapsedCount(targets) > CHA_CAP) {
            if (receiverSinkDispatch(frame, inv, callVertex, mctx, path, sink, targets, true)) {
                return; // over the cap, the receiver's atoms may still select a few targets (fallback: the refusal)
            }
            refuse(sink, RTrackRefusal.CHA_FAN_CAP);
            return;
        }
        if (targets.size() > 1 && receiverSinkDispatch(frame, inv, callVertex, mctx, path, sink, targets, false)) {
            return; // the targets follow the receiver's resolved atoms
        }
        CallPath pushed = CallPath.pushBackward(frame, callVertex, mctx, path); // the backward path bound
        Set<String> jdkApplied = null; // one backward application per collapse key, as forward
        for (DispatchResolution.ResolvedTarget t : targets) {
            JdkModels.Op jop = models.op(t.method());
            if (jop != null) {
                jdkApplied = jdkApplied != null ? jdkApplied : new java.util.HashSet<>();
                if (!models.firstOfKey(jdkApplied, jop)) {
                    continue;
                }
            }
            resultOfTarget(frame, inv, mctx, path, sink, pushed, t);
        }
    }

    /** One target of a backward invoke-result case: the callee's return values, resolved into {@code sink}. */
    private void resultOfTarget(LocalFlowGraph frame, Invoke inv, MethodContext mctx, CallPath path, Sink sink, CallPath pushed,
                    DispatchResolution.ResolvedTarget t) {
        TargetCheck tc = targetCheck(t.method()); // the shared per-target rules
        if (tc.rule() == TargetRule.THREAD_LOCAL) {
            // A translated thread-local read / a current-thread accessor
            threadLocal.tlInvokeResult(frame, inv, tc.tl(), mctx, path, sink);
            return;
        }
        if (tc.rule() == TargetRule.MODEL && models.invokeResult(frame, inv, tc.op(), mctx, path, sink)) {
            return; // a modelled JDK target's result (`result ir` walks the IR below)
        }
        if (tc.rule() == TargetRule.CLOSED) {
            models.refuseUnlisted(sink, tc.closed(), t.method(), "bwd");
            return;
        }
        LocalFlowGraph calleeFrame = bridge.frameOf(t.method());
        StructuredGraph g = calleeFrame != null ? graphOf(calleeFrame) : null;
        if (calleeFrame == null && dropDeadTarget(t.method(), "bwd")) {
            return;
        }
        if (g == null) {
            missingIr("bwd-callee" + (calleeFrame == null ? "/noLfg/" : "/noGraph/"), t.method());
            refuse(sink, RTrackRefusal.MISSING_IR);
            return;
        }
        // the callee invocation's context: STATIC(call, caller) for a static callee
        // (the enter() rule); an instance callee's receiver is unknown here.
        MethodContext calleeMctx = t.method().isStatic()
                        ? MethodContext.staticCtx(new ContextElement(bridge.methodOf(frame), StringAnalysisChildInlining.pointsToBci(inv)), mctx != null ? mctx : MethodContext.UNKNOWN)
                        : MethodContext.UNKNOWN;
        for (ReturnNode ret : g.getNodes(ReturnNode.TYPE)) {
            if (ret.result() != null) {
                backward(calleeFrame, ret.result(), calleeMctx, pushed, sink);
            }
        }
    }

    /**
     * The backward invoke-result case's source of the receiver-aware dispatch rule
     * ({@code DispatchResolution.receiverDispatchTarget}). A virtual/interface invoke whose result is resolved backward,
     * and whose fan has several targets (or is over the CHA cap), resolves its receiver through an ordinary interned sink
     * (argument 0, same frame, context and path). Each receiver atom whose exact type selects a fan target starts that
     * target. An atom of unknown type, a type the rule doubts, or any refusal of the receiver sink takes the committed
     * outcome instead (the whole fan, or the {@code CHA_FAN_CAP} refusal over the cap). Sound: every run-time receiver is
     * one of the receiver sink's atoms unless that sink is refused (the engine's contract for every sink), and it
     * dispatches to its exact type's resolution. The result sink never inherits the receiver sink's refusals (the fallback
     * covers them), so the rule only removes targets. The listener is monotone and replayed: the selected targets at the
     * fixpoint are the union over the receiver's atoms, independent of arrival order. A receiver sink that stays empty
     * and unrefused starts no target: the inference "no base object, so the operation never executes" that
     * {@link #loadCase} draws from an empty unrefused base sink, under the same contract (every source mints or refuses
     * by name). {@link #pointsToReceiverNarrow} treats an empty points-to state the other way, as doubt: that state is an
     * external, context-insensitive fact, while this sink is the engine's own, per context. Returns false when it does
     * not apply (a direct call).
     */
    private boolean receiverSinkDispatch(LocalFlowGraph frame, Invoke inv, LocalFlowGraph.LocalVertex callVertex, MethodContext mctx, CallPath path, Sink sink,
                    List<DispatchResolution.ResolvedTarget> targets, boolean overCap) {
        if (!(inv.callTarget() instanceof MethodCallTargetNode ct) || ct.invokeKind() == null || !ct.invokeKind().isIndirect() || ct.arguments().isEmpty() ||
                        ct.targetMethod() == null) {
            return false;
        }
        ValueNode recv = ct.arguments().get(0);
        ResolvedJavaMethod callee = ct.targetMethod();
        CallPath pushed = CallPath.pushBackward(frame, callVertex, mctx, path);
        RecvSinkCase c = new RecvSinkCase(frame, callVertex);
        recvSinkCases.add(c);
        Runnable fallback = () -> {
            if (c.fellBack.compareAndSet(false, true)) {
                if (overCap) {
                    refuse(sink, RTrackRefusal.CHA_FAN_CAP); // the committed outcome over the cap
                    return;
                }
                for (DispatchResolution.ResolvedTarget t : targets) {
                    if (c.started.add(t.method())) {
                        enqueue(() -> resultOfTarget(frame, inv, mctx, path, sink, pushed, t));
                    }
                }
            }
        };
        attach("bwdrecv", frame, recv, mctx, path, new Listener(List.of("bwdrecv", sink, inv.asNode()), x -> {
            if (c.fellBack.get()) {
                return;
            }
            RAtom xa = atoms.get(x);
            AnalysisMethod m = DispatchResolution.receiverDispatchTarget(xa != null ? atomExactType(xa) : null, callee, targets);
            if (m == null) {
                fallback.run();
                return;
            }
            if (c.started.add(m)) {
                for (DispatchResolution.ResolvedTarget t : targets) {
                    if (m.equals(t.method())) {
                        enqueue(() -> resultOfTarget(frame, inv, mctx, path, sink, pushed, t));
                        break;
                    }
                }
            }
        }, r -> fallback.run(), sink));
        return true;
    }

    /** One backward receiver-sink dispatch case: whether it fell back, and the targets its atoms started. */
    private static final class RecvSinkCase {
        final AtomicBoolean fellBack = new AtomicBoolean();
        final Set<AnalysisMethod> started = ConcurrentHashMap.newKeySet();
        final LocalFlowGraph frame;
        final LocalFlowGraph.LocalVertex call;

        RecvSinkCase(LocalFlowGraph frame, LocalFlowGraph.LocalVertex call) {
            this.frame = frame;
            this.call = call;
        }
    }

    private final ConcurrentLinkedQueue<RecvSinkCase> recvSinkCases = new ConcurrentLinkedQueue<>();

    /**
     * Census (print-only): the receiver-sink cases by outcome, the 0-target bucket split by the call's final points-to
     * receiver state. That state is context-insensitive, so {@code empty} corroborates a 0 case and {@code nonEmpty} does
     * not refute one (another context of the call can hold the receivers).
     */
    private String recvSinkCensus() {
        int n = 0;
        int fell = 0;
        int[] byCount = new int[4];
        int[] zero = new int[4]; // empty, nonEmpty, saturated, noFlow
        for (RecvSinkCase c : recvSinkCases) {
            n++;
            if (c.fellBack.get()) {
                fell++;
            } else {
                byCount[Math.min(c.started.size(), 3)]++;
                if (c.started.isEmpty()) {
                    zero[zeroTargetPointsToBucket(c)]++;
                }
            }
        }
        return " recvSink{cases=" + n + " fellBack=" + fell + " narrowed=[0:" + byCount[0] + " 1:" + byCount[1] + " 2:" + byCount[2] + " 3+:" + byCount[3] + "]}" +
                        " recvSink0{empty=" + zero[0] + " nonEmpty=" + zero[1] + " saturated=" + zero[2] + " noFlow=" + zero[3] + "}";
    }

    /** The points-to bucket of one 0-target case (0 empty, 1 nonEmpty, 2 saturated, 3 noFlow). Print-only. */
    private int zeroTargetPointsToBucket(RecvSinkCase c) {
        String[] reason = {"other"};
        List<AnalysisType> types;
        try {
            types = bridge.pointsToReceiverTypes(bridge.methodOf(c.frame), c.call, r -> reason[0] = r);
        } catch (Throwable ex) {
            return 3;
        }
        if (types != null) {
            return types.isEmpty() ? 0 : 1;
        }
        switch (reason[0]) {
            case "emptyState":
            case "receiverDisabled":
                return 0;
            case "invokeSaturated":
            case "receiverSaturated":
            case "receiverAllInstantiated":
                return 2;
            default:
                return 3;
        }
    }

    // ------------------------------------------------------------------
    // The reflection bridge's crossings. Only the two VM function-pointer call nodes
    // (OUTER: through SubstrateAccessor.expandSignature; INNER: the stub's call through its target pointer) get targets;
    // each target is an ordinary crossing.
    // ------------------------------------------------------------------
    final Counter e3Crossings = new Counter();
    /** Print-only diagnostic (default off): the frames whose caller fan is over the cap (RETURN_FAN_CAP / CALLER_FAN_CAP). */
    final Counter e3ChaCap = new Counter();
    final Counter e3ResultCases = new Counter();
    final Counter e3Unresolved = new Counter();

    private volatile ReflectionBridge reflBridgeBuilt;

    /** The bridge's table and edges, built once after the fixpoint's metadata is fixed (under the index build lock). */
    ReflectionBridge reflBridge() {
        ReflectionBridge b = reflBridgeBuilt;
        if (b != null) {
            return b;
        }
        irCallerIndex(); // built first, outside the index build lock (it takes this object's monitor)
        ContainerAtoms.enterMon(e2BuildLock);
        try {
            synchronized (e2BuildLock) {
                if (reflBridgeBuilt == null) {
                    reflBridgeBuilt = ReflectionBridge.build(this);
                }
                return reflBridgeBuilt;
            }
        } finally {
            ContainerAtoms.exitMon(e2BuildLock);
        }
    }

    /** The IR caller sites of {@code callee} as {caller method, invoke node} pairs, or null when incomplete. */
    List<Object[]> irCallInvokesOf(LocalFlowGraph callee) {
        Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> idx = irCallerIndex();
        if (incompleteCallers.contains(callee)) {
            return null;
        }
        List<Object[]> out = new ArrayList<>();
        for (ForwardFixpoint.CallerSite c : idx.getOrDefault(callee, List.of())) {
            List<ValueNode> invs = invokesOfVertex(c.call().owner, c.call());
            if (invs.isEmpty()) {
                return null;
            }
            for (ValueNode v : invs) {
                out.add(new Object[]{c.caller(), v});
            }
        }
        return out;
    }

    // ------------------------------------------------------------------
    // The load case: pause on the load's reaching-version pool, resolve the owner backward, resume from the reaching
    // stores.
    // ------------------------------------------------------------------
    void loadCase(LocalFlowGraph frame, ValueNode loadNode, ValueNode base, Object member, Sink sink, MethodContext mctx, CallPath path) {
        loadCase(frame, loadNode, base, member, List.of(), sink, mctx, path);
    }

    /**
     * The load case of {@code base.member}, followed by the members {@code rest} (a JDK model's chained load,
     * e.g. {@code Itr.next()} = {@code this$0.<elem>}; empty for every IR load): each hop resolves the reaching stores'
     * values and loads the next member from their atoms, at the same load node; the last hop resumes the stored values.
     */
    void loadCase(LocalFlowGraph frame, ValueNode loadNode, ValueNode base, Object member, List<Object> rest, Sink sink, MethodContext mctx, CallPath path) {
        bump(itemKinds, "loadCase");
        if (member == null || base == null) {
            refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
            return;
        }
        if (DUMP && models.abstracted(member)) {
            System.out.println("[rtrack-dump] JDKMODEL-FIELD field-loadcase " + memberName(member) + " at " + frameName(frame) + " node=" + loadNode + " sink=" + describeRoot(sink.rootKey) +
                            " mctx=" + mctx);
        }
        if (models.fieldRule(sink, member, "field-loadcase")) {
            return; // a backward walk reads a representation field
        }
        if (sink.trackDepth.incrementAndGet() > sink.trackDepthCap) {
            refuse(sink, RTrackRefusal.TRACK_DEPTH); // the aggregate proxy
            return;
        }
        Object key = rest.isEmpty() ? List.of("lc", sink, loadNode, member) : List.of("lc", sink, loadNode, member, rest);
        attach("loadcase", frame, base, mctx, path, new Listener(key, y -> loadFrom(atoms.get(y), member, rest, frame, loadNode, sink), r -> refuse(sink, r), sink));
    }

    /** The load case whose base is a model operand {@code baseKey} (a callback temp), resolved by {@code baseTask}. */
    void loadCaseKey(LocalFlowGraph frame, ValueNode loadNode, Object baseKey, Consumer<Sink> baseTask, Object member, List<Object> rest, Sink sink, MethodContext mctx,
                    CallPath path) {
        bump(itemKinds, "loadCase");
        if (DUMP && models.abstracted(member)) {
            System.out.println("[rtrack-dump] JDKMODEL-FIELD field-loadcase-key " + memberName(member) + " at " + frameName(frame) + " node=" + loadNode + " sink=" + describeRoot(sink.rootKey) +
                            " mctx=" + mctx);
        }
        if (models.fieldRule(sink, member, "field-loadcase")) {
            return;
        }
        if (sink.trackDepth.incrementAndGet() > sink.trackDepthCap) {
            refuse(sink, RTrackRefusal.TRACK_DEPTH);
            return;
        }
        attachOperandSink("loadcase", frame, baseKey, baseTask, mctx, path, List.of("lck", sink, loadNode, baseKey, member, rest),
                        y -> loadFrom(atoms.get(y), member, rest, frame, loadNode, sink), r -> refuse(sink, r), sink);
    }

    /** One hop of the load case: the stores of {@code member} in {@code y}'s table that reach {@code loadNode}. */
    private void loadFrom(RAtom y, Object member, List<Object> rest, LocalFlowGraph frame, ValueNode loadNode, Sink sink) {
        if (member instanceof JdkModels.Slot slot && y.kind == AtomKind.CONSTANT && !models.heapSlotsFilled(y.constant, slot)) {
            refuse(sink, RTrackRefusal.JDK_MODEL_UNMODELLED); // a heap constant's slots are filled only from a representation
            return;
        }
        if (y.length0 && member == ARRAY_ELEMENT) {
            counters[ContextPolicy.CIDX_LENGTH_ZERO_PROOFS]++;
            return; // stores[[]] empty by proof
        }
        Table yt = y.table;
        EntryList<StoreEntry> list = yt.stores(member);
        Object key = rest.isEmpty() ? List.of("lc", sink, frame, loadNode) : List.of("lc", sink, frame, loadNode, rest);
        register(list, key, idx -> {
            if (rest.isEmpty()) {
                resumeValue(list.get(idx), sink);
            } else {
                nextHop(list.get(idx), rest, frame, loadNode, sink);
            }
        }, idx -> yt.pools(member).connected(list.get(idx).frame(), list.get(idx).node(), frame, loadNode), sink);
    }

    /**
     * A chained load's next hop: the atoms of the store's value ({@link #resumeValue}, through an interned sink of the
     * store entry), then the next member from their tables.
     */
    private void nextHop(StoreEntry s, List<Object> rest, LocalFlowGraph frame, ValueNode loadNode, Sink sink) {
        List<Object> tail = rest.subList(1, rest.size());
        if (s.value() instanceof ImageHeapConstant ihc) {
            loadFrom(constantAtom(ihc), rest.get(0), tail, frame, loadNode, sink);
            return;
        }
        MethodContext mc = s.mctx() instanceof MethodContext m ? m : MethodContext.UNKNOWN;
        attachOperandSink("loadchain", s.frame(), new StoredValueKey(s), hop -> resumeValue(s, hop), mc, s.path(), List.of("lchain", sink, loadNode, rest, s.node()),
                        z -> loadFrom(atoms.get(z), rest.get(0), tail, frame, loadNode, sink), r -> refuse(sink, r), sink);
    }

    /** The root of a stored value's interned sink (the store entry, by value). */
    private record StoredValueKey(StoreEntry entry) {
    }

    private void staticLoadCase(LocalFlowGraph frame, LoadFieldNode lfn, Sink sink) {
        AnalysisField f = bridge.resolveField(lfn.field());
        if (f == null) {
            refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
            return;
        }
        Table st = staticTable(f);
        EntryList<StoreEntry> list = st.stores(f);
        register(list, List.of("ls", sink, frame, lfn), idx -> resumeValue(list.get(idx), sink),
                        idx -> st.pools(f).connected(list.get(idx).frame(), list.get(idx).node(), frame, lfn),
                        sink);
    }

    // ------------------------------------------------------------------
    // Birthplace minting: ContextPolicy values + the owner / static-fan orchestration.
    // ------------------------------------------------------------------
    private void contextsAndMint(LocalFlowGraph frame, ValueNode n, MethodContext mctx, CallPath path, Sink sink) {
        contextsAndMint(frame, n, mctx, path, sink, null);
    }

    /**
     * {@code freshSite} = a JDK model's fresh site (the object is born at the call node {@code n} with the site's
     * class; the contexts are an allocation's at that node), null = the birthplace {@code n}'s own site.
     *
     * <p>The owner of an allocation in an instance frame that never reads {@code this} is still resolved, as the receiver
     * argument of the entering call (slot 0: with a path the call's receiver argument, without one the caller fan), and
     * every forward entry of a tracked receiver records its entry path (the class comment's receiver-entry invariant).
     */
    void contextsAndMint(LocalFlowGraph frame, ValueNode n, MethodContext mctx, CallPath path, Sink sink, Object freshSite) {
        bump(itemKinds, "contextsAndMint");
        AnalysisMethod method = bridge.methodOf(frame);
        boolean instanceFrame = method != null && !method.isStatic();
        if (instanceFrame) {
            if (mctx != null && mctx.isOwner()) {
                HeapContext ctx = ContextPolicy.DefaultContextPolicy.contextForAllocation(method, mctx, mctx.ownerSite,
                                mctx.ownerCtx, null, counters);
                mintInto(sink, n, frame, ctx, mctx, internKey(mctx.ownerSite, mctx.ownerCtx), freshSite);
                return;
            }
            // Unknown owner: a BackwardTask on `this`; one atom per
            // resolved owner; MERGE when unresolvable (counted, never refused).
            StructuredGraph g = graphOf(frame);
            ParameterNode thisParam = g != null ? g.getParameter(0) : null;
            if (thisParam == null && g == null) {
                mergeMint(sink, n, frame, ContextPolicy.CIDX_CTX_MERGE_OWNER_UNKNOWN, freshSite);
                return;
            }
            OwnerResolution res = new OwnerResolution(n, freshSite, frame, sink, ContextPolicy.CIDX_CTX_MERGE_OWNER_UNKNOWN,
                            o -> MethodContext.owner(o.key.site, o.key.context),
                            () -> mergeMint(sink, n, frame, ContextPolicy.CIDX_CTX_MERGE_OWNER_UNKNOWN, freshSite));
            synchronized (ownerResolutions) {
                ownerResolutions.add(res);
            }
            // Deferred: an owner sink can receive the atoms this very site mints (self-owned structures), so inline
            // delivery would recurse without bound. The owner sink is read at round boundaries only.
            Listener ownerListener = new Listener(List.of("owner", sink, n, res), a -> {
            }, null, null, sink); // (the owner atoms feed sink's mint)
            if (thisParam == null) {
                // The method never reads `this`, so its IR has no
                // ParameterNode(0); the owner is still the entering call's receiver (slot 0), and the owner decision comes from
                // that sink exactly as for a method whose `this` has a node
                thislessOwnerResolutions.incrementAndGet();
                res.ownerSink = attachReceiverOf("owner-thisless", frame, path, ownerListener);
            } else {
                res.ownerSink = attach("owner", frame, thisParam, MethodContext.UNKNOWN, path, ownerListener);
            }
            return;
        }
        // A static-method allocation (the static rule; a clone's ctx
        // follows the method's shape like any birthplace).
        if (mctx != null && mctx.isStatic()) {
            // The static frame's own invocation context is known (it is this frame's
            // own context, not the caller's: the entering call must not be duplicated).
            mintStatic(sink, n, frame, mctx, path, freshSite);
            return;
        }
        if (path != null && path.call != null) {
            ContextElement elem = callElementOf(path);
            if (elem == null || elem.method == null) {
                mergeMint(sink, n, frame, ContextPolicy.CIDX_CTX_MERGE_STATIC_UNKNOWN, freshSite);
                return;
            }
            // The static chain, read from the path the tracking came through (the backward mctx is UNKNOWN on
            // backward routes): while the caller is itself static, its entering call is the next link.
            MethodContext callerCtx = invocationCtx(path);
            mintStatic(sink, n, frame, MethodContext.staticCtx(elem, callerCtx), path, freshSite);
            return;
        }
        // No entering call: fan-then-merge. The world-top static
        // method has no entering call by construction: EMPTY ctx.
        List<ForwardFixpoint.CallerSite> callers = callersOf(frame);
        boolean incomplete = containerCallersIncomplete(frame);
        int nCallers = callers == null ? 0 : callers.size();
        boolean outsideStatic = worldTop.outsideCaller(frame);
        int sf = staticFanDecision(incomplete, nCallers, !incomplete && nCallers == 0 && outsideStatic, ROOT_FAN_CAP);
        if (sf == SF_MERGE) {
            // unenumerable fan / no caller of a non-world-top frame / over the cap: the merge
            mergeMint(sink, n, frame, ContextPolicy.CIDX_CTX_MERGE_STATIC_UNKNOWN, freshSite);
            return;
        }
        if (sf == SF_EMPTY) {
            mintInto(sink, n, frame, HeapContext.EMPTY, MethodContext.UNKNOWN, null, freshSite);
            return;
        }
        boolean any = false;
        boolean anyUnresolved = false;
        for (ForwardFixpoint.CallerSite c : callers) {
            LocalFlowGraph callerFrame = c.call() != null ? c.call().owner : null;
            AnalysisMethod callerMethod = callerFrame != null ? bridge.methodOf(callerFrame) : null;
            if (c.call() == null || callerMethod == null) {
                anyUnresolved = true;
                continue;
            }
            ContextElement elem = new ContextElement(callerMethod, c.call().bci);
            HeapContext ctx = ContextPolicy.DefaultContextPolicy.contextForAllocation(method, MethodContext.UNKNOWN, null,
                            null, elem, counters);
            mintInto(sink, n, frame, ctx, MethodContext.staticCtx(elem, MethodContext.UNKNOWN), null, freshSite);
            any = true;
        }
        if (!any || anyUnresolved) {
            // an unresolvable fan member: the MERGE covers it (sound, counted)
            mergeMint(sink, n, frame, ContextPolicy.CIDX_CTX_MERGE_STATIC_UNKNOWN, freshSite);
        }
        if (outsideStatic) {
            // The fan's call-site contexts cover the direct callers only; the outside
            // invocation is the EMPTY context (the world-top atom), whose return refuses WORLD_TOP_EXIT.
            e2StaticOutsideMint.incrementAndGet();
            mintInto(sink, n, frame, HeapContext.EMPTY, MethodContext.UNKNOWN, null, freshSite);
        }
    }

    /** The heap context for an allocation minted under method context {@code m}. */
    private HeapContext ctxFor(AnalysisMethod method, MethodContext m) {
        if (m.isStatic()) {
            return ContextPolicy.DefaultContextPolicy.contextForAllocation(method, m.caller, null, null, m.call, counters);
        }
        return ContextPolicy.DefaultContextPolicy.contextForAllocation(method, null, m.ownerSite, m.ownerCtx, null, counters);
    }

    /**
     * A static-method allocation under the static frame's invocation context {@code own}. When the static chain ends at
     * an instance caller whose owner is unknown, that owner is resolved as an instance allocation's owner: backward on
     * the instance caller's {@code this} along the path, one atom per owner (the chain's tail replaced by OWNER(owner)),
     * MERGE (counted) when unresolvable, refused or over the cap.
     */
    private void mintStatic(Sink sink, ValueNode n, LocalFlowGraph frame, MethodContext own0, CallPath path, Object freshSite) {
        AnalysisMethod method = bridge.methodOf(frame);
        MethodContext own = extendChainFromPath(own0, path);
        OwnerTail tail = unknownOwnerTail(own, path);
        LocalFlowGraph ownerFrame = tail != null ? tail.frame() : null;
        if (ownerFrame == null) {
            mintInto(sink, n, frame, ctxFor(method, own), own, null, freshSite);
            return;
        }
        // The MERGE for the chain: the owner-merged identity (HeapContext.mergedOf),
        // never the owner-specific key a ctxk truncation would collide with.
        HeapContext mergedCtx = HeapContext.mergedOf(ctxFor(method, own).elements());
        StructuredGraph g = graphOf(ownerFrame);
        ParameterNode thisParam = g != null ? g.getParameter(0) : null;
        if (thisParam == null && g == null) {
            counters[ContextPolicy.CIDX_CTX_MERGE_OWNER_UNKNOWN]++;
            mintInto(sink, n, frame, mergedCtx, own, null, freshSite);
            return;
        }
        OwnerResolution res = new OwnerResolution(n, freshSite, frame, sink, ContextPolicy.CIDX_CTX_MERGE_OWNER_UNKNOWN,
                        o -> withOwnerTail(own, MethodContext.owner(o.key.site, o.key.context)),
                        () -> {
                            counters[ContextPolicy.CIDX_CTX_MERGE_OWNER_UNKNOWN]++;
                            mintInto(sink, n, frame, mergedCtx, own, null, freshSite);
                        });
        synchronized (ownerResolutions) {
            ownerResolutions.add(res);
        }
        CallPath ownerPath = tail.entering();
        Listener ownerListener = new Listener(List.of("owner-static", sink, n, own, res), a -> {
        }, null, null, sink); // read at round boundaries (feeds sink)
        if (thisParam == null) {
            // The static chain's instance frame never reads `this`; its owner is the entering
            // call's receiver (slot 0), as in contextsAndMint
            thislessOwnerResolutions.incrementAndGet();
            res.ownerSink = attachReceiverOf("owner-static-thisless", ownerFrame, ownerPath, ownerListener);
        } else {
            res.ownerSink = attach("owner", ownerFrame, thisParam, MethodContext.UNKNOWN, ownerPath, ownerListener);
        }
    }

    /**
     * A static chain whose terminal caller is UNKNOWN while the path still carries the link that entered that terminal
     * frame is completed from the path: the caller invocation's context is {@code invocationCtx(link)}. Bounded by ctxk.
     */
    private MethodContext extendChainFromPath(MethodContext own, CallPath path) {
        if (DUMP && own != null && own.isStatic() && focused(String.valueOf(own.call))) {
            StringBuilder links = new StringBuilder();
            for (CallPath q = path; q != null; q = q.next) {
                links.append(" | ").append(callElementOf(q)).append(" callType=").append(q.call == null ? "null" : q.call.getClass().getSimpleName())
                                .append(" from=").append(frameName(q.callerFrame)).append(" cm=").append(q.callerMctx);
            }
            System.out.println("[rtrack-dump] EXTEND own=" + own + " depth=" + (path != null ? path.depth() : 0) + links);
        }
        return extendChain(own, path, 1);
    }

    /**
     * {@code depth} = the static links of the chain up to and including {@code own}. A null caller means UNKNOWN when the
     * chain is shorter than ctxk and TRUNCATED at ctxk otherwise; only the former is completed.
     */
    private MethodContext extendChain(MethodContext own, CallPath path, int depth) {
        if (own == null || !own.isStatic() || path == null || !Objects.equals(callElementOf(path), own.call)) {
            return own;
        }
        MethodContext tail = own.caller;
        if (tail != null && tail.isOwner()) {
            return own; // known
        }
        MethodContext rest;
        if (tail != null && tail.isStatic()) {
            rest = extendChain(tail, path.next, depth + 1);
        } else if (depth < ContextPolicy.CTXK) {
            rest = invocationCtx(path); // UNKNOWN (null or the UNKNOWN value): read it off the path
        } else {
            return own; // truncated at ctxk
        }
        if (rest == tail || rest == null || rest.unknown) {
            return own;
        }
        return MethodContext.staticCtx(own.call, rest);
    }

    /** The instance caller whose owner is unknown, and the path link entering it (null = none). */
    private record OwnerTail(LocalFlowGraph frame, CallPath entering) {
    }

    /**
     * If {@code own}'s static chain (fewer than ctxk static elements) ends in an UNKNOWN caller and the path locates that
     * caller as an instance frame, that frame and the link entering it; null when there is nothing to resolve.
     */
    private OwnerTail unknownOwnerTail(MethodContext own, CallPath path) {
        int d = 0;
        MethodContext c = own;
        CallPath p = path;
        LocalFlowGraph f = null;
        while (c != null && c.isStatic()) {
            if (p == null || !Objects.equals(callElementOf(p), c.call)) {
                return null; // the path does not show this chain: nothing to resolve along it
            }
            f = p.callerFrame;
            p = p.next;
            c = c.caller;
            d++;
        }
        if (c != null || d == 0 || f == null) {
            // an owner already known, or nothing static. (Not "d >= ctxk": even when
            // truncation drops the owner from the identity, the walk's returns follow
            // the method-context chain, which keeps it, and the merge must not share
            // the owner-specific key.)
            return null;
        }
        AnalysisMethod fm = bridge.methodOf(f);
        if (fm == null || fm.isStatic()) {
            return null;
        }
        return new OwnerTail(f, p);
    }

    /** The static chain {@code own} with its terminal (unknown) caller replaced by {@code tail}. */
    private static MethodContext withOwnerTail(MethodContext own, MethodContext tail) {
        if (own == null || !own.isStatic()) {
            return tail;
        }
        return MethodContext.staticCtx(own.call, own.caller == null ? tail : withOwnerTail(own.caller, tail));
    }

    /**
     * The method context of the invocation of {@code out.callerFrame}, where {@code out} is the path link leaving that
     * frame (an instance frame's context is recorded on the link that leaves it). A recorded context wins; else a static
     * frame's context is rebuilt from its entering call ({@code out.next}), recursively (bounded by ctxk); else UNKNOWN.
     */
    private MethodContext invocationCtx(CallPath out) {
        if (out == null || out.callerFrame == null) {
            return MethodContext.UNKNOWN;
        }
        if (out.callerMctx instanceof MethodContext mc && (mc.isOwner() || mc.isStatic())) {
            return mc;
        }
        AnalysisMethod m = bridge.methodOf(out.callerFrame);
        if (m == null || !m.isStatic()) {
            return MethodContext.UNKNOWN;
        }
        CallPath entering = out.next;
        if (entering == null || entering.call == null) {
            return MethodContext.UNKNOWN;
        }
        ContextElement e = callElementOf(entering);
        if (e == null || e.method == null) {
            return MethodContext.UNKNOWN;
        }
        return MethodContext.staticCtx(e, invocationCtx(entering));
    }

    private ContextElement callElementOf(CallPath path) {
        if (path.call instanceof LocalFlowGraph.LocalVertex cv) {
            return new ContextElement(bridge.methodOf(path.callerFrame), cv.bci);
        }
        if (path.call instanceof Invoke inv) {
            return new ContextElement(bridge.methodOf(path.callerFrame), StringAnalysisChildInlining.pointsToBci(inv));
        }
        if (path.call instanceof JdkModelEngine.ModelCall mc) {
            return new ContextElement(bridge.methodOf(path.callerFrame), StringAnalysisChildInlining.pointsToBci(mc.inv)); // a model callback link
        }
        return null;
    }

    void mintInto(Sink sink, ValueNode n, LocalFlowGraph frame, HeapContext ctx, MethodContext mctx, RAtomKey ownerKey) {
        mintInto(sink, n, frame, ctx, mctx, ownerKey, null);
    }

    void mintInto(Sink sink, ValueNode n, LocalFlowGraph frame, HeapContext ctx, MethodContext mctx, RAtomKey ownerKey, Object freshSite) {
        bump(itemKinds, "mint");
        RAtomKey key = internKey(freshSite != null ? freshSite : siteOf(frame, n), ctx);
        if (DUMP && focused(frameName(frame)) && !atoms.containsKey(key)) {
            System.out.println("[rtrack-dump] MINT " + key + " mctx=" + mctx + " sinkRoot=" + describeRoot(sink.rootKey));
        }
        RAtom atom = atoms.computeIfAbsent(key,
                        k -> new RAtom(k, AtomKind.ALLOCATION, frame, n, mctx, ownerKey, null,
                                        length0Of(n) || n instanceof BoxNode)); // empty by construction
        if (atom.length0) {
            censusCompleteByProof.incrementAndGet();
        }
        MethodContext m = mctx != null ? mctx : MethodContext.UNKNOWN;
        // Add-then-check under the table monitor, linearised with schedule()'s set-then-snapshot: a context added
        // concurrently with the first schedule is walked by exactly one side (never lost under parallel rounds).
        boolean walkNow;
        Table mt = atom.table;
        ContainerAtoms.enterMon(mt.monitor);
        try {
            synchronized (mt.monitor) {
                walkNow = atom.mintMctxs.add(m) && mt.buildScheduled;
            }
        } finally {
            ContainerAtoms.exitMon(mt.monitor);
        }
        if (walkNow) {
            startBirthWalk(atom, m); // another minting context: its walk too (the union)
        }
        schedule(atom);
        addAtomTo(sink, key);
    }

    private void mergeMint(Sink sink, ValueNode n, LocalFlowGraph frame, int counterIdx, Object freshSite) {
        counters[counterIdx]++;
        mintInto(sink, n, frame, HeapContext.MERGED, MethodContext.UNKNOWN, null, freshSite);
    }

    /** One owner sink's state as read in a boundary's READ phase. */
    private record OwnerSnap(boolean hasSink, boolean refused, List<Object> owners) {
    }

    /**
     * Determinism: at a round boundary each pending decision must read its owner sink's final state for that round. If
     * the resolutions were decided one by one while a decision's mints run their listener cascades inline, a cascade
     * could grow or refuse another pending owner sink before that one is decided, which would then read a next-round
     * state in the (schedule-dependent) creation order of the resolutions. So a READ phase snapshots every pending owner
     * sink first, then the decisions apply.
     *
     * Cost only (an order change given the READ phase): the boundary's decisions are taken on the driver from the READ
     * snapshot, but the mints they decide are enqueued as ordinary container items and run in the next container drain.
     * The round induction is unchanged: the decisions at boundary r fix round r+1; only when its mints run within that
     * round changes.
     */
    private void boundaryApply(Runnable mint) {
        enqueue(mint);
    }

    final Counter boundaryStaleReads = new Counter();

    /**
     * The owner resolution, staged in rounds. The owner sink (the backward tracking of the allocating method's
     * {@code this}) is read only at a round boundary (quiescence); while it is still changing, no owner-specific atom is
     * minted. At the boundary the decision is taken from the owner sink's state, its final (schedule-independent) state
     * for that round (by induction over rounds):
     * <ul>
     * <li>unrefused, within the owner cap, at least one owner, round budget not exhausted ⇒ one owner-specific atom per
     * owner not yet minted;</li>
     * <li>refused / over the cap / no owner / budget exhausted with new owners pending ⇒ the MERGED
     * (context-insensitive) atom, counted; never a refusal.</li>
     * </ul>
     * Atoms minted in earlier rounds stay (monotone); once merged, the MERGED atom covers every owner (a superset table),
     * so no owner-specific atom is minted after it.
     */
    private final class OwnerResolution implements BoundaryDecision {
        final ValueNode site;
        /** The fresh site of a model's object (null: the birthplace's own site). */
        final Object freshSite;
        final LocalFlowGraph frame;
        final Sink outer;
        final int counterIdx;
        /** The minting method context for a resolved owner (OWNER(o), or a static chain ending in OWNER(o)). */
        final java.util.function.Function<RAtom, MethodContext> mctxForOwner;
        /** The MERGE (the context-insensitive atom for this site / chain). */
        final Runnable mergeAction;
        private final Set<Object> mintedOwners = ConcurrentHashMap.newKeySet();
        private volatile boolean merged;
        /** The owner tracking (the interned sink of `this`); set right after attach. */
        volatile Sink ownerSink;
        /** This boundary's decision was {@link #OD_DEFER} (read and reset by the driver only). */
        private boolean deferred;

        @Override
        public boolean deferred() {
            return deferred;
        }

        @Override
        public void keepPending() {
            deferred = false;
        }

        /** The deferred UNRESOLVABLE merge, taken at a quiet boundary. */
        @Override
        public void mergeDeferred() {
            deferred = false;
            ownerDecisions[OD_MERGE_UNRESOLVABLE]++;
            unresolvableWithSink.add(this);
            mergeNow();
        }

        OwnerResolution(ValueNode site, Object freshSite, LocalFlowGraph frame, Sink outer, int counterIdx,
                        java.util.function.Function<RAtom, MethodContext> mctxForOwner, Runnable mergeAction) {
            this.site = site;
            this.freshSite = freshSite;
            this.frame = frame;
            this.outer = outer;
            this.counterIdx = counterIdx;
            this.mctxForOwner = mctxForOwner;
            this.mergeAction = mergeAction;
        }

        /** The owner sink's state read in the boundary's READ phase (null = read live). */
        private OwnerSnap snap;

        /** The READ phase of a boundary: the owner sink's round-final state, before any decision mints. */
        void snapshot() {
            Sink os = ownerSink;
            boolean refused = os != null && os.refused();
            snap = new OwnerSnap(os != null, refused, os != null && !refused ? os.atomsSnapshot() : List.of());
        }

        /**
         * The owner decision at a round boundary. Returns true when it minted something (new work).
         * {@code budgetExhausted}: the round budget is used up; a resolution with new owners takes the merge instead.
         */
        @Override
        public boolean decide(boolean budgetExhausted) {
            Sink os = ownerSink;
            OwnerSnap sn = snap;
            snap = null;
            boolean refused;
            List<Object> owners;
            if (sn != null) {
                refused = sn.refused;
                owners = sn.owners;
                // census: did an earlier decision of this boundary change this owner sink
                // (the read-while-minting order dependence)?
                boolean liveRefused = os != null && os.refused();
                if (liveRefused != refused || (!liveRefused && os != null && os.atomCount() != owners.size())) {
                    boundaryStaleReads.incrementAndGet();
                }
            } else {
                refused = os != null && os.refused();
                owners = os != null && !refused ? os.atomsSnapshot() : List.of();
            }
            List<Object> fresh = new ArrayList<>(owners.size());
            for (Object k : owners) {
                if (!mintedOwners.contains(k)) {
                    fresh.add(k);
                }
            }
            int d = ownerDecision(merged, os != null, refused, owners.size(), fresh.size(), mintedOwners.size(), budgetExhausted, ROOT_FAN_CAP);
            deferred = d == OD_DEFER;
            if (d == OD_NONE || d == OD_DEFER) {
                return false; // OD_DEFER: roundBoundaryImpl merges it at a quiet boundary, or keeps it pending
            }
            if (d != OD_MINT_FIRST && d != OD_MINT_LATER) {
                if (d == OD_MERGE_UNRESOLVABLE && os != null) {
                    unresolvableWithSink.add(this);
                }
                ownerDecisions[d]++;
                mergeNow();
                return true;
            }
            boolean first = d == OD_MINT_FIRST;
            for (Object k : fresh) {
                RAtom owner = atoms.get(k);
                if (owner == null || !mintedOwners.add(k)) {
                    continue;
                }
                ownerDecisions[first ? OD_MINT_FIRST : OD_MINT_LATER]++;
                MethodContext m = mctxForOwner.apply(owner);
                boundaryApply(() -> mintInto(outer, site, frame, ctxFor(bridge.methodOf(frame), m), m, owner.key, freshSite));
            }
            return true;
        }

        /** The MERGE (the context-insensitive atom, a superset of every owner-specific table). */
        void mergeNow() {
            synchronized (this) {
                if (merged) {
                    return;
                }
                merged = true;
            }
            if (DUMP && (focused(frameName(frame)) || focused(describeRoot(outer.rootKey)))) {
                Sink os = ownerSink;
                StringBuilder pc = new StringBuilder();
                if (os != null) {
                    for (RTrackRefusal r : os.refusalsSnapshot()) {
                        pc.append(" {PROV ").append(r).append(":").append(provChain(os, r)).append("}");
                    }
                }
                System.out.println("[rtrack-dump] OWNER-MERGE site=" + describeNode(site) + " frame=" + frameName(frame) + " outerRoot=" + describeRoot(outer.rootKey) +
                                " ownerRoot=" + (os != null ? describeRoot(os.rootKey) + " refusals=" + os.refusalsSnapshot() + " atoms=" + os.atomCount() : "null") + pc);
            }
            boundaryApply(mergeAction);
        }

        boolean isDone() {
            return merged;
        }
    }

    /**
     * Fan-then-merge for a static-method allocation with no entering call, as a pure function (pinned by the
     * context-policy JUnit): an unenumerable caller set, no caller of a frame that is not a world-top entry, or a fan over
     * the cap ⇒ the MERGED atom; a world-top frame has no entering call by construction ⇒ the EMPTY context; otherwise ⇒
     * the fan (one call-site context per caller; an unresolvable member adds the merge).
     */
    static int staticFanDecision(boolean incomplete, int callers, boolean worldTopNoCallers, int cap) {
        if (incomplete) {
            return SF_MERGE;
        }
        if (callers == 0) {
            return worldTopNoCallers ? SF_EMPTY : SF_MERGE;
        }
        return callers > cap ? SF_MERGE : SF_FAN;
    }

    static final int SF_MERGE = 0;
    static final int SF_EMPTY = 1;
    static final int SF_FAN = 2;

    /**
     * The owner decision at a round boundary, as a pure function of the owner sink's state for the round (pinned by
     * {@code RecursiveTrackingRulesTest}). {@code owners}/{@code fresh}/{@code minted}: the sink's atom count, those not yet minted,
     * those minted in earlier rounds. Returns OD_NONE (not pending), OD_MINT_FIRST / OD_MINT_LATER (mint the fresh
     * owners), OD_DEFER (an existing but empty owner sink; merged only at a quiet boundary), or a merge reason.
     */
    static int ownerDecision(boolean merged, boolean haveSink, boolean refused, int owners, int fresh, int minted,
                    boolean budgetExhausted, int cap) {
        if (merged) {
            return OD_NONE;
        }
        if (!haveSink) {
            return OD_MERGE_UNRESOLVABLE;
        }
        if (refused) {
            return OD_MERGE_REFUSED;
        }
        if (owners > cap) {
            return OD_MERGE_CAP;
        }
        if (fresh == 0) {
            if (minted != 0) {
                return OD_NONE; // decided, unchanged
            }
            // no owner at quiescence: the merge is deferred while the round budget lasts (roundBoundaryImpl)
            return budgetExhausted ? OD_MERGE_UNRESOLVABLE : OD_DEFER;
        }
        if (budgetExhausted) {
            return OD_MERGE_BUDGET; // a counted merge at a round boundary, never a refusal
        }
        return minted == 0 ? OD_MINT_FIRST : OD_MINT_LATER;
    }

    static final int OD_NONE = -1;
    /** Owner decision census (counters; no decision reads them). */
    static final int OD_MINT_FIRST = 0;
    static final int OD_MINT_LATER = 1;
    static final int OD_MERGE_REFUSED = 2;
    static final int OD_MERGE_CAP = 3;
    static final int OD_MERGE_UNRESOLVABLE = 4;
    static final int OD_MERGE_BUDGET = 5;
    /**
     * An owner sink that exists but holds no owner (empty, unrefused, nothing minted) at a boundary, before the round
     * budget is used up. Merging it at once as UNRESOLVABLE is often premature, so the boundary merges such a resolution
     * only when it is quiet (no other decision of the same boundary minted or merged); otherwise it stays pending and the
     * next boundary re-decides it from a fresh READ snapshot. The deferred merges of one quiet boundary run together, and
     * each can still deliver owners to the others (sound: MERGE is the superset). A missing owner sink merges at once,
     * and an exhausted budget turns the deferral off (the round-budget termination argument then applies unchanged). Not
     * a census index.
     */
    static final int OD_DEFER = 6;
    static final String[] OD_NAMES = {"ownerMints", "ownerMintsLater", "mergeRefused", "mergeCap", "mergeUnresolvable", "mergeBudget"};
    final long[] ownerDecisions = new long[OD_NAMES.length];
    /** Rounds that decided something (the round count), and the per-round decision work. */
    private int ownerRounds;
    /** Census (driver only): [OD_DEFER decisions kept pending, those merged at a quiet boundary]; every UNRESOLVABLE merge with an owner sink. */
    private final long[] ownerDeferCounts = new long[2];
    private final List<OwnerResolution> unresolvableWithSink = new ArrayList<>();

    /**
     * Census: {@code ownerDefer{deferrals quietMerges laterOwners=a/n}}, where {@code a} of the {@code n}
     * UNRESOLVABLE merges with an owner sink find owners in that sink at the end (the merges that were still premature).
     */
    private String ownerDeferCensus() {
        int later = 0;
        for (OwnerResolution r : unresolvableWithSink) {
            Sink os = r.ownerSink;
            if (os != null && !os.refused() && os.atomCount() > 0) {
                later++;
            }
        }
        return " ownerDefer{deferrals=" + ownerDeferCounts[0] + " quietMerges=" + ownerDeferCounts[1] + " laterOwners=" + later + "/" + unresolvableWithSink.size() + "}";
    }

    private final List<String> roundLog = new ArrayList<>();

    /**
     * A round boundary (the caller guarantees quiescence). Every pending owner resolution is decided from its owner
     * sink's state (final for this round); returns true when a decision minted something (the next round runs).
     */
    boolean roundBoundary() {
        long t0 = System.nanoTime();
        boundaryCalls++;
        try {
            return roundBoundaryImpl();
        } finally {
            boundaryNs += System.nanoTime() - t0;
        }
    }

    /** One pending owner decision as a round boundary sees it ({@link OwnerResolution}; the JUnit's model). */
    interface BoundaryDecision {
        /** The owner decision from this boundary's READ snapshot; true = it minted or merged. */
        boolean decide(boolean budgetExhausted);

        /** The last {@link #decide} was {@link #OD_DEFER}. */
        boolean deferred();

        /** OD_DEFER at a boundary that was not quiet: the decision stays pending for the next boundary. */
        void keepPending();

        /** OD_DEFER at a quiet boundary: the merge. */
        void mergeDeferred();
    }

    /**
     * The decisions of one round boundary (the READ snapshot already taken): every pending decision is taken (in any
     * order: each reads only its own snapshot), then the OD_DEFER ones merge only when the boundary is quiet, else they
     * all stay pending. Returns the number of decisions taken (0 = the fixpoint is final). Deterministic: "quiet" is an
     * OR over the boundary's decisions. {@code census[0]} counts the deferrals kept pending, {@code census[1]} the quiet
     * merges.
     */
    static int decideBoundary(List<? extends BoundaryDecision> pending, boolean budgetExhausted, long[] census) {
        int decided = 0;
        List<BoundaryDecision> deferredHere = new ArrayList<>();
        for (BoundaryDecision r : pending) {
            if (r.decide(budgetExhausted)) {
                decided++;
            } else if (r.deferred()) {
                deferredHere.add(r);
            }
        }
        boolean quiet = decided == 0;
        for (BoundaryDecision r : deferredHere) {
            if (quiet) {
                r.mergeDeferred();
                census[1]++;
            } else {
                r.keepPending();
                census[0]++;
            }
        }
        return quiet ? deferredHere.size() : decided;
    }

    private boolean roundBoundaryImpl() {
        if (guardTripped || !queuesEmpty()) {
            return false;
        }
        List<OwnerResolution> snap;
        synchronized (ownerResolutions) {
            snap = new ArrayList<>(ownerResolutions);
        }
        boolean exhausted = ownerRounds >= OWNER_ROUND_BUDGET;
        long r0 = System.nanoTime();
        boundaryResolutions += snap.size();
        for (OwnerResolution r : snap) {
            r.snapshot(); // the READ phase
        }
        boundaryReadNs += System.nanoTime() - r0;
        int decided = decideBoundary(snap, exhausted, ownerDeferCounts);
        boolean any = decided > 0;
        synchronized (ownerResolutions) {
            // linear filter (a List-argument removeAll is quadratic at 1e6 resolutions)
            ownerResolutions.removeIf(OwnerResolution::isDone);
        }
        if (any) {
            ownerRounds++;
            roundLog.add(decided + (exhausted ? "!" : ""));
        }
        if (!any && OBJRET_DELIVER && objectReturn.objretEmptyRule()) {
            return true; // a PRECISE(empty) hook fell back at the fixpoint (more work: the drain continues)
        }
        return any;
    }

    // ------------------------------------------------------------------
    // The complete caller index. The string layer's callersOf lists only call sites some Phase-A walk materialised: a
    // call on a receiver no seed walked (e.g. `d1.get(0)` with d1 an invoke result) is absent, so every "all callers"
    // (the no-path caller fan, the merged/unknown return, the static fan) would silently miss it (counter-example: test
    // program RtCtxFactory, a false ADMIT). The index adds every call site of the points-to call graph (each universe
    // method's InvokeInfos, original callees) as a detached CallerSite; built once, lazily, in a deterministic order. A
    // call site it cannot place (a nested/inlined position, or a caller without an analysed frame) marks the callee
    // frame INCOMPLETE: its consumers refuse by name (MISSING_IR). World-top frames keep their decided (empty) caller set.
    // ------------------------------------------------------------------
    private volatile Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> irCallers;
    private final Set<LocalFlowGraph> incompleteCallers = ConcurrentHashMap.newKeySet();
    private final Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> mergedCallers = new ConcurrentHashMap<>();
    private final Counter irCallerSites = new Counter();
    private final Counter irOnlyCallerSites = new Counter();
    private final Counter irCallerProblems = new Counter();
    private long irCallerBuildMs;

    /**
     * The volatile fast path: the index is published by the single volatile write at the end of irCallerIndexBuild,
     * after every structure it covers (incompleteCallers included) is complete.
     */
    private Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> irCallerIndex() {
        Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> built = irCallers;
        return built != null ? built : irCallerIndexBuild();
    }

    private synchronized Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> irCallerIndexBuild() {
        if (irCallers != null) {
            return irCallers;
        }
        long t0 = System.nanoTime();
        Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> idx = new IdentityHashMap<>();
        List<AnalysisMethod> methods = new ArrayList<>();
        for (AnalysisMethod m : bridge.universeMethods()) {
            methods.add(m);
        }
        methods.sort((a, b) -> {
            int c = TransferFacts.methodFlowKey(a).compareTo(TransferFacts.methodFlowKey(b));
            return c != 0 ? c : TransferFacts.methodDescriptorKey(a).compareTo(TransferFacts.methodDescriptorKey(b));
        });
        for (AnalysisMethod m : methods) {
            Iterable<? extends com.oracle.graal.pointsto.meta.InvokeInfo> invokes;
            try {
                invokes = m.getInvokes();
            } catch (Throwable t) {
                continue; // no type-flow graph: the method is not analysed code (nothing to enumerate)
            }
            if (invokes == null) {
                continue;
            }
            LocalFlowGraph callerFrame = bridge.frameOf(m);
            for (com.oracle.graal.pointsto.meta.InvokeInfo ii : invokes) {
                Iterable<AnalysisMethod> callees;
                try {
                    callees = ii.getOriginalCallees();
                } catch (Throwable t) {
                    continue;
                }
                jdk.vm.ci.code.BytecodePosition pos = ii.getPosition();
                for (AnalysisMethod callee : callees) {
                    LocalFlowGraph cf = bridge.frameOf(callee);
                    if (cf == null) {
                        continue; // a callee nobody can walk into
                    }
                    if (callerFrame == null || pos == null || pos.getCaller() != null) {
                        irCallerProblems.incrementAndGet();
                        incompleteCallers.add(cf);
                        continue;
                    }
                    int bci = pos.getBCI();
                    List<ForwardFixpoint.CallerSite> l = idx.computeIfAbsent(cf, k -> new ArrayList<>(2));
                    boolean dup = false;
                    for (ForwardFixpoint.CallerSite c : l) {
                        if (c.call().owner == callerFrame && c.call().bci == bci) {
                            dup = true;
                            break;
                        }
                    }
                    if (!dup) {
                        LocalFlowGraph.LocalVertex d = new LocalFlowGraph.LocalVertex(callerFrame, -1, LocalFlowGraph.VertexKind.INVOKE_CALLSITE);
                        d.bci = bci;
                        d.calleeMethod = callee;
                        List<ValueNode> invs = invokesByBci(callerFrame, bci);
                        d.irNode = invs.size() == 1 ? invs.get(0) : null;
                        l.add(new ForwardFixpoint.CallerSite(m, d));
                        irCallerSites.incrementAndGet();
                    }
                }
            }
        }
        irCallerBuildMs = (System.nanoTime() - t0) / 1_000_000;
        irCallers = idx;
        return idx;
    }

    // ------------------------------------------------------------------
    // World-top and caller-less frames.
    // ------------------------------------------------------------------

    /**
     * The pending allowlist: exact declaring class -> exact field names ({@code "*"} = every field of that exact class). A
     * listed class or named field that does not exist is a loud scan failure ({@code [rtrack-e2] ADDRESS-ALLOWLIST-MISSING}).
     */
    static final Map<String, List<String>> PENDING_ALLOWLIST = Map.of(
                    "com.oracle.svm.core.jni.access.JNIAccessibleMethod", List.of("nonvirtualTarget", "newObjectTarget", "callWrapper", "varargsWrapper", "arrayWrapper",
                                    "valistWrapper", "varargsNonvirtualWrapper", "arrayNonvirtualWrapper", "valistNonvirtualWrapper"),
                    "com.oracle.svm.core.c.BoxedRelocatedPointer", List.of("pointer"),
                    "com.oracle.svm.core.c.CIsolateData", List.of("offset"),
                    "com.oracle.svm.core.code.ImageCodeInfo", List.of("*"),
                    "com.oracle.svm.core.jni.access.JNIAccessibleField", List.of("id"));

    /** World-top census (print-only; out of every verdict layer). */
    final Counter e2WorldTopExit = new Counter();
    final Counter e2WorldTopEntryWithCallers = new Counter();
    final Counter e2NoCallerExit = new Counter();
    final Counter e2OwnerRetWorldTop = new Counter();
    final Counter e2StaticOutsideMint = new Counter();
    final Counter e2StringWorldTopExit = new Counter();
    final Counter e2StringNoCallerExit = new Counter();
    /** World-top census: the frames per rule (event|frame), printed sorted at census time. */
    final Map<String, Set<String>> e2Frames = new ConcurrentHashMap<>();
    volatile Set<AnalysisMethod> virtualReached;
    volatile int virtualRootCount;
    volatile int virtualReadFailures;
    /** The virtual roots' names (the predicate's sources; kept as collected, not printed). */
    final Set<String> virtualRootNames = ConcurrentHashMap.newKeySet();
    final Map<LocalFlowGraph, Boolean> outsideMemo = new ConcurrentHashMap<>();

    final Map<LocalFlowGraph, Boolean> narrowMemo = new ConcurrentHashMap<>();

    volatile Set<AnalysisMethod> virtualReachedNonRefl;

    /**
     * The world-top predicate sets' build lock (a dedicated monitor under the lock-order tripwire; the builds take no
     * other monitor).
     */
    final Object e2BuildLock = new Object();

    // ---- the address-taken methods (MethodPointer targets) ----
    volatile Set<AnalysisMethod> addressTakenSet;
    volatile int addressScanFailures;
    volatile String addressCensus = "";
    static final Object READ_ERROR = new Object();
    /** Census only: the classes of the unread (pending) values in read word slots. */
    final Map<String, Integer> addressPendingClasses = new ConcurrentHashMap<>();

    volatile Set<AnalysisMethod> addressTakenUnmodelledSet;
    volatile int addressAccessorSlotsSkipped;
    volatile int pendingUnconfirmed;

    private final Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> bridgedMergedCallers = new ConcurrentHashMap<>();

    final Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> fanCallersMemo = new ConcurrentHashMap<>();
    /** Caller-filter census (print-only): frames filtered, sites examined, sites dropped, frames un-emptied, keep reasons. */
    final AtomicLong cptFrames = new AtomicLong();
    final AtomicLong cptFramesNarrowed = new AtomicLong();
    final AtomicLong cptSites = new AtomicLong();
    final AtomicLong cptDropped = new AtomicLong();
    final AtomicLong cptUnemptied = new AtomicLong();
    final AtomicLong cptContra = new AtomicLong();
    final AtomicLong cptContraUnchecked = new AtomicLong();
    final Map<String, AtomicLong> cptKeep = new ConcurrentHashMap<>();

    /**
     * The container engine's callers of {@code frame}: {@link #stringCallersOf} plus the bridged
     * reflective call sites, keyed by IR node (dedup by the call descriptor).
     */
    List<ForwardFixpoint.CallerSite> callersOf(LocalFlowGraph frame) {
        List<ForwardFixpoint.CallerSite> base = stringCallersOf(frame);
        List<ForwardFixpoint.CallerSite> cached = bridgedMergedCallers.get(frame);
        if (cached != null) {
            return cached;
        }
        List<ForwardFixpoint.CallerSite> br = reflBridge().callersOf(frame);
        if (br.isEmpty()) {
            return base;
        }
        List<ForwardFixpoint.CallerSite> out = new ArrayList<>(base != null ? base : List.of());
        for (ForwardFixpoint.CallerSite c : br) {
            boolean present = false;
            for (ForwardFixpoint.CallerSite e : out) {
                if (e.call() == c.call() || e.call() != null && e.call().irNode != null && e.call().irNode == c.call().irNode) {
                    present = true;
                    break;
                }
            }
            if (!present) {
                out.add(c);
            }
        }
        List<ForwardFixpoint.CallerSite> prev = bridgedMergedCallers.putIfAbsent(frame, out);
        return prev != null ? prev : out;
    }

    /**
     * The complete callers of {@code frame} without the bridge: the LFG's sites, then the IR-only sites (dedup by
     * (caller frame, bci)).
     */
    List<ForwardFixpoint.CallerSite> stringCallersOf(LocalFlowGraph frame) {
        List<ForwardFixpoint.CallerSite> lfg = bridge.callersOf(frame);
        List<ForwardFixpoint.CallerSite> cached = mergedCallers.get(frame);
        if (cached != null) {
            return cached;
        }
        List<ForwardFixpoint.CallerSite> out = new ArrayList<>(lfg != null ? lfg : List.of());
        List<ForwardFixpoint.CallerSite> ir = irCallerIndex().get(frame);
        if (ir != null) {
            for (ForwardFixpoint.CallerSite c : ir) {
                boolean present = false;
                for (ForwardFixpoint.CallerSite e : out) {
                    if (e.call() != null && e.call().owner == c.call().owner && e.call().bci == c.call().bci) {
                        present = true;
                        break;
                    }
                }
                if (!present) {
                    out.add(c);
                    irOnlyCallerSites.incrementAndGet();
                }
            }
        }
        List<ForwardFixpoint.CallerSite> prev = mergedCallers.putIfAbsent(frame, out);
        return prev != null ? prev : out;
    }

    /** The container engine's incompleteness: {@link #callersIncomplete} or a bridged caller the bridge could not place. */
    boolean containerCallersIncomplete(LocalFlowGraph frame) {
        return callersIncomplete(frame) || reflBridge().incomplete(frame);
    }

    /** True when the index could not place some caller of {@code frame} (consumers refuse by name). */
    boolean callersIncomplete(LocalFlowGraph frame) {
        irCallerIndex();
        return incompleteCallers.contains(frame);
    }

    // ------------------------------------------------------------------
    // Constant atoms and static tables.
    // ------------------------------------------------------------------
    RAtom constantAtom(ImageHeapConstant ihc) {
        Object site = ihc.getConstantData();
        RAtomKey key = internKey(site, HeapContext.EMPTY); // a constant is global: no ctx
        RAtom atom = atoms.get(key);
        if (atom == null) {
            boolean len0 = false;
            boolean primitiveArray = false;
            if (ihc instanceof ImageHeapObjectArray oa) {
                len0 = oa.getLength() == 0;
            } else if (ihc instanceof ImageHeapPrimitiveArray pa) {
                // no reference members: complete by proof (same JVM-semantics class as length-0)
                len0 = true;
                primitiveArray = pa.getLength() > 0;
            }
            RAtom fresh = new RAtom(key, AtomKind.CONSTANT, null, null, MethodContext.UNKNOWN, null, ihc, len0);
            RAtom winner = atoms.putIfAbsent(key, fresh);
            atom = winner != null ? winner : fresh;
            if (winner == null) {
                if (primitiveArray) {
                    primitiveArrayProofs.incrementAndGet();
                } else if (len0) {
                    censusCompleteByProof.incrementAndGet();
                }
            }
        }
        schedule(atom);
        return atom;
    }

    /** One build-time store per field/element, read lazily, never executing a future. */
    private void buildTimeStores(RAtom atom) {
        ImageHeapConstant ihc = atom.constant;
        if (ihc instanceof ImageHeapInstance inst) {
            for (ResolvedJavaField rf : ihc.getType().getInstanceFields(true)) {
                if (rf.getJavaKind() != JavaKind.Object) {
                    continue;
                }
                AnalysisField f = bridge.resolveField(rf);
                if (f == null) {
                    refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE);
                    continue;
                }
                Object v;
                try {
                    v = inst.getFieldValue(f);
                } catch (Throwable t) {
                    v = PENDING;
                }
                if (models.heapFill(atom, f, v)) {
                    continue; // a modelled container's representation fills its slot (the model engine's)
                }
                appendBuildTimeStore(atom.table, atom.key, f, v, -1);
            }
        } else if (ihc instanceof ImageHeapObjectArray oa) {
            for (int i = 0; i < oa.getLength(); i++) {
                Object v;
                try {
                    v = oa.getElement(i);
                } catch (Throwable t) {
                    v = PENDING;
                }
                appendBuildTimeStore(atom.table, atom.key, ARRAY_ELEMENT, v, i);
            }
        }
    }

    static final Object PENDING = new Object();

    private static String describeSnapshot(Object v) {
        if (v instanceof java.util.concurrent.Future<?> fut) {
            return "FUTURE(done=" + fut.isDone() + ")";
        }
        return v == PENDING ? "PENDING" : String.valueOf(v);
    }

    /**
     * A build-time store into {@code holder.member} (index {@code idx} for arrays, part of the dedup key: every element
     * is its own store). A value that is not yet a constant (a pending future) is a named refusal.
     */
    void appendBuildTimeStore(Table holder, Object holderId, Object member, Object v, int idx) {
        if (v == null) {
            return;
        }
        if (!(v instanceof JavaConstant jc)) {
            heapSnapshotPending.incrementAndGet();
            refuse(holder, RTrackRefusal.HEAP_SNAPSHOT_PENDING);
            return;
        }
        if (!(jc instanceof ImageHeapConstant value)) {
            return; // a null/primitive build-time value: nothing to track
        }
        models.fieldRule(holder, member, "heap-container"); // an image-heap container of a modelled class (refused)
        EntryList<StoreEntry> list = holder.stores(member);
        Object node = List.of("buildtime", holderId, idx);
        StoreEntry e = new StoreEntry(null, node, value, null, MethodContext.UNKNOWN);
        if (list.append(e, e.dedupKey(), e.nodeKey()) >= 0) {
            censusStoreEntries.incrementAndGet();
            if (list.distinctNodeCount() > STORE_FAN_CAP) {
                refuse(holder, RTrackRefusal.STORE_FAN_CAP);
            }
        }
        // The build-time store is a store: its value escapes into holder.member
        // (found again only at the loads of holder.member). Recorded
        // lazily: the escape is registered when the value's atom is scheduled.
        Object[] rec = {holder, member};
        List<Object[]> hs = buildTimeHolders.computeIfAbsent(value.getConstantData(), k -> new ArrayList<>(1));
        RAtom valueAtom;
        RAtom twin = null;
        synchronized (hs) {
            hs.add(rec);
            valueAtom = atoms.get(internKey(value.getConstantData(), HeapContext.EMPTY));
            if (OBJRET_ON) {
                twin = objectReturn.heapBirthTwin(value.getConstantData()); // the heap birth's query atom
            }
        }
        if (valueAtom != null && valueAtom.table.buildScheduled) {
            buildTimeEscape(valueAtom, holder, member);
        }
        if (twin != null && twin.table.buildScheduled) {
            buildTimeEscape(twin, holder, member);
        }
    }

    private void registerBuildTimeEscapes(RAtom atom) {
        List<Object[]> hs = buildTimeHolders.get(constantSiteOf(atom));
        if (hs == null) {
            return;
        }
        List<Object[]> snap;
        synchronized (hs) {
            snap = new ArrayList<>(hs);
        }
        for (Object[] rec : snap) {
            buildTimeEscape(atom, (Table) rec[0], rec[1]);
        }
    }

    // ------------------------------------------------------------------
    // The reverse heap index: every heap holder of a constant K (a build-time object H with H.f == K / H[i] == K, or a
    // static whose build-time value is K) is a use of K's identity: K is found again at the loads of H.f, which only H's
    // table records. Built lazily, once, never executing a future. Every holder of K gets scheduled. The gap is never
    // silent: over its build budget, incomplete (a read reference slot still a pending future), or a
    // holder fan over the cap ⇒ CONSTANT_HOLDERS_UNINDEXED on T(K).
    // ------------------------------------------------------------------
    /** The index build budget: reference slots scanned (0 = unbounded). */
    static final long HEAP_INDEX_BUDGET = Long.getLong("svm.stringanalysis.fwd.rtrack.heapindexbudget", 100_000_000L);
    /** A constant with more heap holders than this refuses its table by name (0 = off). */
    static final int HOLDER_FAN_CAP = Integer.getInteger("svm.stringanalysis.fwd.rtrack.holderfan", 0);

    volatile Map<Object, List<Object[]>> holderIndex;
    /**
     * The declared types of the read reference slots that are still pending futures: such a slot may hold any constant K
     * whose type is assignable to the declared type, so K's holder set is not provably complete (its table refuses by
     * name). Only primitive-array declared types are kept here; any other pending slot sets {@link #pendingUnknownType}.
     */
    final Set<AnalysisType> pendingSlotTypes = ConcurrentHashMap.newKeySet();
    final Map<String, Counter> pendingSlotsBy = new ConcurrentHashMap<>();

    volatile boolean pendingUnknownType;

    volatile String holderIndexProblem; // null = complete
    private boolean holderIndexBuilt;
    final Counter heapIndexObjects = new Counter();
    final AtomicLong heapIndexSlots = new AtomicLong();
    final Counter heapIndexEdges = new Counter();
    final Counter heapIndexPendingRead = new Counter();
    final Counter heapIndexPendingUnread = new Counter();
    final AtomicLong heapIndexBuildMs = new AtomicLong();
    final Counter heapHoldersScheduled = new Counter();
    final Counter constantsNeedingHolders = new Counter();
    final long[] holderFanHist = new long[8];

    final Counter pendingReferenceFree = new Counter();
    /** The record-commit translations of a non-null component (a collector record; census {@code recordCommit}). */
    final Counter recordCommitStores = new Counter();

    synchronized Map<Object, List<Object[]>> holderIndex() {
        if (holderIndexBuilt) {
            return holderIndex;
        }
        holderIndexBuilt = true;
        long t0 = System.nanoTime();
        Map<Object, List<Object[]>> idx = new java.util.HashMap<>();
        String problem = null;
        Map<AnalysisType, Set<ImageHeapConstant>> objs = bridge.heapObjects();
        if (objs == null) {
            problem = "heap-unavailable";
        } else {
            outer: for (Map.Entry<AnalysisType, Set<ImageHeapConstant>> e : objs.entrySet()) {
                for (ImageHeapConstant h : e.getValue()) {
                    heapIndexObjects.incrementAndGet();
                    if (h instanceof ImageHeapInstance inst) {
                        for (ResolvedJavaField rf : h.getType().getInstanceFields(true)) {
                            if (rf.getJavaKind() != JavaKind.Object) {
                                continue;
                            }
                            AnalysisField f = bridge.resolveField(rf);
                            if (f == null) {
                                problem = "unresolved-field";
                                break outer;
                            }
                            if (HEAP_INDEX_BUDGET > 0 && heapIndexSlots.incrementAndGet() > HEAP_INDEX_BUDGET) {
                                problem = "budget";
                                break outer;
                            }
                            Object v;
                            try {
                                v = inst.getFieldValue(f);
                            } catch (Throwable t) {
                                v = PENDING;
                            }
                            if (reverseHeap.indexSlot(idx, v, h, f, f.isRead())) {
                                reverseHeap.notePending(f.getType(), "field " + f.format("%H.%n"));
                                objectIdentity.notePendingSlot("field " + f.format("%H.%n"), objectIdentity.declaredSlotTypes(f));
                            }
                            if (v != null && !(v instanceof JavaConstant) && models.heapSlot(f) != null) {
                                // A still-pending representation array: its unknown elements
                                // admit every constant (as a pending element does below)
                                reverseHeap.notePending(null, "representation " + f.format("%H.%n"));
                                objectIdentity.notePendingSlot("representation " + f.format("%H.%n"), null);
                            }
                            JdkModels.Slot fill = v instanceof ImageHeapObjectArray ? models.heapSlot(f) : null;
                            if (fill != null) {
                                // The heap fill's reverse edges: each representation element is held by h's slot
                                ImageHeapObjectArray arr = (ImageHeapObjectArray) v;
                                for (int i = 0; i < arr.getLength(); i++) {
                                    Object ev;
                                    try {
                                        ev = arr.getElement(i);
                                    } catch (Throwable t) {
                                        ev = PENDING;
                                    }
                                    if (reverseHeap.indexSlot(idx, ev, h, fill, true)) {
                                        reverseHeap.notePending(null, "representation " + f.format("%H.%n"));
                                        objectIdentity.notePendingSlot("representation " + f.format("%H.%n"), null);
                                    }
                                }
                            }
                        }
                    } else if (h instanceof ImageHeapObjectArray oa) {
                        for (int i = 0; i < oa.getLength(); i++) {
                            if (HEAP_INDEX_BUDGET > 0 && heapIndexSlots.incrementAndGet() > HEAP_INDEX_BUDGET) {
                                problem = "budget";
                                break outer;
                            }
                            Object v;
                            try {
                                v = oa.getElement(i);
                            } catch (Throwable t) {
                                v = PENDING;
                            }
                            if (reverseHeap.indexSlot(idx, v, h, ARRAY_ELEMENT, true)) {
                                AnalysisType at = h.getType() instanceof AnalysisType t ? t : null;
                                reverseHeap.notePending(at != null ? at.getComponentType() : null, "array " + (at != null ? at.toJavaName(true) : "?"));
                                objectIdentity.notePendingSlot("array " + (at != null ? at.toJavaName(true) : "?"), at != null ? List.of(at.getComponentType()) : null);
                            }
                        }
                    }
                }
            }
            Iterable<AnalysisField> statics = bridge.staticFields();
            if (statics == null) {
                problem = problem != null ? problem : "statics-unavailable";
            } else if (problem == null) {
                for (AnalysisField f : statics) {
                    if (!f.isRead() || !(f.getDeclaringClass().isInitialized() || bridge.classInitSimulated(f.getDeclaringClass()))) { // incl. simulated
                        continue; // never read: no load / runtime-initialized: no build-time value
                    }
                    Object v = buildTimeStaticValue(f); // one rule with the static table
                    if (reverseHeap.indexSlot(idx, v, f, f, true)) {
                        reverseHeap.notePending(f.getType(), "static " + f.format("%H.%n"));
                        objectIdentity.notePendingSlot("static " + f.format("%H.%n"), objectIdentity.declaredSlotTypes(f));
                    }
                }
            }
        }
        heapIndexBuildMs.set((System.nanoTime() - t0) / 1_000_000);
        holderIndexProblem = problem;
        holderIndex = idx;
        System.err.println("[sug-fwd-rtrack-heapindex] objects=" + heapIndexObjects.get() + " slots=" + heapIndexSlots.get() +
                        " edges=" + heapIndexEdges.get() + " keys=" + idx.size() + " pendingRead=" + heapIndexPendingRead.get() +
                        " pendingUnread=" + heapIndexPendingUnread.get() + " pendingTypes=" + pendingSlotTypes.size() + " problem=" + problem +
                        " ms=" + heapIndexBuildMs.get() + " pendingBy=" + top(pendingSlotsBy));
        return idx;
    }

    /**
     * The build-time escape of {@code atom} into {@code holder.member}. The waiter inherits the holder's refusals, so the
     * build-time elements C of a representation array A that the field rule refuses (A the value of an abstracted field
     * of a heap container H) inherit A's refusal: C's table is never silently missing the model loads of H's slot. C's
     * holders (A) and A's holders (H) are scheduled through the reverse heap index, whose incompleteness refuses by name.
     */
    private void buildTimeEscape(RAtom atom, Table holder, Object member) {
        markStored(atom); // an image-heap holder (never a runtime-born STRING atom; conservative)
        if (models.fieldRule(atom.table, member, "heap-escape")) {
            return; // a heap value inside a modelled container's representation
        }
        EntryList<LoadEntry> list = holder.loads(member);
        register(list, List.of("esc-bt", atom.key), idx -> continueAt(atom, list.get(idx), member), null, atom.table);
    }

    Table staticTable(AnalysisField f) {
        Table existing = staticTables.get(f);
        if (existing != null) {
            return existing;
        }
        Table t = new Table(f, false);
        Table winner = staticTables.putIfAbsent(f, t);
        if (winner != null) {
            return winner;
        }
        censusStaticTables.incrementAndGet();
        checkReflectiveField(t, f);
        if (argStampIndex == null) {
            refuse(t, RTrackRefusal.MISSING_IR);
            return t;
        }
        // The runtime-code stores+loads of f, from the same-pass index.
        for (AnalysisMethod m : argStampIndex.rtrackStaticAccessMethods(f)) {
            LocalFlowGraph frame = bridge.frameOf(m);
            StructuredGraph g = frame != null ? graphOf(frame) : null;
            if (frame == null || g == null) {
                refuse(t, RTrackRefusal.MISSING_IR);
                continue;
            }
            for (Node node : g.getNodes()) {
                if (node instanceof StoreFieldNode sfn && sfn.field().isStatic() && bridge.resolveField(sfn.field()) == f) {
                    if (f.getJavaKind() != JavaKind.Object) {
                        continue;
                    }
                    StoreEntry e = new StoreEntry(frame, sfn, sfn.value(), null, MethodContext.UNKNOWN);
                    if (t.stores(f).append(e, e.dedupKey(), e.nodeKey()) >= 0) {
                        censusStoreEntries.incrementAndGet();
                        if (t.stores(f).distinctNodeCount() > STORE_FAN_CAP) {
                            refuse(t, RTrackRefusal.STORE_FAN_CAP);
                        }
                    }
                } else if (node instanceof LoadFieldNode lfn && lfn.field().isStatic() && bridge.resolveField(lfn.field()) == f) {
                    LoadEntry e = new LoadEntry(frame, lfn, null, MethodContext.UNKNOWN);
                    if (t.loads(f).append(e, e.dedupKey()) >= 0) {
                        censusLoadEntries.incrementAndGet();
                    }
                }
            }
        }
        // The build-time value, read without executing a future. Only a class whose <clinit> ran at build time has one
        // (a run-time-initialized class's <clinit> is analysed code, in the scan above). "Ran at build time" includes a
        // simulated class initializer (not isInitialized(), statics are snapshot values); an isInitialized()-only test
        // would drop such a static's value silently.
        boolean buildTime = f.getDeclaringClass().isInitialized() || bridge.classInitSimulated(f.getDeclaringClass());
        if (f.getJavaKind() == JavaKind.Object && !buildTime) {
            // Never silent: a runtime-initialized class's <clinit> must be analysed code (the
            // scan above then saw its stores); an initializer outside the analysed universe is
            // an unseen writer: a named refusal.
            AnalysisMethod clinit = null;
            try {
                clinit = f.getDeclaringClass().getClassInitializer();
            } catch (Throwable ignore) {
                // no initializer
            }
            if (clinit != null && bridge.frameOf(clinit) == null) {
                staticWriterUnseen.incrementAndGet();
                refuse(t, RTrackRefusal.MISSING_IR);
            }
        }
        if (DUMP && focused(f.format("%H.%n"))) {
            AnalysisMethod ci = null;
            try {
                ci = f.getDeclaringClass().getClassInitializer();
            } catch (Throwable ignore) {
                // none
            }
            System.out.println("[rtrack-dump] STATIC-TABLE " + f.format("%H.%n") + " initialized=" + f.getDeclaringClass().isInitialized() + " simulated=" +
                            bridge.classInitSimulated(f.getDeclaringClass()) + " clinit=" + ci + " clinitFrame=" + (ci != null && bridge.frameOf(ci) != null) +
                            " scanned=" + argStampIndex.rtrackStaticAccessMethods(f) + " btValue=" + describeSnapshot(buildTimeStaticValue(f)));
        }
        if (f.getJavaKind() == JavaKind.Object && buildTime) {
            appendBuildTimeStore(t, f, f, buildTimeStaticValue(f), -1);
        }
        return t;
    }

    /**
     * The build-time value of a static of a class that ran its initializer at build time (initialized, or simulated),
     * read without executing a future, in SVM's own read order ({@code AnalysisConstantReflectionProvider.readValue}):
     * the simulation's published value if the simulated {@code <clinit>} stored the field, otherwise the shadow heap's
     * static value ({@code getDataIfComputed().getFieldValue}). Not computed / a pending future ⇒ PENDING
     * ({@code HEAP_SNAPSHOT_PENDING}). One rule for the static table and the reverse heap index's static holders.
     */
    Object buildTimeStaticValue(AnalysisField f) {
        try {
            if (!f.getDeclaringClass().isInitialized()) {
                JavaConstant sv = bridge.simulatedStaticValue(f); // the simulation's published value
                if (sv != null) {
                    return sv;
                }
            }
            TypeData td = f.getDeclaringClass().getDataIfComputed();
            return td != null ? td.getFieldValue(f) : PENDING;
        } catch (Throwable ignore) {
            return PENDING;
        }
    }

    private final Counter staticWriterUnseen = new Counter();

    // ------------------------------------------------------------------
    // The pools' IR adapter: (frame, member) → FrameCfg from the fixed IR.
    // ------------------------------------------------------------------
    FrameCfg frameCfgOf(LocalFlowGraph frame, Object member) {
        List<Object> key = List.of(frame, member);
        FrameCfg cached = frameCfgCache.get(key);
        if (cached != null) {
            return cached;
        }
        FrameCfg cfg = computeFrameCfg(frame, member);
        frameCfgCache.put(key, cfg);
        return cfg;
    }

    private Object[] blocksOf(LocalFlowGraph frame) {
        return frameBlocks.computeIfAbsent(frame, f -> {
            StructuredGraph g = graphOf(f);
            if (g == null) {
                return new Object[]{new HIRBlock[0], new int[0][], 0};
            }
            ControlFlowGraph cfg;
            synchronized (g) {
                try {
                    cfg = ControlFlowGraph.computeForSchedule(g);
                } catch (Throwable t) {
                    return new Object[]{new HIRBlock[0], new int[0][], 0};
                }
            }
            HIRBlock[] blocks = cfg.getBlocks();
            Map<HIRBlock, Integer> index = new IdentityHashMap<>();
            for (int i = 0; i < blocks.length; i++) {
                index.put(blocks[i], i);
            }
            List<List<Integer>> tmp = new ArrayList<>(blocks.length);
            for (int i = 0; i < blocks.length; i++) {
                tmp.add(new ArrayList<>(2));
            }
            for (int b = 0; b < blocks.length; b++) {
                for (int s = 0; s < blocks[b].getSuccessorCount(); s++) {
                    Integer si = index.get(blocks[b].getSuccessorAt(s));
                    if (si != null) {
                        tmp.get(si).add(b);
                    }
                }
            }
            int[][] preds = new int[blocks.length][];
            for (int i = 0; i < blocks.length; i++) {
                preds[i] = tmp.get(i).stream().mapToInt(Integer::intValue).toArray();
            }
            Integer entry = index.get(cfg.getStartBlock());
            return new Object[]{blocks, preds, entry != null ? entry : 0};
        });
    }

    /**
     * A fixed node that may run analysed code (so the same method may re-enter on the same object before the next node):
     * an invoke, a foreign call (over-inclusive), a class initialisation check.
     */
    private static boolean mayRunCode(Node fn) {
        return fn instanceof Invoke || fn instanceof jdk.graal.compiler.nodes.extended.ForeignCall ||
                        fn.getClass().getSimpleName().equals("EnsureClassInitializedNode");
    }

    /**
     * The positions at which the SSA value {@code w} is (re-)defined: a fixed node: its own position; a phi: its merge's
     * block start; a parameter/constant: none (defined once per invocation); any other floating value: the union of its
     * inputs' definition points. Returns false when a position cannot be located: the caller makes that receiver
     * never-kill (sound).
     */
    private static boolean defPointsOf(Node w, Map<Node, int[]> pos, Map<Node, Integer> mergeBlock, Set<Node> seen,
                    List<int[]> out) {
        if (!seen.add(w)) {
            return true;
        }
        if (w instanceof ParameterNode || w instanceof ConstantNode) {
            return true;
        }
        if (w instanceof PhiNode phi) {
            Integer b = mergeBlock.get(phi.merge());
            if (b == null) {
                return false;
            }
            out.add(new int[]{b, -1});
            return true;
        }
        int[] p = pos.get(w);
        if (p != null) {
            out.add(new int[]{p[0], p[1] * 2 + 1});
            return true;
        }
        if (w instanceof jdk.graal.compiler.nodes.FixedNode) {
            return false; // a fixed node outside the schedule: cannot locate
        }
        boolean ok = true;
        for (Node in : w.inputs()) {
            ok &= defPointsOf(in, pos, mergeBlock, seen, out);
        }
        return ok;
    }

    private FrameCfg computeFrameCfg(LocalFlowGraph frame, Object member) {
        Object[] bp = blocksOf(frame);
        HIRBlock[] blocks = (HIRBlock[]) bp[0];
        int[][] preds = (int[][]) bp[1];
        if (blocks.length == 0) {
            return new FrameCfg(0, new int[0][], List.of());
        }
        int entryBlock = (Integer) bp[2];
        List<PoolAccess> accesses = new ArrayList<>();
        List<ContainerTables.PoolEvent> events = new ArrayList<>();
        Map<Node, int[]> pos = new IdentityHashMap<>();
        Map<Node, Integer> mergeBlock = new IdentityHashMap<>();
        int seq = 0;
        for (int b = 0; b < blocks.length; b++) {
            if (blocks[b].getBeginNode() instanceof jdk.graal.compiler.nodes.AbstractMergeNode mn) {
                mergeBlock.put(mn, b);
            }
            int order = 0;
            for (Node fn : blocks[b].getNodes()) {
                int base = order * 2;
                pos.put(fn, new int[]{b, order});
                if (mayRunCode(fn)) {
                    events.add(ContainerTables.PoolEvent.invoke(b, base + 1));
                }
                if (member == ARRAY_ELEMENT) {
                    if (fn instanceof StoreIndexedNode sin) {
                        accesses.add(new PoolAccess(seq++, true, sin.array(), b, base, sin));
                    } else if (fn instanceof LoadIndexedNode lin) {
                        accesses.add(new PoolAccess(seq++, false, lin.array(), b, base, lin));
                    } else if (fn instanceof BasicArrayCopyNode acn && acn.getSource() != null && acn.getDestination() != null) {
                        // The desugared pair sits load-before-store.
                        accesses.add(new PoolAccess(seq++, false, acn.getSource(), b, base, acn));
                        accesses.add(new PoolAccess(seq++, true, acn.getDestination(), b, base + 1, acn));
                    }
                } else if (member instanceof AnalysisField af && !af.isStatic()) {
                    if (fn instanceof StoreFieldNode sfn && !sfn.field().isStatic() && bridge.resolveField(sfn.field()) == af) {
                        accesses.add(new PoolAccess(seq++, true, sfn.object(), b, base, sfn));
                    } else if (fn instanceof LoadFieldNode lfn && !lfn.field().isStatic() && bridge.resolveField(lfn.field()) == af) {
                        accesses.add(new PoolAccess(seq++, false, lfn.object(), b, base, lfn));
                    }
                }
                order++;
            }
        }
        // Every receiver's definition points (DEF events); an unlocatable one is never-kill.
        Set<Object> neverKill = new java.util.HashSet<>();
        Set<Object> done = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        for (PoolAccess a : accesses) {
            if (member == ARRAY_ELEMENT && a.receiver != null) {
                // Soundness (the array member `[]` is index-insensitive): an element store a[i] = x does not overwrite
                // a[j] (and a desugared arraycopy writes only a range), so a `[]` store proves no kill, of a store
                // version or of E_w. `a[0] = s; a[1] = t; x = a[0];` must let s reach x. Array receivers are therefore
                // never-kill. No switch is offered: the killing form is unsound.
                neverKill.add(a.receiver);
            }
            if (!(a.receiver instanceof Node w) || !done.add(w)) {
                continue;
            }
            List<int[]> dps = new ArrayList<>(2);
            if (!defPointsOf(w, pos, mergeBlock, java.util.Collections.newSetFromMap(new IdentityHashMap<>()), dps)) {
                neverKill.add(w);
                continue;
            }
            for (int[] dp : dps) {
                events.add(ContainerTables.PoolEvent.def(w, dp[0], dp[1]));
            }
        }
        return new FrameCfg(blocks.length, preds, accesses, entryBlock, events, neverKill);
    }

    // ------------------------------------------------------------------
    // Length-0: the array's length value has stamp exactly [0,0].
    // ------------------------------------------------------------------
    static boolean length0Of(ValueNode n) {
        ValueNode len = null;
        if (n instanceof NewArrayNode nan) {
            len = nan.length();
        } else if (n instanceof NewArrayWithExceptionNode nwe) {
            len = nwe.length();
        } else if (n instanceof DynamicNewArrayNode dn) {
            len = dn.length();
        }
        return len != null && stampExactlyZero(len);
    }

    static boolean stampExactlyZero(ValueNode len) {
        try {
            Stamp s = len.stamp(NodeView.DEFAULT);
            return s instanceof IntegerStamp is && is.lowerBound() == 0 && is.upperBound() == 0;
        } catch (Throwable t) {
            return false;
        }
    }

    // ------------------------------------------------------------------
    // The [rtrack-dump] table census (marker-gated).
    // ------------------------------------------------------------------
    private void dumpTables() {
        List<RAtom> sorted = new ArrayList<>(atoms.values());
        sorted.sort((a, b) -> a.key.toString().compareTo(b.key.toString()));
        for (RAtom a : sorted) {
            if (!focused(frameName(a.birthFrame) + " " + a.key)) {
                continue;
            }
            System.out.println("[rtrack-dump] atom=" + a.key + " kind=" + a.kind + " birth=" + frameName(a.birthFrame) +
                            " length0=" + a.length0 + " steps=" + a.steps.get() +
                            (a.table.refusalsSnapshot().isEmpty() ? ""
                                            : " refusals=" + a.table.refusalsSnapshot() + " firstAt=" +
                                                            refusalOrigin.get(a.table)));
            for (RTrackRefusal r : a.table.refusalsSnapshot()) {
                System.out.println("[rtrack-dump]   PROV " + r + ":" + provChain(a.table, r));
            }
            List<String> wl = dumpWalkLog.get(a.key);
            if (wl != null) {
                // the focused atom's walk positions
                synchronized (wl) {
                    for (int i = 0; i < wl.size() && i < 20000; i++) {
                        System.out.println("[rtrack-dump]   WALK " + i + " " + wl.get(i));
                    }
                }
            }
            if (a.kind == AtomKind.STRING) {
                // a STRING atom's recorded usages and escapes
                List<String> us = new ArrayList<>();
                for (TransferFacts.UsageFact uf : a.strUsages) {
                    us.add(String.valueOf(uf));
                }
                java.util.Collections.sort(us);
                for (String u : us) {
                    System.out.println("[rtrack-dump]   USAGE " + cap(u));
                }
                System.out.println("[rtrack-dump]   strEscapes=" + a.strEscapes.get() + " wiredAnyLoad=" + a.wiredAnyLoad + " nodes=" + a.strNodes.size());
            }
            dumpLists(a.table);
        }
        List<Sink> fs = new ArrayList<>();
        for (Sink s : sinks.values()) {
            if (focused(describeRoot(s.rootKey))) {
                fs.add(s);
            }
        }
        fs.sort((x, y) -> describeRoot(x.rootKey).compareTo(describeRoot(y.rootKey)));
        for (Sink s : fs) {
            List<Object> as = s.atomsSnapshot();
            List<String> ks = new ArrayList<>();
            for (Object k : as) {
                ks.add(String.valueOf(k));
            }
            java.util.Collections.sort(ks);
            System.out.println("[rtrack-dump] sink root=" + describeRoot(s.rootKey) + " atoms=" + as.size() + " refusals=" + s.refusalsSnapshot() +
                            " keys=" + (ks.size() > 60 ? ks.subList(0, 60) + "…" : ks));
            for (RTrackRefusal r : s.refusalsSnapshot()) {
                System.out.println("[rtrack-dump]   PROV " + r + ":" + provChain(s, r));
            }
        }
        for (Map.Entry<AnalysisField, Table> e : staticTables.entrySet()) {
            if (!focused(e.getKey().format("%H.%n"))) {
                continue;
            }
            System.out.println("[rtrack-dump] static field=" + e.getKey().format("%H.%n") +
                            (e.getValue().refusalsSnapshot().isEmpty() ? "" : " refusals=" + e.getValue().refusalsSnapshot()));
            dumpLists(e.getValue());
        }
    }

    private void dumpLists(Table t) {
        for (Map.Entry<Object, EntryList<StoreEntry>> e : t.stores.entrySet()) {
            for (int i = 0; i < e.getValue().size(); i++) {
                StoreEntry s = e.getValue().get(i);
                System.out.println("[rtrack-dump]   store member=" + memberName(e.getKey()) + " frame=" + frameName(s.frame()) +
                                " node=" + describeNode(s.node()) + " value=" + valueDesc(s.value()));
            }
        }
        for (Map.Entry<Object, EntryList<LoadEntry>> e : t.loads.entrySet()) {
            for (int i = 0; i < e.getValue().size(); i++) {
                LoadEntry l = e.getValue().get(i);
                System.out.println("[rtrack-dump]   load member=" + memberName(e.getKey()) + " frame=" + frameName(l.frame()) +
                                " node=" + describeNode(l.node()) + " path=" + l.path());
            }
        }
    }

    private String describeRoot(Object root) {
        if (root instanceof SinkRoot r) {
            return frameName(r.frame()) + " " + describeNode(r.node()) + " " + r.mctx() + " " + r.path();
        }
        return String.valueOf(root);
    }

    static String memberName(Object m) {
        return m instanceof AnalysisField f ? f.format("%H.%n") : String.valueOf(m);
    }

    String frameName(LocalFlowGraph frame) {
        if (frame == null) {
            return "BUILD-TIME";
        }
        AnalysisMethod m = bridge.methodOf(frame);
        return m != null ? m.format("%H.%n(%p)") : String.valueOf(frame);
    }

    private static String valueDesc(Object v) {
        if (v instanceof DesugaredLoad dl) {
            return "DesugaredLoad(" + describeNode(dl.node()) + "," + memberName(dl.member()) + ")";
        }
        if (v instanceof ImageHeapConstant ihc) {
            return "const:" + ihc.getType().getName();
        }
        return describeNode(v);
    }

    static String describeNode(Object n) {
        if (n instanceof StoreFieldNode s) {
            return "StoreField(" + s.field().format("%H.%n") + ")";
        }
        if (n instanceof LoadFieldNode l) {
            return "LoadField(" + l.field().format("%H.%n") + ")";
        }
        if (n instanceof LoadIndexedNode) {
            return "LoadIndexed";
        }
        if (n instanceof StoreIndexedNode) {
            return "StoreIndexed";
        }
        if (n instanceof BasicArrayCopyNode) {
            return "ArrayCopy";
        }
        return String.valueOf(n);
    }
}
