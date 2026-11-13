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

import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.CURRENT_THREAD_SITE;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.STORE_FAN_CAP;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.TL_VALUE;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.argOf;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.bump;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.currentThreadIdentity;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.currentThreadIdentityLooked;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.declaredMethod;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.exactTypeOf;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.isBirthplace;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.markStored;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.top;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.extended.BoxNode;
import jdk.graal.compiler.nodes.java.DynamicNewArrayNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.NewArrayNode;
import jdk.graal.compiler.nodes.java.NewArrayWithExceptionNode;
import jdk.graal.compiler.nodes.java.NewMultiArrayNode;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

import com.oracle.graal.pointsto.heap.ImageHeapConstant;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.svm.hosted.stringanalysis.ContainerAtoms.HeapContext;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.EntryList;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.LoadEntry;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Sink;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.StoreEntry;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Table;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.CallPath;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.MethodContext;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.EscKind;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.AtomKind;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtom;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtomKey;

/**
 * The thread-local mechanism of {@link RecursiveTracking}: thread-local variables, the current thread and VM thread-locals.
 */
final class ThreadLocalModel {
    private final RecursiveTracking rt;

    ThreadLocalModel(RecursiveTracking rt) {
        this.rt = rt;
    }

    /**
     * The translated operations: the per-thread map primitives of {@code java.lang.ThreadLocal}
     * (by method identity), the current-thread accessors, and the rest of the abstract map internals.
     */
    enum TlOp {
        NONE,
        /** {@code ThreadLocal.get(Thread)}: LOAD {@code this.<tlvalue>} + the initialValue crossing. */
        READ,
        /** {@code ThreadLocalMap.set(ThreadLocal, Object)} / {@code ThreadLocalMap.<init>(ThreadLocal, Object)}: STORE {@code key.<tlvalue> := value}. */
        WRITE,
        /** {@code ThreadLocalMap.remove(ThreadLocal)}: a kill, ignored (sound: no separation). */
        KILL,
        /** {@code ThreadLocalMap.<init>(ThreadLocalMap)}: inheritance, modelled on the variable. */
        INHERIT,
        /** Any other method of the abstract map internals: a named refusal when a tracked value enters it. */
        BYPASS,
        /** {@code Thread.currentThread()}, {@code Thread.currentCarrierThread()}, {@code JavaThreads.getCurrentThreadOrNull()}. */
        CURRENT_THREAD
    }

    /**
     * The thread-local mechanism. A thread-local variable is the synthetic member {@link RecursiveTracking#TL_VALUE} of its variable
     * object's atom (threads merged, variables distinguished); the per-thread map primitives of
     * {@code java.lang.ThreadLocal} are translated into store/load events ({@link TlOp}); the current thread is one
     * singleton atom aliasing every Thread-typed atom; an SVM VM thread-local is one global table per variable.
     */
    static TlOp classifyTlOp(ResolvedJavaMethod m) {
        if (m == null) {
            return TlOp.NONE;
        }
        String cls;
        String name;
        String sig;
        try {
            cls = m.getDeclaringClass().toJavaName();
            name = m.getName();
            sig = m.getSignature().toMethodDescriptor();
        } catch (Throwable t) {
            return TlOp.NONE;
        }
        switch (cls) {
            case "java.lang.ThreadLocal":
                return name.equals("get") && sig.equals("(Ljava/lang/Thread;)Ljava/lang/Object;") ? TlOp.READ : TlOp.NONE;
            case "java.lang.ThreadLocal$ThreadLocalMap":
                if (name.equals("set") && sig.equals("(Ljava/lang/ThreadLocal;Ljava/lang/Object;)V") ||
                                name.equals("<init>") && sig.equals("(Ljava/lang/ThreadLocal;Ljava/lang/Object;)V")) {
                    return TlOp.WRITE;
                }
                if (name.equals("remove") && sig.equals("(Ljava/lang/ThreadLocal;)V")) {
                    return TlOp.KILL;
                }
                if (name.equals("<init>") && sig.equals("(Ljava/lang/ThreadLocal$ThreadLocalMap;)V")) {
                    return TlOp.INHERIT;
                }
                return TlOp.BYPASS;
            case "java.lang.ThreadLocal$ThreadLocalMap$Entry":
                return TlOp.BYPASS;
            case "java.lang.Thread":
                return (name.equals("currentThread") || name.equals("currentCarrierThread")) && sig.equals("()Ljava/lang/Thread;") ? TlOp.CURRENT_THREAD : TlOp.NONE;
            case "com.oracle.svm.core.thread.JavaThreads":
                return name.equals("getCurrentThreadOrNull") && sig.equals("()Ljava/lang/Thread;") ? TlOp.CURRENT_THREAD : TlOp.NONE;
            default:
                return TlOp.NONE;
        }
    }

    /** The translated operation of a resolved target. */
    TlOp tlOp(ResolvedJavaMethod m) {
        if (m == null) {
            return TlOp.NONE;
        }
        return rt.tlOpMemo.computeIfAbsent(m, ThreadLocalModel::classifyTlOp);
    }

    /** The variable identity of an SVM VM thread-local access node (its FastThreadLocal location identity), or null. */
    static Object vmtlIdentity(Node n) {
        if (n instanceof com.oracle.svm.core.graal.thread.LoadVMThreadLocalNode l) {
            return l.getLocationIdentity();
        }
        if (n instanceof com.oracle.svm.core.graal.thread.StoreVMThreadLocalNode s) {
            return s.getKilledLocationIdentity();
        }
        if (n instanceof com.oracle.svm.core.graal.thread.CompareAndSetVMThreadLocalNode c) {
            return c.getKilledLocationIdentity();
        }
        if (n instanceof com.oracle.svm.core.graal.thread.AddressOfVMThreadLocalNode a) {
            try {
                // no public accessor: the node's FastThreadLocal info (same builder module)
                java.lang.reflect.Field f = com.oracle.svm.core.graal.thread.AddressOfVMThreadLocalNode.class.getDeclaredField("threadLocalInfo");
                f.setAccessible(true);
                Object info = f.get(a);
                return info instanceof com.oracle.svm.core.threadlocal.VMThreadLocalInfo vi ? vi.locationIdentity : null;
            } catch (Throwable t) {
                return null;
            }
        }
        return null;
    }

    static Object currentThreadIdentity() {
        if (!currentThreadIdentityLooked) {
            Object id = null;
            try {
                Class<?> pt = Class.forName("com.oracle.svm.core.thread.PlatformThreads", false, RecursiveTracking.class.getClassLoader());
                Object ftl = com.oracle.svm.util.ReflectionUtil.readStaticField(pt, "currentThread");
                if (ftl instanceof com.oracle.svm.core.threadlocal.FastThreadLocal f) {
                    id = f.getLocationIdentity();
                }
            } catch (Throwable t) {
                id = null;
            }
            currentThreadIdentity = id;
            currentThreadIdentityLooked = true;
        }
        return currentThreadIdentity;
    }

    static boolean isCurrentThreadVmtl(Object identity) {
        return identity != null && identity == currentThreadIdentity();
    }

    /** A birthplace whose object may be a {@code java.lang.Thread} (exact type when known; else the stamp's cone). */
    static boolean mayBeThreadNode(ValueNode n, AnalysisType threadType) {
        if (threadType == null || !isBirthplace(n) || n instanceof BoxNode) {
            return false;
        }
        AnalysisType exact = exactTypeOf(n);
        if (exact != null) {
            return threadType.isAssignableFrom(exact);
        }
        if (n instanceof NewArrayNode || n instanceof NewArrayWithExceptionNode || n instanceof DynamicNewArrayNode || n instanceof NewMultiArrayNode) {
            return false;
        }
        jdk.vm.ci.meta.ResolvedJavaType t = jdk.graal.compiler.nodes.type.StampTool.typeOrNull(n.stamp(NodeView.DEFAULT));
        if (t == null) {
            return true;
        }
        if (t.isArray()) {
            return false;
        }
        return t.isAssignableFrom(threadType) || threadType.isAssignableFrom(t);
    }

    /** The image-wide index predicate (ArgStampResolution's same-pass scan): a node the thread-local model needs. */
    static boolean isThreadLocalIndexNode(Node n, AnalysisType threadType) {
        if (n instanceof com.oracle.svm.core.graal.thread.VMThreadLocalAccess) {
            return true;
        }
        if (n instanceof MethodCallTargetNode ct) {
            return classifyTlOp(ct.targetMethod()) == TlOp.CURRENT_THREAD;
        }
        return n instanceof ValueNode vn && mayBeThreadNode(vn, threadType);
    }

    /** {Thread, ThreadLocal, InheritableThreadLocal, TerminatingThreadLocal} (entries null when unavailable). */
    AnalysisType[] tlTypes() {
        AnalysisType[] t = rt.tlTypes;
        if (t == null) {
            t = new AnalysisType[]{rt.bridge.lookupJavaType(Thread.class), rt.bridge.lookupJavaType(ThreadLocal.class),
                            rt.bridge.lookupJavaType(InheritableThreadLocal.class), rt.jdkType("jdk.internal.misc.TerminatingThreadLocal")};
            rt.tlTypes = t;
        }
        return t;
    }

    /** {@code T.resolveConcreteMethod(ThreadLocal.<name><sig>)} on the variable atom's exact type (null = unknown). */
    private AnalysisMethod resolveOnVariable(RAtom atom, String name, String sig) {
        AnalysisType t = rt.atomExactType(atom);
        AnalysisType tl = tlTypes()[1];
        ResolvedJavaMethod base = declaredMethod(tl, name, sig);
        if (t == null || base == null || !tl.isAssignableFrom(t)) {
            return null;
        }
        try {
            ResolvedJavaMethod r = t.resolveConcreteMethod(base, t);
            return r != null ? rt.bridge.resolveMethod(r) : null;
        } catch (Throwable e) {
            return null;
        }
    }

    void tlUnmodelled(ContainerTables.Refusable target, String why) {
        bump(rt.tlUnmodelledBy, why);
        rt.refuseAny(target, RTrackRefusal.THREAD_LOCAL_UNMODELLED);
    }

    /** The initial-store value: the returns of {@code method} (the variable's exact initialValue) invoked on {@code owner}. */
    record InitialValue(RAtomKey owner, AnalysisMethod method, LocalFlowGraph frame) {
    }

    /** The store node of the initial store (dedup per (variable, method)). */
    record InitialValueStore(AnalysisMethod method) {
    }

    /** The number of {@code ThreadLocal$ThreadLocalMap} objects in the image heap (-1 = the heap is unreadable). */
    private int heapThreadLocalMaps() {
        int n = rt.heapThreadLocalMaps;
        if (n != -2) {
            return n;
        }
        Map<AnalysisType, Set<ImageHeapConstant>> heap = rt.bridge.heapObjects();
        if (heap == null) {
            n = -1;
        } else {
            n = 0;
            for (Map.Entry<AnalysisType, Set<ImageHeapConstant>> e : heap.entrySet()) {
                if ("java.lang.ThreadLocal$ThreadLocalMap".equals(e.getKey().toJavaName())) {
                    n += e.getValue().size();
                }
            }
        }
        rt.heapThreadLocalMaps = n;
        return n;
    }

    /** Is any field of the abstract per-thread map structure reflectively/Unsafe-written (the bypass list)? */
    private boolean tlInternalsReflective() {
        Boolean b = rt.tlInternalsReflective;
        if (b != null) {
            return b;
        }
        boolean flagged = false;
        // Only the map's content fields: an Unsafe/reflective write of Thread.threadLocals / inheritableThreadLocals /
        // terminatingThreadLocals can only install an existing ThreadLocalMap object (maps are allocated only by the
        // translated constructors, their contents written only by translated primitives or through these two fields) or
        // null; moving a map between threads is a no-op with all threads merged (the JDK's own such writes store null).
        // Entry keys (Reference.referent) are only cleared.
        String[][] fields = {{"java.lang.ThreadLocal$ThreadLocalMap", "table"}, {"java.lang.ThreadLocal$ThreadLocalMap$Entry", "value"}};
        for (String[] cf : fields) {
            AnalysisType t = null;
            try {
                t = rt.bridge.lookupJavaType(Class.forName(cf[0], false, Object.class.getClassLoader()));
            } catch (Throwable ignore) {
                // unavailable
            }
            if (t == null) {
                continue;
            }
            for (ResolvedJavaField f : t.getInstanceFields(false)) {
                if (f.getName().equals(cf[1])) {
                    AnalysisField af = rt.bridge.resolveField(f);
                    boolean fl;
                    try {
                        fl = af != null && af.isUnsafeAccessed();
                    } catch (Throwable ignore) {
                        fl = true;
                    }
                    if (fl) {
                        bump(rt.tlUnmodelledBy, "reflective-field:" + cf[0] + "." + cf[1]);
                    }
                    flagged |= fl;
                }
            }
        }
        rt.tlInternalsReflective = flagged;
        return flagged;
    }

    /**
     * The first thread-local event on a variable atom: the initial store of its exact-type
     * {@code initialValue()} into {@code T(A).stores[<tlvalue>]}; inheritance (identity {@code childValue}:
     * nothing; overridden: {@code THREAD_LOCAL_UNMODELLED}); an unknown exact type refuses by name.
     */
    private void ensureTlVariable(RAtom atom) {
        if (!rt.tlVariables.add(atom.key)) {
            return;
        }
        if (tlInternalsReflective()) {
            rt.refuse(atom.table, RTrackRefusal.REFLECTIVE_FIELD);
        }
        if (heapThreadLocalMaps() != 0) {
            // a per-thread map built at image-build time (e.g. an inherited map of the build-time main thread) holds
            // slot values the model does not read: never silent
            tlUnmodelled(atom.table, "heap-map");
        }
        AnalysisMethod iv = resolveOnVariable(atom, "initialValue", "()Ljava/lang/Object;");
        if (iv == null) {
            tlUnmodelled(atom.table, "variable-type");
            return;
        }
        LocalFlowGraph f = rt.bridge.frameOf(iv);
        if (f == null || rt.graphOf(f) == null) {
            if (!(f == null && rt.dropDeadTarget(iv, "tl-initialValue"))) {
                rt.missingIr("tl-initialValue", iv);
                rt.refuse(atom.table, RTrackRefusal.MISSING_IR);
            }
        } else {
            StoreEntry e = new StoreEntry(f, new InitialValueStore(iv), new InitialValue(atom.key, iv, f), null,
                            MethodContext.owner(atom.key.site, atom.key.context));
            EntryList<StoreEntry> list = atom.table.stores(TL_VALUE);
            if (list.append(e, e.dedupKey(), e.nodeKey()) >= 0) {
                rt.tlInitial.incrementAndGet();
                rt.censusStoreEntries.incrementAndGet();
                if (list.distinctNodeCount() > STORE_FAN_CAP) {
                    rt.refuse(atom.table, RTrackRefusal.STORE_FAN_CAP);
                }
            }
        }
        AnalysisType itl = tlTypes()[2];
        AnalysisType t = rt.atomExactType(atom);
        AnalysisType ttl = tlTypes()[3];
        if (t != null && (ttl == null || ttl.isAssignableFrom(t))) {
            // The never-entered get(Thread) loses setInitialValue's
            // TerminatingThreadLocal.register(this) (the variable's escape into REGISTRY, read back at thread exit):
            // a TerminatingThreadLocal variable is refused by name (TTL unavailable: every variable, sound).
            tlUnmodelled(atom.table, "terminating");
        }
        if (itl != null && t != null && itl.isAssignableFrom(t)) {
            AnalysisMethod cv = resolveOnVariable(atom, "childValue", "(Ljava/lang/Object;)Ljava/lang/Object;");
            if (cv == null || !"java.lang.InheritableThreadLocal".equals(cv.getDeclaringClass().toJavaName())) {
                tlUnmodelled(atom.table, "childValue-override");
            }
        }
    }

    /**
     * The forward translation at an invoke whose resolved target is a translated operation: the
     * callee body is never entered.
     */
    void tlInvokeUsage(RAtom atom, LocalFlowGraph frame, ValueNode n, MethodCallTargetNode ct, Invoke inv,
                    LocalFlowGraph.LocalVertex callVertex, TlOp op, CallPath path, MethodContext mctx, CallPath pushed) {
        var args = ct.arguments();
        ValueNode invNode = (ValueNode) inv.asNode();
        switch (op) {
            case READ -> {
                // slot 1 (the Thread) only selects the per-thread map, which is abstract: nothing to record
                if (!args.isEmpty() && args.get(0) == n) {
                    ensureTlVariable(atom);
                    rt.tlLoads.incrementAndGet();
                    rt.recordLoad(atom, frame, invNode, TL_VALUE, path, mctx);
                    tlInitialCrossing(atom, pushed);
                }
            }
            case WRITE -> {
                // slot 0 is the (abstract) map; slot 1 the variable (key); slot 2 the stored value
                if (args.size() >= 3) {
                    if (args.get(1) == n) {
                        ensureTlVariable(atom);
                        rt.tlStores.incrementAndGet();
                        rt.recordStore(atom, frame, invNode, args.get(2), TL_VALUE, path, mctx);
                    }
                    if (args.get(2) == n) {
                        rt.tlEscapes.incrementAndGet();
                        rt.escapeInto(atom, frame, invNode, args.get(1), TL_VALUE, path, mctx);
                    }
                } else {
                    tlUnmodelled(atom.table, "write-shape");
                }
            }
            case KILL, INHERIT, CURRENT_THREAD -> {
                // a kill (ignored: no separation), the inheritance copy (modelled on the variable), an accessor
            }
            case BYPASS -> tlUnmodelled(atom.table, "fwd/" + ct.targetMethod().format("%H.%n(%p)") + "<-" + rt.frameName(frame) + "/" + atom.key);
            default -> {
            }
        }
    }

    /** The variable atom enters its exact-type {@code initialValue()} as the receiver at a translated READ. */
    private void tlInitialCrossing(RAtom atom, CallPath pushed) {
        AnalysisMethod iv = resolveOnVariable(atom, "initialValue", "()Ljava/lang/Object;");
        if (iv == null) {
            return; // refused by ensureTlVariable
        }
        LocalFlowGraph f = rt.bridge.frameOf(iv);
        StructuredGraph g = f != null ? rt.graphOf(f) : null;
        if (g == null) {
            return; // dead or refused by ensureTlVariable
        }
        if (rt.enterReceiver(atom, f, g, pushed, MethodContext.owner(atom.key.site, atom.key.context))) {
            rt.tlCrossings.incrementAndGet(); // (counted only where the body reads `this`)
        }
    }

    /** The backward translation at an invoke result: a READ is the ordinary load case. */
    void tlInvokeResult(LocalFlowGraph frame, Invoke inv, TlOp op, MethodContext mctx, CallPath path, Sink sink) {
        switch (op) {
            case READ -> {
                rt.tlBackwardLoads.incrementAndGet();
                rt.loadCase(frame, (ValueNode) inv.asNode(), argOf((ValueNode) inv.asNode(), 0), TL_VALUE, sink, mctx, path);
            }
            case CURRENT_THREAD -> currentThreadCase(sink);
            default -> tlUnmodelled(sink, "bwd/" + (inv.callTarget() != null ? inv.callTarget().targetMethod().format("%H.%n(%p)") : "?"));
        }
    }

    List<AnalysisMethod> tlIndexedMethods() {
        List<AnalysisMethod> ms = new ArrayList<>(rt.argStampIndex != null ? rt.argStampIndex.rtrackThreadLocalMethods() : List.of());
        ms.sort((a, b) -> {
            int c = TransferFacts.methodFlowKey(a).compareTo(TransferFacts.methodFlowKey(b));
            return c != 0 ? c : TransferFacts.methodDescriptorKey(a).compareTo(TransferFacts.methodDescriptorKey(b));
        });
        return ms;
    }

    private RAtom currentThreadAtom() {
        RAtomKey key = rt.internKey(CURRENT_THREAD_SITE, HeapContext.EMPTY);
        RAtom atom = rt.atoms.computeIfAbsent(key, k -> rt.new RAtom(k, AtomKind.CURRENT_THREAD, null, null, MethodContext.UNKNOWN, null, null, false));
        rt.schedule(atom);
        return atom;
    }

    /**
     * A current-thread read resolves to the singleton plus every Thread-typed atom that can exist (the aliasing):
     * the MERGED atom of every Thread-typed allocation site (a superset of its context-specific atoms)
     * and every Thread-typed image-heap constant (the build-time main thread).
     */
    private void currentThreadCase(Sink sink) {
        rt.tlCurrentThreadResolutions.incrementAndGet();
        if (tlTypes()[0] == null || rt.argStampIndex == null) {
            tlUnmodelled(sink, "currentThread-types");
            return;
        }
        rt.addAtomTo(sink, currentThreadAtom().key);
        for (Object[] site : rt.threadSites()) {
            rt.mintInto(sink, (ValueNode) site[1], (LocalFlowGraph) site[0], HeapContext.MERGED, MethodContext.UNKNOWN, null);
        }
        Map<AnalysisType, Set<ImageHeapConstant>> heap = rt.bridge.heapObjects();
        if (heap == null) {
            tlUnmodelled(sink, "currentThread-heap");
            return;
        }
        AnalysisType threadType = tlTypes()[0];
        List<AnalysisType> types = new ArrayList<>();
        for (AnalysisType t : heap.keySet()) {
            if (threadType.isAssignableFrom(t)) {
                types.add(t);
            }
        }
        types.sort((a, b) -> a.toJavaName().compareTo(b.toJavaName()));
        for (AnalysisType t : types) {
            for (ImageHeapConstant c : heap.get(t)) {
                rt.addAtomTo(sink, rt.constantAtom(c).key);
            }
        }
    }

    /** Is the atom's object possibly a Thread (the forward half of the current-thread aliasing)? */
    boolean atomMayBeThread(RAtom a) {
        AnalysisType threadType = tlTypes()[0];
        if (threadType == null) {
            return false;
        }
        return switch (a.kind) {
            case CURRENT_THREAD -> true;
            case CONSTANT -> a.constant != null && threadType.isAssignableFrom(a.constant.getType());
            case ALLOCATION -> a.birthNode != null && mayBeThreadNode(a.birthNode, threadType);
            case STRING -> false; // a String is never a Thread
        };
    }

    /** The forward half of the aliasing: a Thread-typed atom's value also appears at every current-thread read site. */
    void walkFromCurrentThreadReads(RAtom atom) {
        if (rt.argStampIndex == null) {
            tlUnmodelled(atom.table, "currentThread-index");
            return;
        }
        for (Object[] site : rt.currentThreadReads()) {
            rt.enqueueWalk(atom, (LocalFlowGraph) site[0], (ValueNode) site[1], null, MethodContext.UNKNOWN);
        }
    }

    Table vmtlTable(Object identity) {
        Table existing = rt.vmtlTables.get(identity);
        if (existing != null) {
            return existing;
        }
        Table t = new Table(identity, false);
        Table winner = rt.vmtlTables.putIfAbsent(identity, t);
        if (winner != null) {
            return winner;
        }
        if (rt.argStampIndex == null) {
            rt.refuse(t, RTrackRefusal.MISSING_IR);
            return t;
        }
        for (AnalysisMethod m : tlIndexedMethods()) {
            LocalFlowGraph frame = rt.bridge.frameOf(m);
            StructuredGraph g = frame != null ? rt.graphOf(frame) : null;
            if (g == null) {
                continue;
            }
            for (Node node : g.getNodes()) {
                if (!(node instanceof com.oracle.svm.core.graal.thread.VMThreadLocalAccess)) {
                    continue;
                }
                Object id = vmtlIdentity(node);
                if (id == null) {
                    tlUnmodelled(t, "vmtl-identity"); // an access whose variable cannot be told apart: never silent
                    continue;
                }
                if (id != identity) {
                    continue;
                }
                ValueNode value = node instanceof com.oracle.svm.core.graal.thread.StoreVMThreadLocalNode s ? s.getValue()
                                : node instanceof com.oracle.svm.core.graal.thread.CompareAndSetVMThreadLocalNode c ? c.getUpdate() : null;
                if (value != null) {
                    if (value.getStackKind() == JavaKind.Object) {
                        StoreEntry e = new StoreEntry(frame, node, value, null, MethodContext.UNKNOWN);
                        if (t.stores(TL_VALUE).append(e, e.dedupKey(), e.nodeKey()) >= 0) {
                            rt.censusStoreEntries.incrementAndGet();
                            if (t.stores(TL_VALUE).distinctNodeCount() > STORE_FAN_CAP) {
                                rt.refuse(t, RTrackRefusal.STORE_FAN_CAP);
                            }
                        }
                    }
                } else if (node instanceof com.oracle.svm.core.graal.thread.LoadVMThreadLocalNode l) {
                    if (l.getStackKind() == JavaKind.Object) {
                        LoadEntry e = new LoadEntry(frame, l, null, MethodContext.UNKNOWN);
                        if (t.loads(TL_VALUE).append(e, e.dedupKey()) >= 0) {
                            rt.censusLoadEntries.incrementAndGet();
                        }
                    }
                } else if (node instanceof com.oracle.svm.core.graal.thread.AddressOfVMThreadLocalNode) {
                    rt.refuse(t, RTrackRefusal.UNSAFE_ACCESS); // raw accesses through the address are not in the table
                }
            }
        }
        return t;
    }

    /** Forward: the atom's value stored into a VM thread-local (a StoreVMThreadLocal value / a CAS update). */
    void vmtlEscape(RAtom atom, Object identity) {
        markStored(atom); // before the identity / current-thread early returns
        if (identity == null) {
            tlUnmodelled(atom.table, "vmtl-identity");
            return;
        }
        if (isCurrentThreadVmtl(identity)) {
            // installing the current thread: covered by the aliasing iff the value is Thread-typed
            if (!atomMayBeThread(atom)) {
                tlUnmodelled(atom.table, "currentThread-store");
            }
            return;
        }
        rt.tlVmtlEscapes.incrementAndGet();
        rt.holderEnd.escRec(atom, List.of("vmtl", identity), EscKind.VMTL, String.valueOf(identity), 0); // holder-end rule: holder-free (the global table)
        Table t = vmtlTable(identity);
        EntryList<LoadEntry> list = t.loads(TL_VALUE);
        rt.register(list, List.of("esc-vmtl", atom.key), idx -> rt.continueAt(atom, list.get(idx), TL_VALUE), null, atom.table);
    }

    /** Backward: a VM thread-local load waits on the variable's stores (the current thread: the singleton + aliases). */
    void vmtlLoadCase(Node load, Sink sink) {
        Object identity = vmtlIdentity(load);
        if (identity == null) {
            tlUnmodelled(sink, "vmtl-identity");
            return;
        }
        if (isCurrentThreadVmtl(identity)) {
            currentThreadCase(sink);
            return;
        }
        rt.tlVmtlLoads.incrementAndGet();
        Table t = vmtlTable(identity);
        EntryList<StoreEntry> list = t.stores(TL_VALUE);
        rt.register(list, List.of("lvmtl", sink, load), idx -> rt.resumeValue(list.get(idx), sink), null, sink);
    }

    /** The translated operations met (sorted; census only). */
    private String tlOpCensus() {
        List<String> out = new ArrayList<>();
        for (Map.Entry<ResolvedJavaMethod, TlOp> e : rt.tlOpMemo.entrySet()) {
            if (e.getValue() != TlOp.NONE) {
                out.add(e.getValue() + ":" + e.getKey().format("%H.%n(%p)"));
            }
        }
        java.util.Collections.sort(out);
        return out.toString();
    }

    String tlCensus() {
        return " threadLocal{loads=" + rt.tlLoads.get() + " stores=" + rt.tlStores.get() + " escapes=" + rt.tlEscapes.get() + " initial=" + rt.tlInitial.get() +
                        " crossings=" + rt.tlCrossings.get() + " bwdLoads=" + rt.tlBackwardLoads.get() + " variables=" + rt.tlVariables.size() +
                        " curThreadResolutions=" + rt.tlCurrentThreadResolutions.get() + " curThreadReads=" + (rt.currentThreadReads != null ? rt.currentThreadReads.size() : -1) +
                        " threadSites=" + (rt.threadSites != null ? rt.threadSites.size() : -1) + " vmtlTables=" + rt.vmtlTables.size() + " vmtlLoads=" + rt.tlVmtlLoads.get() +
                        " vmtlEscapes=" + rt.tlVmtlEscapes.get() + " heapMaps=" + rt.heapThreadLocalMaps + " curThreadIdentity=" + (currentThreadIdentity() != null ? "ok" : "MISSING") +
                        " unmodelled=" +
                        top(rt.tlUnmodelledBy) + " ops=" + tlOpCensus() + "}";
    }
}
