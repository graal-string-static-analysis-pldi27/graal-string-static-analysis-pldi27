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

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import com.oracle.graal.pointsto.heap.ImageHeapConstant;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.util.GraalAccess;
import com.oracle.svm.core.meta.MethodPointer;
import com.oracle.svm.core.reflect.SubstrateAccessor;
import com.oracle.svm.core.reflect.SubstrateConstructorAccessor;
import com.oracle.svm.core.reflect.SubstrateMethodAccessor;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.FrameState;
import jdk.graal.compiler.nodes.IndirectCallTargetNode;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PhiNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.VirtualState;
import jdk.graal.compiler.nodes.calc.ConditionalNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.spi.LimitedValueProxy;
import jdk.graal.compiler.nodes.util.GraphUtil;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * The reflection bridge, a computational shortcut for the two SVM function-pointer calls behind {@code Method.invoke}.
 * <ul>
 * <li><b>The table.</b> Built once after the fixpoint from the reflection accessors in the image heap, in sorted order
 * (target key, kind, stub key), from the hosted objects: the stub from {@code expandSignature}'s {@code MethodPointer},
 * the direct target from {@code directTarget}, a constructor's factory from {@code factoryMethodTarget}; static-bound vs
 * virtual by {@code targetMethod.canBeStaticallyBound()} ({@code vtableIndex} is not yet computed). A virtual target's
 * CHA is the points-to analysis's own dispatch over the accessor's {@code receiverType}: the callees linked on the
 * target's context-insensitive virtual invoke, which {@code onAccessorReachable} registers -- nothing is minted.</li>
 * <li><b>The edges, by IR structure.</b> OUTER: an indirect call whose address unproxifies to
 * {@code LoadField SubstrateAccessor.expandSignature}; targets = every stub of the table. INNER: an indirect call in a
 * stub frame whose address unproxifies to the stub's parameter 2 (the target pointer); targets = the stub's table
 * targets. Bridged caller sites are keyed by the IR node.</li>
 * <li><b>The coverage proof</b> (gates the narrowed outside-caller predicate): every load of an accessor
 * function-pointer field in analysed code flows only into an OUTER call (address or argument), a return whose every IR
 * caller's result does the same, or an observation; every stub's parameter 2 is used only as its INNER call's address.
 * Then the accessors' pointers are invoked only through the bridged edges (invoke, invokeSpecial, the caller-sensitive
 * invoke, newInstance; method handles reuse these accessors). Any failure (an unreadable accessor, an unmatched use, a
 * stub or OUTER frame without IR) keeps the base (un-narrowed) predicate.</li>
 * <li><b>The registries</b>: the JNI registry
 * ({@code JNIAccessFeature.calledJavaMethods}) and the C-entry-point stub registry ({@code CEntryPointCallStubSupport})
 * as a second source: JNI-callable methods are outside by name; the base predicate's pending-slot allowlist is confirmed
 * per holder object (a pending slot whose holder the registries do not list fails). A registry read failure keeps the
 * allowlist alone and disables the narrowing.</li>
 * </ul>
 */
final class ReflectionBridge {

    static final String ACCESSOR = "com.oracle.svm.core.reflect.SubstrateAccessor";
    static final String CTOR_ACCESSOR = "com.oracle.svm.core.reflect.SubstrateConstructorAccessor";

    /** An accessor's function-pointer field (by exact declaring class and name): the pointers only the bridge's edges call. */
    static boolean isAccessorPointerField(String declaringClass, String name) {
        return ACCESSOR.equals(declaringClass) && ("expandSignature".equals(name) || "directTarget".equals(name)) ||
                        CTOR_ACCESSOR.equals(declaringClass) && "factoryMethodTarget".equals(name);
    }

    /**
     * The narrowed world-top predicate (pure; pinned by {@code ReflectionBridgeTest}): an outside caller is unmodelled for a
     * native entry, a JNI-registered method (registry), a direct or virtual root that is not reflective-only, an
     * implementation reached through a virtual root that is not reflective-only, or a method whose address is taken
     * outside the accessors' pointer fields.
     */
    static boolean narrowedOutside(boolean nativeEntry, boolean jniRegistered, boolean directRoot, boolean directReflectiveOnly, boolean virtualRoot,
                    boolean virtualReflectiveOnly, boolean reachedThroughNonReflectiveVirtualRoot, boolean addressTakenUnmodelled) {
        return nativeEntry || jniRegistered || directRoot && !directReflectiveOnly || virtualRoot && !virtualReflectiveOnly ||
                        reachedThroughNonReflectiveVirtualRoot || addressTakenUnmodelled;
    }

    /**
     * A root registration is reflective-only (pure; pinned) when the method is in the bridge's table for that kind, its
     * first registration reason is an image-heap scan reason (ReflectionFeature.onAccessorReachable's), and it is neither
     * JNI-registered nor a native entry. A non-scan first reason is another source: outside.
     */
    static boolean reflectiveOnly(boolean inBridgeTable, boolean firstReasonIsScan, boolean jniRegistered, boolean nativeEntry) {
        return inBridgeTable && firstReasonIsScan && !jniRegistered && !nativeEntry;
    }

    /**
     * In the analysis child, {@code ExtraRootsDiscovery} also registers every member of the reflection configuration as a direct root
     * with the reason {@code "string-analysis extra root (reflection)"} (constructors: {@code "string-analysis extra root
     * constructor (reflection)"}); the parent never does. A method keeps only its first root reason, so whether it is the
     * accessor scan ({@code ReflectionFeature.onAccessorReachable}) or the extra-root string is a race between the two
     * registrations (seen on JMH's generated {@code *_jmhTest} targets). Both mean "reachable through the reflection
     * metadata only", so both count as the reflective first reason; the rule's other inputs are unchanged.
     * <p>
     * The child's extra-root reason for a reflection-configuration member (pure; pinned by JUnit). The strings are
     * {@link ExtraRootsDiscovery}'s shared constants, so a wording change cannot silently break the match.
     */
    static boolean childReflectionExtraRoot(Object reason) {
        return reason instanceof String s && s.startsWith(ExtraRootsDiscovery.REFLECTION_REASON_PREFIX) && s.endsWith(ExtraRootsDiscovery.REFLECTION_REASON_SUFFIX);
    }

    /**
     * Whether a root registration reason is the reflective first reason of {@link #reflectiveOnly}: an image-heap scan
     * reason, or the child's reflection extra root.
     */
    static boolean reflectiveFirstReason(Object reason) {
        return reason instanceof com.oracle.graal.pointsto.ObjectScanner.ScanReason || childReflectionExtraRoot(reason);
    }

    private final RecursiveTracking rt;

    /** The OUTER edge's targets: every distinct expand-signature method (stub or error stub), sorted. */
    final List<AnalysisMethod> stubs = new ArrayList<>();
    /** The INNER edge's targets per stub (sorted, distinct). */
    final Map<AnalysisMethod, List<AnalysisMethod>> innerTargets = new IdentityHashMap<>();
    /** Reflective direct-root sources (stubs, non-abstract targets, factories) and virtual-root sources (virtual targets). */
    final Set<AnalysisMethod> reflDirect = Collections.newSetFromMap(new IdentityHashMap<>());
    final Set<AnalysisMethod> reflVirtual = Collections.newSetFromMap(new IdentityHashMap<>());
    /** The accessor image-heap objects of the table (their pointer fields are the bridge's; the address scan skips them). */
    final Set<ImageHeapConstant> accessorConstants = Collections.newSetFromMap(new IdentityHashMap<>());
    /** Bridged caller sites per callee frame (OUTER sites for stubs, INNER sites for targets). */
    private final Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> callers = new IdentityHashMap<>();
    /** Callee frames some of whose bridged callers could not be placed (no frame / no IR): MISSING_IR. */
    private final Set<LocalFlowGraph> incomplete = Collections.newSetFromMap(new IdentityHashMap<>());
    /** Matched edges by IR node (Invoke node identity): OUTER, INNER. */
    private final Set<Node> outerNodes = Collections.newSetFromMap(new IdentityHashMap<>());
    private final Map<Node, AnalysisMethod> innerNodes = new IdentityHashMap<>();

    int accessors;
    int methodAccessors;
    int ctorAccessors;
    int readFailures;
    int virtualTargets;
    int chaReadFailures;
    int maxInnerFan;
    int keyCollisions;
    /** A build mode whose late root registrations the first-reason belt does not see (null = none). */
    String guardReason;
    /** Every registered foreign-call target (outside: compiled-code callers no index lists). */
    final Set<AnalysisMethod> foreignCallTargets = Collections.newSetFromMap(new IdentityHashMap<>());
    int innerTargetEdges;
    int pointerReaderMethods;
    int pointerLoads;
    int outerFramesMissing;
    int innerMissing;
    final TreeSet<String> coverageProblems = new TreeSet<>();
    /** Option D. */
    final Set<AnalysisMethod> jniMethods = Collections.newSetFromMap(new IdentityHashMap<>());
    final Set<Object> jniMethodObjects = Collections.newSetFromMap(new IdentityHashMap<>());
    final Set<Object> boxedPointerObjects = Collections.newSetFromMap(new IdentityHashMap<>());
    int jniEntries;
    int jniUnresolved;
    int cEntryBoxed;
    int cEntryBoxedNonNative;
    int boxedDataPointers;
    String registryFailure;
    long buildMs;

    private ReflectionBridge(RecursiveTracking rt) {
        this.rt = rt;
    }

    /** True when the table was read completely and the coverage proof holds (the narrowing may apply). */
    boolean complete() {
        return readFailures == 0 && chaReadFailures == 0 && coverageProblems.isEmpty() && registryFailure == null && outerFramesMissing == 0 && innerMissing == 0 && !outerNodes.isEmpty() &&
                        guardReason == null;
    }

    /** The bridged targets of the invoke {@code inv} in {@code frame}, or null when it is not a bridged edge. */
    List<AnalysisMethod> targetsOf(LocalFlowGraph frame, Invoke inv) {
        Node n = inv.asNode();
        if (outerNodes.contains(n)) {
            return stubs;
        }
        AnalysisMethod stub = innerNodes.get(n);
        if (stub != null) {
            return innerTargets.getOrDefault(stub, List.of());
        }
        if (isOuterShape(inv)) {
            // An OUTER-shaped call the build did not place: the stubs' caller lists lack it, so the crossing
            // (and the result case) refuses MISSING_IR
            unplacedOuter++;
            return UNPLACED;
        }
        return null;
    }

    /** The identity sentinel of an unplaced OUTER-shaped call ({@link #targetsOf}); the engine refuses MISSING_IR. */
    static final List<AnalysisMethod> UNPLACED = java.util.Collections.unmodifiableList(new ArrayList<>());
    volatile int unplacedOuter;

    boolean isOuterNode(Node n) {
        return outerNodes.contains(n);
    }

    List<ForwardFixpoint.CallerSite> callersOf(LocalFlowGraph frame) {
        List<ForwardFixpoint.CallerSite> l = callers.get(frame);
        return l != null ? l : List.of();
    }

    boolean incomplete(LocalFlowGraph frame) {
        return incomplete.contains(frame);
    }

    /** The OUTER edge by IR structure: an indirect call whose address unproxifies to LoadField SubstrateAccessor.expandSignature. */
    static boolean isOuterShape(Invoke inv) {
        if (!(inv.callTarget() instanceof IndirectCallTargetNode ict)) {
            return false;
        }
        ValueNode addr = GraphUtil.unproxify(ict.computedAddress());
        return addr instanceof LoadFieldNode lf && "expandSignature".equals(lf.field().getName()) &&
                        ACCESSOR.equals(lf.field().getDeclaringClass().toJavaName(true));
    }

    private static String key(ResolvedJavaMethod m) {
        return m == null ? "null" : m.getDeclaringClass().toJavaName(true) + "#" + m.getName() + m.getSignature().toMethodDescriptor();
    }

    private static Object hostedField(Object o, Class<?> c, String name) throws ReflectiveOperationException {
        Field f = c.getDeclaredField(name);
        f.setAccessible(true);
        return f.get(o);
    }

    private AnalysisMethod pointerMethod(Object p) {
        if (p instanceof MethodPointer mp && mp.getMethod() != null) {
            AnalysisMethod am = rt.bridge.resolveMethod(mp.getMethod());
            if (am == null) {
                readFailures++;
            }
            return am;
        }
        if (p != null) {
            readFailures++; // a non-MethodPointer function pointer: unknown target
        }
        return null;
    }

    private record Row(String sortKey, AnalysisMethod stub, List<AnalysisMethod> targets) {
    }

    static ReflectionBridge build(RecursiveTracking rt) {
        ReflectionBridge b = new ReflectionBridge(rt);
        long t0 = System.nanoTime();
        try {
            b.buildTable();
            b.buildEdges();
            b.readRegistries();
            b.guardReason = buildModeGuard();
            List<AnalysisMethod> fc = rt.bridge.foreignCallTargets();
            if (fc == null) {
                b.guardReason = (b.guardReason == null ? "" : b.guardReason + ";") + "foreign-calls-unreadable";
            } else {
                b.foreignCallTargets.addAll(fc);
            }
        } catch (Throwable t) {
            b.readFailures++;
            b.coverageProblems.add("build-failed:" + t);
        }
        b.buildMs = (System.nanoTime() - t0) / 1_000_000;
        return b;
    }

    /**
     * The build modes that register roots after the reflective registrations without a registry this check reads: a
     * layered build ({@code ClassInclusionPolicy} / {@code LayeredDispatchTableFeature}), {@code -H:Preserve} or the
     * base-layer inclusion policy. Any of them (or an unreadable check) disables the narrowing.
     */
    static String buildModeGuard() { // also the closed-field rule's build-mode guard
        try {
            StringBuilder why = new StringBuilder();
            if (com.oracle.svm.core.imagelayer.ImageLayerBuildingSupport.buildingImageLayer()) {
                why.append("layered-build;");
            }
            if (!com.oracle.svm.core.SubstrateOptions.Preserve.getValue().values().isEmpty()) {
                why.append("preserve;");
            }
            if (com.oracle.svm.core.SubstrateOptions.UseBaseLayerInclusionPolicy.getValue()) {
                why.append("base-layer-inclusion-policy;");
            }
            return why.length() == 0 ? null : why.toString();
        } catch (Throwable t) {
            return "guard-unreadable:" + t.getClass().getSimpleName();
        }
    }

    /** The methods outside by a registry: JNI-callable or a registered foreign-call target. */
    boolean registeredOutside(AnalysisMethod m) {
        return jniMethods.contains(m) || foreignCallTargets.contains(m);
    }

    private void buildTable() throws ReflectiveOperationException {
        Map<AnalysisType, Set<ImageHeapConstant>> heap = rt.bridge.heapObjects();
        if (heap == null) {
            readFailures++;
            return;
        }
        List<Row> rows = new ArrayList<>();
        for (Map.Entry<AnalysisType, Set<ImageHeapConstant>> e : heap.entrySet()) {
            Class<?> jc = e.getKey().getJavaClass();
            if (jc == null || !SubstrateAccessor.class.isAssignableFrom(jc)) {
                continue;
            }
            for (ImageHeapConstant c : e.getValue()) {
                accessorConstants.add(c);
                accessors++;
                JavaConstant hc = c.getHostedObject();
                Object o = hc != null ? GraalAccess.getOriginalSnippetReflection().asObject(Object.class, hc) : null;
                if (!(o instanceof SubstrateAccessor acc)) {
                    readFailures++;
                    continue;
                }
                AnalysisMethod stub = pointerMethod(acc.getExpandSignature());
                if (stub == null) {
                    readFailures++;
                    continue;
                }
                List<AnalysisMethod> targets = new ArrayList<>();
                AnalysisMethod direct = pointerMethod(hostedField(acc, SubstrateAccessor.class, "directTarget"));
                if (direct != null) {
                    targets.add(direct);
                    reflDirect.add(direct);
                }
                ResolvedJavaMethod target = acc.getTargetMethod();
                String kind;
                if (acc instanceof SubstrateMethodAccessor) {
                    methodAccessors++;
                    kind = "method";
                    if (target != null && !target.canBeStaticallyBound()) {
                        AnalysisMethod vt = rt.bridge.resolveMethod(target);
                        virtualTargets++;
                        if (vt instanceof com.oracle.graal.pointsto.meta.PointsToAnalysisMethod pm && vt.isVirtualRootMethod()) {
                            reflVirtual.add(vt);
                            try {
                                // the CHA over receiverType (= the target's declaring class): points-to's own dispatch
                                targets.addAll(pm.getContextInsensitiveVirtualInvoke(com.oracle.svm.common.meta.MultiMethod.ORIGINAL_METHOD).getAllCallees());
                            } catch (Throwable t) {
                                chaReadFailures++;
                            }
                        } else {
                            chaReadFailures++;
                        }
                    }
                } else if (acc instanceof SubstrateConstructorAccessor) {
                    ctorAccessors++;
                    kind = "ctor";
                    AnalysisMethod factory = pointerMethod(hostedField(acc, SubstrateConstructorAccessor.class, "factoryMethodTarget"));
                    if (factory != null) {
                        targets.add(factory);
                        reflDirect.add(factory);
                    }
                } else {
                    kind = "other";
                    readFailures++;
                }
                reflDirect.add(stub);
                rows.add(new Row(key(target) + "|" + kind + "|" + key(stub), stub, targets));
            }
        }
        rows.sort((x, y) -> x.sortKey().compareTo(y.sortKey()));
        // Distinct methods are kept by identity; two distinct methods with one key (e.g. same-named classes
        // of two loaders) cannot be ordered canonically, and count as a read failure (the base predicate)
        TreeMap<String, AnalysisMethod> stubByKey = new TreeMap<>();
        Map<AnalysisMethod, TreeMap<String, AnalysisMethod>> tgt = new IdentityHashMap<>();
        for (Row r : rows) {
            AnalysisMethod prevStub = stubByKey.putIfAbsent(key(r.stub()), r.stub());
            if (prevStub != null && prevStub != r.stub()) {
                keyCollisions++;
                readFailures++;
            }
            TreeMap<String, AnalysisMethod> m = tgt.computeIfAbsent(r.stub(), k -> new TreeMap<>());
            for (AnalysisMethod t : r.targets()) {
                AnalysisMethod prev = m.putIfAbsent(key(t), t);
                if (prev != null && prev != t) {
                    keyCollisions++;
                    readFailures++;
                }
            }
        }
        stubs.addAll(stubByKey.values());
        for (Map.Entry<AnalysisMethod, TreeMap<String, AnalysisMethod>> e : tgt.entrySet()) {
            List<AnalysisMethod> l = new ArrayList<>(e.getValue().values());
            innerTargets.put(e.getKey(), l);
            maxInnerFan = Math.max(maxInnerFan, l.size());
            innerTargetEdges += l.size();
        }
    }

    private void addCaller(LocalFlowGraph callee, AnalysisMethod callerMethod, LocalFlowGraph callerFrame, Invoke inv) {
        List<ForwardFixpoint.CallerSite> l = callers.computeIfAbsent(callee, k -> new ArrayList<>(2));
        LocalFlowGraph.LocalVertex cv = rt.callVertexOf(callerFrame, inv);
        for (ForwardFixpoint.CallerSite c : l) {
            if (c.call() == cv) {
                return;
            }
        }
        l.add(new ForwardFixpoint.CallerSite(callerMethod, cv));
    }

    private static boolean referencesPointerField(AnalysisMethod m) {
        jdk.graal.compiler.nodes.EncodedGraph g;
        try {
            g = m.getAnalyzedGraph();
        } catch (Throwable t) {
            return false;
        }
        if (g == null || g.getObjects() == null) {
            return false;
        }
        for (Object o : g.getObjects()) {
            if (o instanceof ResolvedJavaField f && isAccessorPointerField(f.getDeclaringClass().toJavaName(true), f.getName())) {
                return true;
            }
        }
        return false;
    }

    private void buildEdges() {
        // (1) the readers of the accessors' pointer fields: the OUTER sites and the coverage proof
        List<AnalysisMethod> readers = new ArrayList<>();
        for (AnalysisMethod m : rt.bridge.universeMethods()) {
            if (referencesPointerField(m)) {
                readers.add(m);
            }
        }
        readers.sort((x, y) -> key(x).compareTo(key(y)));
        List<Object[]> outer = new ArrayList<>(); // {method, frame, invoke}
        for (AnalysisMethod m : readers) {
            pointerReaderMethods++;
            StructuredGraph g = rt.graphOfMethod(m);
            if (g == null) {
                coverageProblems.add("no-graph:" + key(m));
                continue;
            }
            LocalFlowGraph f = rt.bridge.frameOf(m);
            for (Node n : g.getNodes()) {
                if (n instanceof Invoke inv && isOuterShape(inv)) {
                    outerNodes.add(n);
                    if (f == null) {
                        outerFramesMissing++;
                    } else {
                        outer.add(new Object[]{m, f, inv});
                    }
                }
            }
            for (Node n : g.getNodes()) {
                if (n instanceof LoadFieldNode lf && isAccessorPointerField(lf.field().getDeclaringClass().toJavaName(true), lf.field().getName())) {
                    pointerLoads++;
                    checkPointerUses(lf, m, 0, Collections.newSetFromMap(new IdentityHashMap<>()));
                }
            }
        }
        // (2) OUTER sites are the callers of every stub; (3) each stub's INNER site is the caller of its targets
        for (AnalysisMethod s : stubs) {
            LocalFlowGraph sf = rt.bridge.frameOf(s);
            if (sf == null) {
                // a stub without a frame: no walk enters it (MISSING_IR at the OUTER crossing); its targets lose a caller
                markTargetsIncomplete(s);
                continue;
            }
            for (Object[] o : outer) {
                addCaller(sf, (AnalysisMethod) o[0], (LocalFlowGraph) o[1], (Invoke) o[2]);
            }
            if (outerFramesMissing > 0) {
                incomplete.add(sf);
            }
            List<AnalysisMethod> targets = innerTargets.getOrDefault(s, List.of());
            StructuredGraph g = rt.graphOf(sf);
            if (g == null) {
                markTargetsIncomplete(s);
                continue;
            }
            Invoke inner = null;
            int innerCount = 0;
            ParameterNode p2 = g.getParameter(2);
            for (Node n : g.getNodes()) {
                if (n instanceof Invoke inv && inv.callTarget() instanceof IndirectCallTargetNode ict) {
                    ValueNode addr = GraphUtil.unproxify(ict.computedAddress());
                    if (p2 != null && addr == p2) {
                        inner = inv;
                        innerCount++;
                    }
                }
            }
            if (targets.isEmpty()) {
                continue; // an error stub: no INNER call is expected
            }
            if (inner == null || innerCount != 1) {
                coverageProblems.add("inner-unmatched:" + key(s) + " count=" + innerCount);
                markTargetsIncomplete(s);
                continue;
            }
            // the target pointer (parameter 2) is used only as the INNER call's address
            checkStubPointerUses(p2, (IndirectCallTargetNode) inner.callTarget(), s, Collections.newSetFromMap(new IdentityHashMap<>()));
            innerNodes.put(inner.asNode(), s);
            for (AnalysisMethod t : targets) {
                LocalFlowGraph tf = rt.bridge.frameOf(t);
                if (tf != null) {
                    addCaller(tf, s, sf, inner);
                }
            }
        }
    }

    private void checkStubPointerUses(ValueNode v, IndirectCallTargetNode inner, AnalysisMethod stub, Set<Node> seen) {
        for (Node u : v.usages()) {
            if (!seen.add(u) || u instanceof FrameState || u instanceof VirtualState || u instanceof LogicNode) {
                continue;
            }
            if (u == inner && GraphUtil.unproxify(inner.computedAddress()) == GraphUtil.unproxify(v) && !inner.arguments().contains(v)) {
                continue; // the INNER call's address, and never one of its arguments
            }
            if (u instanceof LimitedValueProxy lp && lp.getOriginalNode() == v) {
                checkStubPointerUses((ValueNode) u, inner, stub, seen);
                continue;
            }
            coverageProblems.add("stub-pointer-use:" + key(stub) + " " + u.getClass().getSimpleName());
        }
    }

    private void markTargetsIncomplete(AnalysisMethod stub) {
        innerMissing++;
        for (AnalysisMethod t : innerTargets.getOrDefault(stub, List.of())) {
            LocalFlowGraph tf = rt.bridge.frameOf(t);
            if (tf != null) {
                incomplete.add(tf);
            }
        }
    }

    /**
     * The coverage proof for one pointer value: its uses are an OUTER call (address or argument), an observation, a
     * carrier, or a return whose every IR caller's result is used the same way (one level: {@code invokeTarget}).
     */
    private void checkPointerUses(ValueNode v, AnalysisMethod where, int depth, Set<Node> seen) {
        for (Node u : v.usages()) {
            if (!seen.add(u)) {
                continue;
            }
            if (u instanceof FrameState || u instanceof VirtualState || u instanceof LogicNode) {
                continue; // metadata; a null test / comparison of the word
            }
            if (u instanceof IndirectCallTargetNode ict) {
                // Only as the OUTER call's address or its target slot (2, before the caller-sensitive class)
                boolean asAddress = ict.computedAddress() == v;
                int slots = 0;
                boolean onlyTargetSlot = true;
                for (int i = 0; i < ict.arguments().size(); i++) {
                    if (ict.arguments().get(i) == v) {
                        slots++;
                        onlyTargetSlot &= i == 2;
                    }
                }
                if (ict.invoke() != null && isOuterShape(ict.invoke()) && (asAddress && slots == 0 || !asAddress && slots == 1 && onlyTargetSlot)) {
                    continue;
                }
                coverageProblems.add("indirect-non-outer:" + key(where) + "@" + (ict.invoke() != null ? ict.invoke().bci() : -1));
                continue;
            }
            if (u instanceof LimitedValueProxy lp && lp.getOriginalNode() == v || u instanceof PhiNode || u instanceof ConditionalNode) {
                checkPointerUses((ValueNode) u, where, depth, seen);
                continue;
            }
            if (u instanceof ReturnNode) {
                if (depth >= 1) {
                    coverageProblems.add("returned-twice:" + key(where));
                    continue;
                }
                LocalFlowGraph f = rt.bridge.frameOf(where);
                List<Object[]> sites = f != null ? rt.irCallInvokesOf(f) : null;
                if (sites == null) {
                    coverageProblems.add("returned-callers-unknown:" + key(where));
                    continue;
                }
                for (Object[] s : sites) {
                    checkPointerUses((ValueNode) s[1], (AnalysisMethod) s[0], depth + 1, Collections.newSetFromMap(new IdentityHashMap<>()));
                }
                continue;
            }
            coverageProblems.add("pointer-use:" + key(where) + " " + u.getClass().getSimpleName());
        }
    }

    // ---- the registries ----
    private void readRegistries() {
        try {
            Class<?> jf = Class.forName("com.oracle.svm.hosted.jni.JNIAccessFeature", false, ReflectionBridge.class.getClassLoader());
            if (org.graalvm.nativeimage.ImageSingletons.contains(jf)) {
                Object feature = org.graalvm.nativeimage.ImageSingletons.lookup(jf);
                Field f = jf.getDeclaredField("calledJavaMethods");
                f.setAccessible(true);
                List<?> called = (List<?>) f.get(feature);
                for (Object entry : called) {
                    jniEntries++;
                    Class<?> ec = entry.getClass();
                    jniMethodObjects.add(hostedField(entry, ec, "jniMethod"));
                    for (String fn : new String[]{"targetMethod", "callWrapper", "newObjectMethod"}) {
                        noteJni(hostedField(entry, ec, fn));
                    }
                    for (String group : new String[]{"variantWrappers", "nonvirtualVariantWrappers"}) {
                        Object g = hostedField(entry, ec, group);
                        if (g != null) {
                            for (String w : new String[]{"varargs", "array", "valist"}) {
                                noteJni(hostedField(g, g.getClass(), w));
                            }
                        }
                    }
                }
            }
        } catch (Throwable t) {
            registryFailure = "jni:" + t;
        }
        try {
            Class<?> cs = Class.forName("com.oracle.svm.hosted.code.CEntryPointCallStubSupport", false, ReflectionBridge.class.getClassLoader());
            if (org.graalvm.nativeimage.ImageSingletons.contains(cs)) {
                Object support = org.graalvm.nativeimage.ImageSingletons.lookup(cs);
                Map<?, ?> cache = (Map<?, ?>) hostedField(support, cs, "cFunctionPointerCache");
                for (Map.Entry<?, ?> e : cache.entrySet()) {
                    cEntryBoxed++;
                    boxedPointerObjects.add(e.getValue());
                    AnalysisMethod t = e.getKey() instanceof MethodPointer mp && mp.getMethod() != null ? rt.bridge.resolveMethod(mp.getMethod()) : null;
                    if (t == null || !t.isNativeEntryPoint()) {
                        cEntryBoxedNonNative++; // B' premise not confirmed for this holder: its pending slot fails
                        boxedPointerObjects.remove(e.getValue());
                    }
                }
            }
        } catch (Throwable t) {
            registryFailure = (registryFailure == null ? "" : registryFailure + ";") + "centry:" + t;
        }
    }

    /**
     * A registry entry is resolved with the universe's own key (substitutions applied, as
     * {@code JNIAccessFeature.addMethod}'s {@code universe.lookup}); an entry that does not resolve is a registry failure
     * (the base predicate), never "not analysed code".
     */
    private void noteJni(Object m) {
        if (m == null) {
            return;
        }
        AnalysisMethod am = m instanceof ResolvedJavaMethod rm ? rt.bridge.resolveMethodSubstituted(rm) : null;
        if (am == null) {
            jniUnresolved++;
            registryFailure = (registryFailure == null ? "" : registryFailure + ";") + "jni-unresolved:" + (m instanceof ResolvedJavaMethod rm ? key(rm) : m.getClass().getSimpleName());
            return;
        }
        jniMethods.add(am);
    }

    /** Option D's confirmation of a B'-allowlisted pending slot: true when the registries list the holder object. */
    boolean pendingHolderConfirmed(String declaringClass, Object holderHosted) {
        if (declaringClass.equals("com.oracle.svm.core.jni.access.JNIAccessibleMethod")) {
            return holderHosted != null && jniMethodObjects.contains(holderHosted);
        }
        if (declaringClass.equals("com.oracle.svm.core.c.BoxedRelocatedPointer")) {
            if (holderHosted != null && boxedPointerObjects.contains(holderHosted)) {
                return true; // the C-entry registry's box: a native-entry stub
            }
            // a box whose hosted pointer is no method pointer (CGlobalDataInfo.CGLOBALDATA_RUNTIME_BASE_ADDRESS, a data base
            // address) holds no call target
            try {
                Object p = holderHosted instanceof com.oracle.svm.core.c.BoxedRelocatedPointer brp ? brp.getPointer() : null;
                if (p != null && !(p instanceof MethodPointer)) {
                    boxedDataPointers++;
                    return true;
                }
            } catch (Throwable t) {
                return false;
            }
            return false;
        }
        return true; // the non-pointer words of B' (CIsolateData.offset, ImageCodeInfo.*, JNIAccessibleField.id)
    }

    String census() {
        StringBuilder sb = new StringBuilder(" e3{complete=").append(complete()).append(" accessors=").append(accessors)

                        .append(" method=").append(methodAccessors).append(" ctor=").append(ctorAccessors).append(" readFailures=").append(readFailures)
                        .append(" stubs=").append(stubs.size()).append(" virtualTargets=").append(virtualTargets).append(" chaReadFailures=").append(chaReadFailures)
                        .append(" maxInnerFan=").append(maxInnerFan).append(" innerTargetEdges=").append(innerTargetEdges).append(" innerSites=").append(innerNodes.size())
                        .append(" outerSites=").append(outerNodes.size()).append(" outerFramesMissing=").append(outerFramesMissing).append(" innerMissing=").append(innerMissing)
                        .append(" bridgedCalleeFrames=").append(callers.size()).append(" incompleteFrames=").append(incomplete.size())
                        .append(" reflDirect=").append(reflDirect.size()).append(" reflVirtual=").append(reflVirtual.size())
                        .append(" pointerReaders=").append(pointerReaderMethods).append(" pointerLoads=").append(pointerLoads)
                        .append(" coverageProblems=").append(coverageProblems.size()).append(" jniEntries=").append(jniEntries).append(" jniMethods=").append(jniMethods.size())
                        .append(" cEntryBoxed=").append(cEntryBoxed).append(" cEntryBoxedNonNative=").append(cEntryBoxedNonNative).append(" boxedDataPointers=").append(boxedDataPointers)
                        .append(" jniUnresolved=").append(jniUnresolved).append(" keyCollisions=").append(keyCollisions)
                        .append(" foreignCallTargets=").append(foreignCallTargets.size()).append(" guard=").append(guardReason == null ? "none" : guardReason)
                        .append(" unplacedOuter=").append(unplacedOuter)
                        .append(" registryFailure=").append(registryFailure == null ? "none" : registryFailure.replace(' ', '_')).append(" buildMs=").append(buildMs);
        return sb.toString();
    }
}
