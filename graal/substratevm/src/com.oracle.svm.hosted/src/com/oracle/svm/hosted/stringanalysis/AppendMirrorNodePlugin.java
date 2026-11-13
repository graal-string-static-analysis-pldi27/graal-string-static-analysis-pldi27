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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import com.oracle.svm.core.graal.RuntimeCompilation;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.GraalError;
import jdk.graal.compiler.nodes.BeginNode;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.EndNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.LogicConstantNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.MergeNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ProfileData.BranchProbabilityData;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.ValuePhiNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The parent side of the builder-append mirror ({@link AppendMirror}). At an invoke whose key carries the child's
 * {@code <key> MIRROR <KIND> <rep,...>} line, the invoke is lowered to the chain
 *
 * <pre>
 * if (arg instanceof exact RepA) r = recv.mirror(..., (RepA) arg, ...)   // the invented labs member, same invoke kind
 * else if (arg instanceof exact RepB) r = recv.mirror(..., (RepB) arg, ...)
 * else r = the original invoke                                          // the parser's own path: stock inlining/intrinsics
 * </pre>
 *
 * The tests are exact and false for null, so null and every other class (plain String, flat reps, other CharSequences)
 * take the untouched original invoke; the arm's Pi is a real check (no trusted filter). For {@code INIT} the arm invokes
 * the invented {@code (String, Void)} constructor on the same receiver. The mirror has the entry's shape on the same
 * class, so a virtual entry invoke becomes a virtual mirror invoke. Arm weight: neutral 0.5 ({@link #armProfile}).
 * <p>
 * Mandatory: the child treated the site as terminal, so a MIRROR line the plugin cannot lower (wrong entry kind, an
 * interface invoke, an unknown or flat rep, a JDK without the mirror members) fails the build, never stock. Registered
 * for the analysis parse only. Runtime compilation is not covered: the multi-method variants carry the name
 * {@code name%%<key>}, so no MIRROR key matches them; an image with runtime compilation and MIRROR lines therefore fails
 * the build ({@link #runtimeCompilationRefusal}).
 */
public final class AppendMirrorNodePlugin implements NodePlugin {

    static final AtomicLong LOWERED = new AtomicLong();
    static final AtomicLong ARMS = new AtomicLong();
    static final Set<String> LOWERED_KEYS = ConcurrentHashMap.newKeySet();
    private final Map<String, ResolvedJavaMethod> mirrorCache = new ConcurrentHashMap<>();

    /** The arm's branch probability: neutral 0.5, since a rep may be the hot argument (pure; pinned by JUnit). */
    static BranchProbabilityData armProfile() {
        return BranchProbabilityData.injected(0.5);
    }

    @Override
    public boolean handleInvoke(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (InlineCacheTrivialMethodNodePlugin.isFlatReentry(b, method)) {
            return false; // the uniform first check of every string-analysis node plugin: the else's own invoke
        }
        if (!RepresentationProfileHolder.hasProfile() || RepresentationProfileHolder.getInstance().getMirrorSites().isEmpty()) {
            return false;
        }
        String refusal = runtimeCompilationRefusal(RuntimeCompilation.isEnabled(), RepresentationProfileHolder.getInstance().getMirrorSites().size());
        if (refusal != null) {
            throw new GraalError(refusal);
        }
        String key = SiteKeys.profileKey(b.getMethod(), b.bci());
        String line = RepresentationProfileHolder.getInstance().getMirror(key);
        if (line == null) {
            return false;
        }
        String[] kr = line.split(" ");
        AppendMirror.Entry e = AppendMirror.lookup(method);
        if (e == null || !e.kind().name().equals(kr[0])) {
            throw fail(key, line, "the invoke " + method.format("%H.%n(%p)") + " is not a " + kr[0] + " entry point");
        }
        InvokeKind kind = b.getInvokeKind();
        if (kind == null || kind == InvokeKind.Interface || kind == InvokeKind.Static || e.slot() >= args.length) {
            throw fail(key, line, "invoke kind " + kind);
        }
        List<ResolvedJavaType> reps = new ArrayList<>();
        for (String r : InlineCacheTrivialMethodNodePlugin.parseRepNames(kr[1], false)) {
            Class<?> c = InlineCacheRegistry.getRepClass(r);
            if (c == null || InlineCacheRegistry.isValueCarryingFlatRep(c)) {
                throw fail(key, line, "rep " + r + " is unknown or value-carrying (stock append reads its value: no mirror)");
            }
            reps.add(b.getMetaAccess().lookupJavaType(c));
        }
        ResolvedJavaMethod mirror = resolveMirror(method.getDeclaringClass(), e);
        if (mirror == null) {
            throw fail(key, line, "no mirror " + e.kind().mirrorName + e.mirrorDescriptor() + " in " + method.getDeclaringClass().toJavaName() + " (a builder JDK without the builder-append mirrors)");
        }
        lower(b, method, args, kind, e, mirror, reps);
        LOWERED.incrementAndGet();
        LOWERED_KEYS.add(key);
        return true;
    }

    /**
     * Fail-closed (pure; JUnit): the build-failure message when runtime compilation is enabled and the profile has MIRROR
     * lines, else null. The stock builder body is rep-safe, so an unlowered runtime-compiled variant would only be
     * slower, but the project scope is pure AOT: such a build must opt out explicitly with
     * {@code -J-Dsvm.stringanalysis.mirror.append=0}, which the message says.
     */
    static String runtimeCompilationRefusal(boolean runtimeCompilation, int mirrorSites) {
        if (!runtimeCompilation || mirrorSites == 0) {
            return null;
        }
        return "string-analysis MIRROR: the profile has " + mirrorSites + " " + AppendMirror.LINE_TYPE +
                        " site(s) but runtime compilation is enabled; the builder-append mirror does not cover runtime-compiled or deopt-target" +
                        " method variants (their keys never match). Build without runtime compilation, or pass -J-Dsvm.stringanalysis.mirror.append=0 (the mirror is on by default).";
    }

    private static GraalError fail(String key, String line, String why) {
        return new GraalError("string-analysis MIRROR: cannot lower " + key + " " + AppendMirror.LINE_TYPE + " " + line + ": " + why);
    }

    private ResolvedJavaMethod resolveMirror(ResolvedJavaType owner, AppendMirror.Entry e) {
        String k = owner.toJavaName() + "#" + e.kind().mirrorName + e.mirrorDescriptor();
        ResolvedJavaMethod m = mirrorCache.get(k);
        if (m != null) {
            return m;
        }
        ResolvedJavaMethod[] candidates = e.kind() == AppendMirror.Kind.INIT ? owner.getDeclaredConstructors(false) : owner.getDeclaredMethods(false);
        for (ResolvedJavaMethod c : candidates) {
            if (c.getName().equals(e.kind().mirrorName) && c.getSignature().toMethodDescriptor().equals(e.mirrorDescriptor()) && !c.isStatic()) {
                mirrorCache.put(k, c);
                return c;
            }
        }
        return null;
    }

    private static void lower(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args0, InvokeKind kind, AppendMirror.Entry e, ResolvedJavaMethod mirror,
                    List<ResolvedJavaType> reps) {
        StructuredGraph graph = b.getGraph();
        ValueNode[] args = InlineCacheTrivialMethodNodePlugin.registered(b, args0);
        ValueNode x = args[e.slot()];
        JavaKind returnKind = method.getSignature().getReturnKind();
        BranchProbabilityData profile = armProfile();
        List<EndNode> ends = new ArrayList<>();
        List<ValueNode> results = new ArrayList<>();
        for (ResolvedJavaType rep : reps) {
            TypeReference exact = TypeReference.createExactTrusted(rep);
            LogicNode test = InstanceOfNode.create(exact, x);
            if (test instanceof LogicConstantNode c && !c.getValue()) {
                continue; // the argument's stamp excludes this rep
            }
            GraalError.guarantee(!(test instanceof LogicConstantNode), "string-analysis MIRROR: the argument is always %s", rep.toJavaName());
            test = graph.addOrUniqueWithInputs(test);
            BeginNode repBegin = graph.add(new BeginNode());
            BeginNode otherBegin = graph.add(new BeginNode());
            b.add(new IfNode(test, repBegin, otherBegin, profile));
            ValueNode pi = graph.addOrUnique(new PiNode(x, StampFactory.objectNonNull(exact), repBegin));
            ValueNode[] armArgs = mirrorArgs(graph, args, e, pi);
            ValueNode r = InlineCacheTrivialMethodNodePlugin.emitBranchCall(b, repBegin, kind == InvokeKind.Virtual ? InvokeKind.Virtual : InvokeKind.Special, mirror, armArgs, returnKind);
            ends.add(b.append(new EndNode()));
            results.add(r);
            BeginNode resume = b.append(new BeginNode());
            otherBegin.setNext(resume);
            ARMS.incrementAndGet();
        }
        /* the else: the original invoke on the parser's own path (stock plugins, intrinsics, inlining) */
        InlineCacheTrivialMethodNodePlugin.withFlatReentry(b, method, () -> b.handleReplacedInvoke(kind, method, args, false));
        if (b.hasParseTerminated()) {
            throw GraalError.shouldNotReachHere("string-analysis MIRROR: the original invoke ended the block (no result to merge): " + method.format("%H.%n(%p)"));
        }
        if (ends.isEmpty()) {
            return; // every rep excluded by the argument's stamp: the original invoke alone (already on the stack)
        }
        ValueNode elseResult = returnKind == JavaKind.Void ? null : b.pop(returnKind);
        ends.add(b.append(new EndNode()));
        results.add(elseResult);
        MergeNode merge = b.append(new MergeNode());
        for (EndNode end : ends) {
            merge.addForwardEnd(end);
        }
        if (returnKind != JavaKind.Void) {
            ValuePhiNode phi = graph.addOrUnique(new ValuePhiNode(StampFactory.forKind(returnKind), merge, results.toArray(new ValueNode[0])));
            b.push(returnKind, phi);
        }
        b.setStateAfter(merge);
    }

    /** The mirror call's arguments: the entry's, the string slot replaced by the arm's Pi; INIT adds the {@code Void} null. */
    static ValueNode[] mirrorArgs(StructuredGraph graph, ValueNode[] args, AppendMirror.Entry e, ValueNode pi) {
        boolean init = e.kind() == AppendMirror.Kind.INIT;
        ValueNode[] a = new ValueNode[args.length + (init ? 1 : 0)];
        System.arraycopy(args, 0, a, 0, args.length);
        a[e.slot()] = pi;
        if (init) {
            a[args.length] = ConstantNode.defaultForKind(JavaKind.Object, graph);
        }
        return a;
    }

    static String summary() {
        Map<String, String> sites = RepresentationProfileHolder.hasProfile() ? RepresentationProfileHolder.getInstance().getMirrorSites() : Map.of();
        StringBuilder sb = new StringBuilder("[string-analysis] mirror-append: sites=" + sites.size() + " lowered-parses=" + LOWERED.get() + " arms=" + ARMS.get() + " lowered-keys=" +
                        LOWERED_KEYS.size());
        for (String k : new TreeMap<>(sites).keySet()) {
            if (!LOWERED_KEYS.contains(k)) {
                sb.append("\n[string-analysis] mirror-append: site never parsed (dead or inlined before parse): ").append(k);
            }
        }
        return sb.toString();
    }
}
