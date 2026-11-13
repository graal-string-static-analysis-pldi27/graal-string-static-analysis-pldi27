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

import java.lang.reflect.Method;

import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.LogicConstantNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.ProfileData.BranchProbabilityData;
import jdk.graal.compiler.nodes.ShortCircuitOrNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.ConditionalNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * A {@link NodePlugin} for the analysis parse that intercepts {@code Object.equals(Object)} and
 * {@code String.equals(Object)} sites whose profile entry is {@link OptimizationType#EQUALS_MATRIX}
 * {@link EqualsMatrixHeuristic#VARIANT_REDIRECT}. At {@code String.equals} sites the invoke becomes a virtual
 * {@code String.maybeCustomStringEquals(Object)}. At {@code Object.equals} sites (no virtual
 * {@code Object.maybeCustomStringEquals}: an Object vtable slot would shift every vtable offset from stock) the site
 * stays one virtual {@code equals}, with an exact-String receiver and a String argument swapped
 * ({@link #emitObjectRedirectSwap}). This deflects rep arguments to the rep's {@code equals} before they reach
 * {@code String.equals} (which would NPE on a {@code null} {@code value} field), keeping stock virtual dispatch for every
 * non-exact-String receiver. {@link EqualsMatrixHeuristic#VARIANT_FAST_PATH} sites and sites without an entry are left
 * to the {@code String.equals} intrinsic, as in stock. Sites are keyed by {@code SiteKeys.profileKey}; without a
 * profile the plugin does nothing.
 * <p>
 * {@link InlineCacheTrivialMethodNodePlugin} runs first and owns every String-declared REDIRECT lowering. This plugin
 * is the residual and the Object-declared rule: the swapped virtual {@code equals} at Object sites, and one virtual
 * {@code String.maybeCustomStringEquals} at String sites the other plugin declined (over-cap rep lists, unknown rep
 * names), sound for any receiver.
 * <p>
 * This replacement is deliberately outside the scope of the always-virt rule
 * ({@code StringAnalysisPolicy.alwaysVirtJdkTrivialApplies}), which removes only performance claims. It is the correctness floor for the
 * equals argument: a stock virtual {@code equals} whose receiver cone is clean devirtualizes into Graal's unguarded
 * {@code StringEqualsInvocationPlugin} field-read intrinsic, which NPEs on a value-null rep argument -- exactly at
 * REDIRECT sites, whose defining property is that the argument can be a rep. So a String-declared REDIRECT site in the
 * rule's scope falls back to this residual, and Object-declared REDIRECT sites (e.g. {@code HashMap#getNode}'s
 * {@code key.equals(k)}) keep the same form either way.
 * <p>
 * compareTo mirror: the same residual for a String-declared {@code compareTo(String)} at an {@code EQUALS_MATRIX
 * REDIRECT} site (a user site or the bridge's {@code String#compareTo(Object)@5}) that
 * {@link InlineCacheTrivialMethodNodePlugin} declined: one virtual {@code String.maybeCustomStringCompareTo}. It deflects
 * a non-String argument to the argument's own {@code compareTo} (negated), and every value-null rep overrides it with its
 * own {@code compareTo}, so it is sound for every receiver and argument class. Outside the always-virt scope too, for the
 * same reason.
 */
public final class EqualsMatrixNodePlugin implements NodePlugin {

    private static final String OBJECT_CLASS = "java.lang.Object";
    private static final String STRING_CLASS = "java.lang.String";
    /** The invented static Object-declared REDIRECT target {@code String.objectMaybeCustomStringEquals(Object,Object)}. */
    static final String OBJECT_REDIRECT_TARGET = "objectMaybeCustomStringEquals";

    private volatile ResolvedJavaMethod objectMaybeCustomStringEqualsMethod;
    private volatile ResolvedJavaMethod stringMaybeCustomStringEqualsMethod;

    @Override
    public boolean handleInvoke(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (InlineCacheTrivialMethodNodePlugin.isFlatReentry(b, method)) {
            return false; // the IC's flat call re-parsed on the stock path
        }
        if (!hasProfile()) {
            return false;
        }
        if (ZeroAdmitStock.active()) {
            return false; // a zero-admit profile compiles String as OFF does
        }
        try {
            String decl = method.getDeclaringClass().toJavaName();
            String name = method.getName();
            // compareTo mirror: a String-declared compareTo(String) at a REDIRECT site the IC plugin declined
            boolean cmp = decl.equals(STRING_CLASS) && (name + method.getSignature().toMethodDescriptor()).equals(InlineCacheTrivialMethodNodePlugin.COMPARE_TO_STRING);
            if (!cmp && (!(decl.equals(OBJECT_CLASS) || decl.equals(STRING_CLASS)) || !name.equals("equals"))) {
                return false;
            }
            if (args.length != 2) {
                return false;
            }
            /*
             * Only a dispatched call is a REDIRECT: a super.equals(o) never reaches a String body, and rewriting it into
             * a virtual call would recurse into the caller's override.
             */
            InvokeKind kind = b.getInvokeKind();
            if (kind != InvokeKind.Virtual && kind != InvokeKind.Interface) {
                return false;
            }

            String loc = sourceLocation(b);
            ProfileEntry entry = lookupEntry(loc);
            if (entry == null) {
                return false;
            }
            if (!EqualsMatrixHeuristic.VARIANT_REDIRECT.equals(entry.getVariant())) {
                return false;
            }

            ResolvedJavaMethod target = cmp ? resolveMaybeCustomStringCompareTo(b) : resolveMaybeCustomStringEquals(b, decl);
            if (target == null) {
                return false;
            }

            if (!cmp && decl.equals(OBJECT_CLASS)) {
                return emitObjectRedirectSwap(b, method, args);
            }
            b.handleReplacedInvoke(target.isStatic() ? InvokeKind.Static : InvokeKind.Virtual, target, args, false);
            return true;
        } catch (Throwable t) {
            return false;
        }
    }

    /**
     * Object-declared REDIRECT: it stays one virtual {@code Object.equals} invoke, as stock; only the pair the parent's
     * {@code String.equals} intrinsic cannot take is asked the other way round:
     * <pre>
     * notRare = !(recv is an exact String) || !(arg instanceof String)
     * (notRare ? recv : arg).equals(notRare ? arg : recv)
     * </pre>
     * An exact-String receiver with a String argument becomes {@code arg.equals(recv)}, the deflection of
     * {@code String.maybeCustomStringEquals} (a rep argument runs its own {@code equals}; two plain Strings are compared by
     * the symmetric intrinsic). Every other pair is the original call: a rep receiver runs its own {@code equals} (= its
     * {@code mCSE}: the value-null reps override {@code mCSE} with {@code this.equals(that)}; the flat
     * {@code SingleByteString} and {@code TrivialString} inherit the deflecting {@code String.mCSE} and their
     * {@code equals} is the same content equality, {@code RepEqualsMatrixTest}); a non-String receiver runs its own
     * {@code equals}; a null receiver throws in the invoke; a null argument is not a String. So dispatch equals what a
     * virtual {@code Object.maybeCustomStringEquals} would do, with no Object member.
     * <p>
     * Unlike a call of the static twin {@code String.objectMaybeCustomStringEquals} (which inlined leaves two indirect
     * calls per site typed with the union of every site's flows), the invoke here is typed by the site's own flows, and
     * {@link RepDispatchAccounting#redirectSwapNodes} keeps the swap nodes out of the trivial-method count.
     */
    private static boolean emitObjectRedirectSwap(GraphBuilderContext b, ResolvedJavaMethod equalsMethod, ValueNode[] args) {
        StructuredGraph graph = b.getGraph();
        ValueNode receiver = args[0].isUnregistered() ? b.add(args[0]) : args[0];
        ValueNode arg = args[1].isUnregistered() ? b.add(args[1]) : args[1];
        args[0] = receiver; // the original invoke (early return below) uses the registered nodes
        args[1] = arg;
        ResolvedJavaType string = b.getMetaAccess().lookupJavaType(String.class);
        LogicNode recvExact = InstanceOfNode.create(TypeReference.createExactTrusted(string), receiver);
        LogicNode argString = InstanceOfNode.create(TypeReference.createTrustedWithoutAssumptions(string), arg);
        if (recvExact instanceof LogicConstantNode c1 && !c1.getValue() || argString instanceof LogicConstantNode c2 && !c2.getValue()) {
            return false; // never the rare pair: the original virtual equals is exactly the REDIRECT here
        }
        LogicNode notRare = graph.addOrUniqueWithInputs(ShortCircuitOrNode.create(graph.addOrUniqueWithInputs(recvExact), true, graph.addOrUniqueWithInputs(argString), true,
                        BranchProbabilityData.unknown()));
        ValueNode r = graph.addOrUniqueWithInputs(new ConditionalNode(notRare, receiver, arg));
        ValueNode a = graph.addOrUniqueWithInputs(new ConditionalNode(notRare, arg, receiver));
        InlineCacheTrivialMethodNodePlugin.emitCallAtParser(b, InvokeKind.Virtual, equalsMethod, new ValueNode[]{r, a}, equalsMethod.getSignature().getReturnKind());
        SWAP_SITES.incrementAndGet();
        return true;
    }

    /** The Object-declared REDIRECT sites swapped (census only). */
    static final java.util.concurrent.atomic.AtomicLong SWAP_SITES = new java.util.concurrent.atomic.AtomicLong();

    /**
     * The equals REDIRECT target that no Java code calls, {@code String.maybeCustomStringEquals(Object)}: rooted in the
     * child ({@link ExtraRootsDiscovery}); empty on a builder JDK without the member.
     */
    static java.util.List<Method> redirectTargets() {
        try {
            return java.util.List.of(String.class.getMethod("maybeCustomStringEquals", Object.class));
        } catch (NoSuchMethodException e) {
            return java.util.List.of();
        }
    }

    private static boolean hasProfile() {
        return RepresentationProfileHolder.hasProfile();
    }

    private static ProfileEntry lookupEntry(String sourceLocation) {
        if (RepresentationProfileHolder.hasProfile()) {
            return RepresentationProfileHolder.getInstance().getEntry(sourceLocation, OptimizationType.EQUALS_MATRIX);
        }
        return null;
    }

    private static String sourceLocation(GraphBuilderContext b) {
        return SiteKeys.profileKey(b.getMethod(), b.bci());
    }

    private volatile ResolvedJavaMethod stringMaybeCustomStringCompareToMethod;

    /**
     * compareTo mirror: the virtual residual {@code String.maybeCustomStringCompareTo(String)}, sound for every
     * receiver: a value-null rep overrides it with its own total comparison, a plain String or flat rep runs String's
     * body, which deflects a non-String argument to {@code -another.compareTo(this)}.
     */
    private ResolvedJavaMethod resolveMaybeCustomStringCompareTo(GraphBuilderContext b) {
        ResolvedJavaMethod cached = stringMaybeCustomStringCompareToMethod;
        if (cached != null) {
            return cached;
        }
        try {
            cached = b.getMetaAccess().lookupJavaMethod(String.class.getMethod("maybeCustomStringCompareTo", String.class));
            stringMaybeCustomStringCompareToMethod = cached;
            return cached;
        } catch (NoSuchMethodException e) {
            return null;
        }
    }

    private ResolvedJavaMethod resolveMaybeCustomStringEquals(GraphBuilderContext b, String decl) {
        boolean objectDecl = decl.equals(OBJECT_CLASS);
        ResolvedJavaMethod cached = objectDecl ? objectMaybeCustomStringEqualsMethod : stringMaybeCustomStringEqualsMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = objectDecl ? String.class.getMethod(OBJECT_REDIRECT_TARGET, Object.class, Object.class) : String.class.getMethod("maybeCustomStringEquals", Object.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            if (objectDecl) {
                objectMaybeCustomStringEqualsMethod = resolved;
            } else {
                stringMaybeCustomStringEqualsMethod = resolved;
            }
            return resolved;
        } catch (NoSuchMethodException e) {
            return null;
        }
    }
}