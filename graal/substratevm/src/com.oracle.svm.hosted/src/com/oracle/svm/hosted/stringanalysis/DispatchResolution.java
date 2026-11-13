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

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.oracle.graal.pointsto.flow.InvokeTypeFlow;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;

import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Deterministic dispatch resolution, shared by the forward fixpoint ({@code ForwardFixpoint}) and the LFG fixtures:
 * the closed-world deterministic CHA resolution, the canonical target order, the most-specific-override filter, the
 * sole-implementation resolution and the receiver-aware dispatch rule.
 */
final class DispatchResolution {

    private DispatchResolution() {
    }

    record ResolvedTarget(AnalysisMethod method, LocalFlowGraph lfg, LocalFlowGraph.LocalVertex testFormal,
                    boolean declaredStatic, String declaringClassName) {
    }

    /**
     * Knob {@code dispatch.cha.cap} (default 64): fan-out bound for CHA resolutions whose per-callsite identity filter
     * was uninformative. Real interface hierarchies measure in the tens; Object-declared megamorphic sites reach 300+.
     */
    static final int CHA_FANOUT_CAP = Integer.getInteger("svm.stringanalysis.dispatch.cha.cap", 64);

    /**
     * Deterministic CHA target set: for a virtual/interface invoke on declared receiver type D, the set is
     * {@code sub.resolveConcreteMethod(declaredCallee)} for every instantiated subtype of D, plus D's own resolution
     * when D is instantiated (the root clause). Static/direct invokes resolve to the declared callee.
     * Inputs are only the closed-world hierarchy and the instantiation flags: no TypeState, no getAllCallees, no
     * {@code isImplementationInvoked} (it varies with points-to linking order). D is the invoke flow's
     * {@link InvokeTypeFlow#getReceiverType()} (pre-fixpoint metadata from the receiver's IR stamp); without an
     * invoke flow, the callee's declaring class is the conservative floor.
     *
     * <p>Soundness (closed world): the runtime receiver type is an instantiated subtype R of D, and the dispatch lands
     * on {@code R.resolveConcreteMethod(declaredCallee)}, exactly the resolution added for R. Non-instantiated subtrees
     * and abstract resolutions cannot receive the dispatch; including never-invoked implementations over-approximates.
     */
    static List<AnalysisMethod> computeDeterministicChaTargets(AnalysisMethod calleeMethod, InvokeTypeFlow invoke) {
        if (calleeMethod == null) {
            return List.of();
        }
        if (calleeMethod.isStatic() || calleeMethod.canBeStaticallyBound()) {
            return List.of(calleeMethod);
        }
        if (invoke instanceof com.oracle.graal.pointsto.flow.AbstractSpecialInvokeTypeFlow) {
            // invokespecial (super./private calls) binds to exactly the callee, never a receiver-type override
            // (`super.append(str)` in StringBuilder.append must stay AbstractStringBuilder.append).
            return List.of(calleeMethod);
        }
        AnalysisType declaredReceiver = invoke != null ? invoke.getReceiverType() : null;
        if (declaredReceiver == null) {
            declaredReceiver = calleeMethod.getDeclaringClass();
        }
        return computeDeterministicChaTargets(calleeMethod, declaredReceiver);
    }

    /** Census (print-only): CHA computations where the abstract-root rule withheld a concrete own resolution of an abstract root. */
    static final java.util.concurrent.atomic.LongAdder ABSTRACT_ROOT_SKIPS = new java.util.concurrent.atomic.LongAdder();

    /** Counts an abstract-root skip that withheld a concrete target. */
    static void noteAbstractRootSkip(AnalysisType root, AnalysisMethod callee) {
        try {
            AnalysisMethod self = root.resolveConcreteMethod(callee);
            if (self == null && root.equals(callee.getDeclaringClass())) {
                self = callee;
            }
            if (self != null && !Modifier.isAbstract(self.getModifiers())) {
                ABSTRACT_ROOT_SKIPS.increment();
            }
        } catch (Throwable t) {
            // print-only
        }
    }

    /** Census (print-only): abstract-root predicate queries on an array root (each keeps the root's own resolution). */
    static final java.util.concurrent.atomic.LongAdder ARRAY_ROOT_QUERIES = new java.util.concurrent.atomic.LongAdder();

    /**
     * Whether a CHA cone root may contribute its own resolution of the callee (the abstract-root rule, counting array
     * queries). Only an abstract instance class is skipped. JVMCI (like {@code Class.getModifiers}) reports array and
     * primitive types as {@code ABSTRACT | FINAL}, yet an array is the exact runtime type of its objects and has no
     * subtypes to inherit for it: an array root always contributes its own resolution (e.g. {@code equals} on a
     * {@code String[]} receiver), or its only target would be lost.
     */
    static boolean rootContributesOwnResolution(jdk.vm.ci.meta.ResolvedJavaType root) {
        if (root != null && (root.isArray() || root.isPrimitive())) {
            ARRAY_ROOT_QUERIES.increment();
        }
        return ownResolutionIsTarget(root);
    }

    /**
     * The abstract-root rule, pure and non-counting: whether a type's own resolution of a callee can be a dispatch
     * target. False only for an abstract instance class (arrays and primitives excepted as in
     * {@link #rootContributesOwnResolution}; interfaces answer true, the callers skip them). Used by the root clause
     * and the subtype loop of {@link #computeDeterministicChaTargets(AnalysisMethod, AnalysisType)}.
     *
     * <p>The abstract-root rule: an abstract class root never contributes its own resolution. No object has an abstract
     * class as its exact runtime type, so the root's own resolution is a target only through a concrete subtype that inherits it,
     * and the subtype loop adds it for exactly that subtype. When every concrete subtype overrides it, it is never a
     * runtime target (without the rule, {@code isAnySubtypeInstantiated} admits the abstract
     * {@code TermsHashPerField.start}, whose two final subclasses both override it, and makes
     * {@code TermsHashPerField.start@14} a static self-recursion). Interfaces are excluded by the callers.
     *
     * <p>The rule also applies inside the subtype loop: {@code getAllSubtypes()} includes the root and every abstract
     * intermediate class. Both parts share this test.
     */
    static boolean ownResolutionIsTarget(jdk.vm.ci.meta.ResolvedJavaType t) {
        return t == null || t.isArray() || t.isPrimitive() || t.isInterface() || !Modifier.isAbstract(t.getModifiers());
    }

    /**
     * Census (print-only): subtype-loop entries skipped as abstract classes with a concrete own resolution. An upper
     * bound on the withheld targets: a concrete heir often re-adds the same method.
     */
    static final java.util.concurrent.atomic.LongAdder ABSTRACT_SUB_SKIPS = new java.util.concurrent.atomic.LongAdder();

    /**
     * The proven override drop over one receiver-position target set (applied in the container engine's memoised
     * crossing) (pure in (methods, blockTypes)): target M is
     * dropped iff (1) another target of the set overrides M (same name and descriptor, declared in a strict subtype
     * of M's declaring class: the most-specific-override relation), and (2)
     * the drop is proven for the block: every block type t dispatches M to another method
     * ({@code ForwardFixpoint.overrideDropProven}: exact dispatch; an unknown resolution keeps M). (1) never drops
     * every target (a most-specific target is never overridden inside the set). {@code blockTypes == null} = top:
     * nothing is dropped. Order is kept. Generic over JVMCI so a JUnit test can use host types.
     */
    static <M extends ResolvedJavaMethod> List<M> provenOverrideDrop(List<M> methods,
                    Collection<? extends jdk.vm.ci.meta.ResolvedJavaType> blockTypes) {
        if (methods == null || methods.size() <= 1 || blockTypes == null || blockTypes.isEmpty()) {
            return methods;
        }
        List<M> kept = null;
        for (int i = 0; i < methods.size(); i++) {
            M target = methods.get(i);
            boolean drop = target != null && overriddenInSet(target, methods) && ForwardFixpoint.overrideDropProven(true, blockTypes, target);
            if (drop && kept == null) {
                kept = new ArrayList<>(methods.size());
                kept.addAll(methods.subList(0, i));
            } else if (!drop && kept != null) {
                kept.add(target);
            }
        }
        return kept == null ? methods : kept;
    }

    /** Whether another method of {@code set} overrides {@code target} (the most-specific-override test). */
    static boolean overriddenInSet(ResolvedJavaMethod target, Collection<? extends ResolvedJavaMethod> set) {
        jdk.vm.ci.meta.ResolvedJavaType targetDecl = target.getDeclaringClass();
        if (targetDecl == null) {
            return false;
        }
        for (ResolvedJavaMethod other : set) {
            if (other == null || other == target) {
                continue;
            }
            jdk.vm.ci.meta.ResolvedJavaType otherDecl = other.getDeclaringClass();
            if (otherDecl == null || otherDecl.equals(targetDecl)) {
                continue;
            }
            if (target.getName().equals(other.getName()) && target.getSignature().toMethodDescriptor().equals(other.getSignature().toMethodDescriptor()) &&
                            targetDecl.isAssignableFrom(otherDecl) && !otherDecl.isAssignableFrom(targetDecl)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The explicit-root form: the same formula over a caller-supplied cone root (the arg-position stamp consult narrows
     * the root from the declared receiver to the provable may-stamp). Same soundness contract: every runtime receiver
     * is an instantiated subtype of some root, and the per-subtype resolution is its dispatch target.
     */
    static List<AnalysisMethod> computeDeterministicChaTargets(AnalysisMethod calleeMethod, AnalysisType declaredReceiver) {
        if (calleeMethod == null) {
            return List.of();
        }
        if (declaredReceiver == null) {
            return List.of();
        }
        Set<AnalysisMethod> targets = new HashSet<>();
        // The root contributes the method it dispatches to, not the callee. The receiver type can be narrower than
        // the callee's declaring class (`CharSequence cs = s; cs.chars()` has receiver type String); adding the
        // callee would add CharSequence.chars, never executed for a String receiver (no LFG, dropped as a dead
        // target: the call vanishes, a false ADMIT). An interface/abstract root
        // contributes nothing itself; the subtype loop covers its implementors.
        if (declaredReceiver.isAnySubtypeInstantiated() && !declaredReceiver.isInterface() && !rootContributesOwnResolution(declaredReceiver)) {
            noteAbstractRootSkip(declaredReceiver, calleeMethod);
        } else if (declaredReceiver.isAnySubtypeInstantiated() && !declaredReceiver.isInterface()) {
            AnalysisMethod self = declaredReceiver.resolveConcreteMethod(calleeMethod);
            if (self == null && declaredReceiver.equals(calleeMethod.getDeclaringClass())) {
                self = calleeMethod;
            }
            if (self != null && !Modifier.isAbstract(self.getModifiers())) {
                targets.add(self);
            }
        }

        if (declaredReceiver.hasSubTypes()) {
            // getAllSubtypes may exclude array types; array receivers only dispatch Object's methods (plus clone),
            // which the root clause (D = Object for array-stamped receivers) and the override-search fallback cover.
            for (AnalysisType sub : declaredReceiver.getAllSubtypes()) {
                if (sub.isInterface() || !sub.isAnySubtypeInstantiated()) {
                    continue;
                }
                if (!ownResolutionIsTarget(sub)) {
                    // An abstract class is never an exact runtime type; an inherited method is kept through its
                    // concrete heir, which resolves for itself.
                    AnalysisMethod skipped = sub.resolveConcreteMethod(calleeMethod);
                    if (skipped != null && !Modifier.isAbstract(skipped.getModifiers())) {
                        ABSTRACT_SUB_SKIPS.increment();
                    }
                    continue;
                }
                // No isImplementationInvoked guard: it depends on points-to linking order (the CHA sets would vary
                // run-to-run). Including never-invoked implementations is a sound over-approximation.
                AnalysisMethod resolvedMethod = sub.resolveConcreteMethod(calleeMethod);
                if (resolvedMethod != null && !Modifier.isAbstract(resolvedMethod.getModifiers())) {
                    targets.add(resolvedMethod);
                }
            }
        }
        return sortTargetsDeterministically(targets);
    }

    /**
     * Canonical target order by {@code format("%H.%n") + signature}, so the resolution and every downstream iteration
     * are a pure function of the closed world.
     */
    static List<AnalysisMethod> sortTargetsDeterministically(Collection<AnalysisMethod> targets) {
        List<AnalysisMethod> sorted = new ArrayList<>(targets);
        if (sorted.size() > 1) {
            // Hot: the key is cached per method (SORT_KEYS) instead of formatted on every comparison.
            sorted.sort(Comparator.comparing(DispatchResolution::deterministicSortKey));
        }
        return sorted;
    }

    /** The cached canonical sort key (pure per method). */
    private static final java.util.concurrent.ConcurrentHashMap<AnalysisMethod, String> SORT_KEYS = new java.util.concurrent.ConcurrentHashMap<>();

    static String deterministicSortKey(AnalysisMethod m) {
        String k = SORT_KEYS.get(m);
        if (k == null) {
            k = m.format("%H.%n") + m.getSignature();
            SORT_KEYS.putIfAbsent(m, k);
        }
        return k;
    }

    /**
     * Whether {@code method} is declared on an interface or is abstract: the dispatch for which the override search
     * ({@code collectMethodImplementations}) can come back empty although a sole concrete implementation exists. Only
     * these get the sole-implementation resolution; an empty search for a concrete method is genuinely unknown.
     */
    static boolean isInterfaceOrAbstractVirtual(AnalysisMethod method) {
        AnalysisType declaring = method.getDeclaringClass();
        if (declaring != null && declaring.isInterface()) {
            return true;
        }
        return Modifier.isAbstract(method.getModifiers());
    }

    /**
     * Bound on the subtypes scanned by {@link #soleImplementationOfAbstract}; a wider hierarchy bails to the
     * conservative UNKNOWN_TARGET path (a sole implementation is unlikely there, and the search stays bounded).
     */
    private static final int SOLE_IMPL_SCAN_LIMIT = 256;

    /**
     * Sole-implementation resolution for an interface/abstract method whose {@code collectMethodImplementations}
     * search is empty: if exactly one invoked, instantiated concrete implementation exists among the declaring type's
     * subtypes, return it as a singleton; otherwise the empty set (UNKNOWN_TARGET, conservative).
     *
     * <p>Soundness (closed world): no later-instantiated subtype exists in the image, and subtypes not instantiated or
     * invoked at analysis time cannot be dispatched to. The resolved body is traced normally and emits its own usage and
     * incompleteness facts, so this removes only a spurious UNKNOWN_TARGET, never a real unsafe usage.
     */
    static Set<AnalysisMethod> soleImplementationOfAbstract(AnalysisMethod declaredMethod) {
        AnalysisType declaring = declaredMethod.getDeclaringClass();
        if (declaring == null) {
            return Set.of();
        }
        // Candidates: the declaring type's subtypes, bounded by SOLE_IMPL_SCAN_LIMIT.
        Set<AnalysisType> candidates = new HashSet<>();
        if (!declaring.hasSubTypes()) {
            return Set.of();
        }
        Collection<AnalysisType> subs = declaring.getAllSubtypes();
        if (subs.size() > SOLE_IMPL_SCAN_LIMIT) {
            return Set.of();
        }
        for (AnalysisType t : subs) {
            candidates.add(t);
        }
        if (candidates.isEmpty() || candidates.size() > SOLE_IMPL_SCAN_LIMIT) {
            return Set.of();
        }
        Set<AnalysisMethod> found = new HashSet<>();
        for (AnalysisType subtype : candidates) {
            if (subtype == null || subtype.isInterface() || !subtype.isAnySubtypeInstantiated()) {
                continue;
            }
            AnalysisMethod resolved = subtype.resolveConcreteMethod(declaredMethod);
            if (resolved != null && resolved.isImplementationInvoked() && !Modifier.isAbstract(resolved.getModifiers())) {
                found.add(resolved);
                if (found.size() > 1) {
                    // Not sole: conservative UNKNOWN_TARGET.
                    return Set.of();
                }
            }
        }
        return found;
    }

    // The receiver-aware dispatch rule. A crossing's committed fan (the CHA targets after the block filters) is
    // narrowed to what the call's receiver can dispatch to, given its exact types. The facts per position
    // (RecursiveTracking): at the receiver position, the atom's exact birth type (the exactrecv rule); at a backward
    // invoke result, the receiver sink's atoms per context; at an argument position and at a backward result, the
    // call's final points-to receiver state (the points-to receiver rule). A receiver of exact type R dispatches to R's
    // resolution of the callee (AnalysisType.resolveConcreteMethod, pure in the closed world). The rule never adds a
    // target, and any doubt keeps the committed fan: a type with no resolution, a resolution outside the fan, no type,
    // or no narrowing.

    /**
     * The fan target a receiver of exact type {@code receiverType} dispatches to: its resolution of {@code callee},
     * when that is a method of {@code fan}; null = doubt (unknown type, no resolution, or one outside the fan).
     */
    static AnalysisMethod receiverDispatchTarget(AnalysisType receiverType, ResolvedJavaMethod callee, List<ResolvedTarget> fan) {
        if (receiverType == null || callee == null || fan == null) {
            return null;
        }
        AnalysisMethod m;
        try {
            m = receiverType.resolveConcreteMethod(callee);
        } catch (Throwable t) {
            return null;
        }
        if (m == null) {
            return null;
        }
        for (ResolvedTarget t : fan) {
            if (m.equals(t.method())) {
                return m;
            }
        }
        return null;
    }

    /**
     * The fan narrowed to what receivers of the exact types {@code receiverTypes} dispatch to (every fan entry whose
     * method one of them selects, in fan order), or null = keep the committed fan: no type, a doubt on any type
     * ({@link #receiverDispatchTarget}), or no narrowing.
     */
    static List<ResolvedTarget> receiverDispatchTargets(Collection<AnalysisType> receiverTypes, ResolvedJavaMethod callee, List<ResolvedTarget> fan) {
        if (receiverTypes == null || receiverTypes.isEmpty() || fan == null || fan.size() < 2) {
            return null;
        }
        Set<AnalysisMethod> selected = new HashSet<>();
        for (AnalysisType r : receiverTypes) {
            AnalysisMethod m = receiverDispatchTarget(r, callee, fan);
            if (m == null) {
                return null;
            }
            selected.add(m);
        }
        List<ResolvedTarget> out = new ArrayList<>(selected.size());
        for (ResolvedTarget t : fan) {
            if (selected.contains(t.method())) {
                out.add(t);
            }
        }
        return out.size() == fan.size() ? null : out;
    }

    // The receiver-typed caller filter for path-less caller fans (the mirror of the points-to receiver rule): a caller
    // site of a frame of method M is dropped only when the call's final points-to receiver state proves that no
    // receiver dispatches to M; every doubt keeps the site.

    /** The drop decision's name; every other value of {@link #callerSiteDecision} is a keep reason. */
    static final String CALLER_DROP = "drop";

    /**
     * The decision for one caller site of a frame of method {@code frameMethod}: the site's call has declared callee
     * {@code declaredCallee}, final points-to receiver types {@code types} (null = unavailable) and committed CHA fan
     * {@code fan}. {@link #CALLER_DROP} iff every receiver type resolves (inside the fan) to a method other than the
     * frame's; otherwise a keep reason: {@code direct} (a static frame or a static/statically bound callee: no receiver
     * dispatch), {@code noTypes}, {@code empty}, {@code typeOutsideFan} (a type with no resolution, or one outside the
     * fan: the points-to receiver rule's own doubt) or {@code dispatches} (some receiver type selects the frame's method).
     */
    static String callerSiteDecision(Collection<AnalysisType> types, AnalysisMethod declaredCallee, AnalysisMethod frameMethod, List<ResolvedTarget> fan) {
        if (frameMethod == null || declaredCallee == null || frameMethod.isStatic() || declaredCallee.isStatic() || declaredCallee.canBeStaticallyBound()) {
            return "direct";
        }
        if (types == null) {
            return "noTypes";
        }
        if (types.isEmpty()) {
            return "empty";
        }
        boolean dispatches = false;
        for (AnalysisType r : types) {
            AnalysisMethod t = receiverDispatchTarget(r, declaredCallee, fan);
            if (t == null) {
                return "typeOutsideFan";
            }
            if (t.equals(frameMethod)) {
                dispatches = true;
            }
        }
        return dispatches ? "dispatches" : CALLER_DROP;
    }

    /**
     * The list-level rule: the sites {@code keep} accepts, in list order; the unfiltered list when nothing is dropped
     * or when everything would be (never empty: a walk inside a method no analysed caller dispatches to is a
     * contradiction, so the committed fan stays; it must not become a new no-caller or world-top refusal).
     */
    static <S> List<S> keepNeverEmpty(List<S> all, java.util.function.Predicate<S> keep) {
        if (all == null || all.isEmpty()) {
            return all;
        }
        List<S> out = new ArrayList<>(all.size());
        for (S s : all) {
            if (keep.test(s)) {
                out.add(s);
            }
        }
        return out.isEmpty() || out.size() == all.size() ? all : out;
    }
}
