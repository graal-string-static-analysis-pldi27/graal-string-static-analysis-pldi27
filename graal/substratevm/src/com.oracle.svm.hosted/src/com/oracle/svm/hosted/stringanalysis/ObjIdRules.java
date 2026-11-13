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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;

import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.EntryList;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.vm.ci.hotspot.HotSpotResolvedJavaMethod;
import jdk.vm.ci.meta.ConstantPool;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaField;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.JavaMethod;
import jdk.vm.ci.meta.JavaType;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Lambda object-identity tracking (phase 1): the pure decision rules of the identity caller set, pinned by
 * {@code ObjectIdentityTest}. Structural only: no rule reads a class or method name.
 * <ul>
 * <li>{@link #qualifies}: a path-less return (or parameter) out of an instance frame {@code M} of class {@code C} may use
 * the identity caller set only when every receiver that dispatches to {@code M} is a {@code C} instance: {@code M} is
 * declared by {@code C}, {@code C} is concrete and instantiated, and no proper subtype of {@code C} is instantiated (so
 * no super call into {@code M} exists either). Only a hidden class ({@code Class.isHidden()}: the LMF lambda classes,
 * which are final) qualifies, the scope premise P-FB was accepted for (no bytecode can name a hidden class); an
 * ordinary class keeps the receiver-filtered path-less caller fan.</li>
 * <li>{@link #guard}: the birth set of {@code C} (allocation births only in phase 1) is complete under premise P-FB: a
 * foreign birth (Unsafe, JNI {@code AllocObject}, MH {@code allocateInstance}, reflection) needs {@code C}'s Class
 * object, which comes only from {@code getClass()} of an instance (the query walk refuses it: {@code CLASS_ESCAPE}), a
 * class constant (the IR scan / the heap holder index), a registry (read here), or raw-memory enumeration (the accepted
 * residual). The raw-memory producers that hand a lambda's Class object to Java code are checked once per image (the
 * conditional premise, {@link #premiseVerdict}: G1 a stack walker showing hidden frames, G2 getClassContext, G3
 * getCallerClass from application code, G4 an Instrumentation; any of them = no lambda qualifies in that image; G5 per
 * class: the lambda itself calls a CallerSensitive method); the still-pending heap slots must be on the audited
 * {@link #PENDING_ALLOW} list.</li>
 * <li>{@link #callerUnion}: the caller set is the union of the births' entry lists (each birth a merged query atom);
 * the first refusal of any of them adds the receiver-filtered path-less caller fan once (a pure union, as
 * the owner-return fallback, {@code RecursiveTracking.ownerRetFallbacks}).</li>
 * </ul>
 */
final class ObjIdRules {
    private ObjIdRules() {
    }

    /** Phase 1: at most this many framed allocation births per class (else the path-less caller fan). */
    static final int MAX_BIRTHS = 4;

    /** Why a frame does not qualify (null = it qualifies). Checked in this order. */
    enum NoQualify {
        STATIC,
        /** Not a hidden class (P-FB is accepted for hidden, i.e. lambda, classes only). */
        NOT_HIDDEN,
        ABSTRACT_OR_INTERFACE,
        NOT_INSTANTIATED,
        INSTANTIATED_SUBTYPE,
        UNREADABLE
    }

    /** Why a qualifying class's birth set is not usable (null = the guard passes). Checked in this order. */
    enum GuardFail {
        /**
         * The per-image conditional premise fails (G1 SW_HIDDEN, G2 CLASSCTX, G3 GCC_NONJDK or G4 INSTR, census
         * {@code objid.w2.premise}): a raw-memory producer may hand a lambda's Class object to Java code in this image.
         */
        PREMISE,
        /** G5: C's own bytecode invokes a {@code @CallerSensitive} method directly (its caller class is C). */
        LAMBDA_CSM,
        /** The birth index failed (enumeration error, frame count mismatch, a build mode outside the closed world). */
        INDEX_FAILED,
        /** A reachable method declared by C has no IR frame the walk can see (its uses of C's instances are unknown). */
        UNFRAMED_METHOD,
        /**
         * A reachable method without a frame names C in its bytecode ({@code new}, an array allocation, an {@code ldc}
         * class constant), or holds an {@code invokedynamic} and is declared by C's nest host (a capture site the index
         * cannot see), or C's host is unresolvable.
         */
        UNFRAMED_BIRTH,
        /**
         * A framed birth no walk can start from: a virtual instance of C committed without its own AllocatedObject (it is
         * only a slot value of another committed object, e.g. {@code m.invoke(null, allocateInstance(f.getClass()))}).
         */
        UNWALKABLE_BIRTH,
        /** Image-heap instances of C (singleton births: phase 2). */
        HEAP_INSTANCE,
        /** No framed allocation of C while C is instantiated (a non-intrinsified capture site, a synthesised factory). */
        NO_FRAMED_BIRTH,
        /** More than {@link #MAX_BIRTHS} framed allocations. */
        TOO_MANY_BIRTHS,
        /** P-FB (b): a framed graph holds a Class constant of C (or of an array of C) other than as an allocation type. */
        CLASS_CONSTANT,
        /** P-FB (b): an image-heap slot holds C's Class object (or the heap index is unavailable). */
        CLASS_HOLDER,
        /** P-FB (c): C is registered for reflection, JNI or {@code Class.forName} (or the registries are unreadable). */
        REGISTERED,
        /**
         * A still-pending read heap slot (never scanned) may hold C's Class object or a C instance by its declared-type
         * closure ({@link #slotClosure}), and its kind is not on {@link #PENDING_ALLOW}.
         */
        PENDING_SLOT
    }

    static NoQualify qualifies(boolean isStatic, boolean hidden, boolean abstractOrInterface, boolean instantiated, boolean instantiatedProperSubtype) {
        if (isStatic) {
            return NoQualify.STATIC;
        }
        if (!hidden) {
            return NoQualify.NOT_HIDDEN;
        }
        if (abstractOrInterface) {
            return NoQualify.ABSTRACT_OR_INTERFACE;
        }
        if (!instantiated) {
            return NoQualify.NOT_INSTANTIATED;
        }
        if (instantiatedProperSubtype) {
            return NoQualify.INSTANTIATED_SUBTYPE;
        }
        return null;
    }

    /** The qualification rule on real types: {@code declaring} is the frame method's declaring class. */
    static NoQualify qualifies(boolean isStatic, AnalysisType declaring) {
        return qualifies(isStatic, declaring, AnalysisType::getJavaClass);
    }

    /** As above; {@code javaClassOf} reads the hosted Class (the JUnit fixture has no original-class provider). */
    static NoQualify qualifies(boolean isStatic, AnalysisType declaring, Function<AnalysisType, Class<?>> javaClassOf) {
        try {
            boolean ai = declaring.isInterface() || declaring.isAbstract() || declaring.isArray();
            boolean sub = false;
            if (!isStatic && !ai) {
                for (AnalysisType s : declaring.getAllSubtypes()) {
                    if (!s.equals(declaring) && s.isInstantiated()) {
                        sub = true;
                        break;
                    }
                }
            }
            Class<?> jc = javaClassOf.apply(declaring);
            return qualifies(isStatic, jc != null && jc.isHidden(), ai, declaring.isInstantiated(), sub);
        } catch (Throwable t) {
            return NoQualify.UNREADABLE; // fail closed: the path-less caller fan
        }
    }

    static GuardFail guard(boolean premiseFails, boolean lambdaCsm, boolean indexFailed, int unframedMethods, boolean unframedBirth, boolean unwalkableBirth, int heapInstances, int births,
                    int classConstants,
                    int classHolders, boolean registered, int pendingNotAllowed) {
        if (premiseFails) {
            return GuardFail.PREMISE;
        }
        if (lambdaCsm) {
            return GuardFail.LAMBDA_CSM;
        }
        if (indexFailed) {
            return GuardFail.INDEX_FAILED;
        }
        if (unframedMethods > 0) {
            return GuardFail.UNFRAMED_METHOD;
        }
        if (unframedBirth) {
            return GuardFail.UNFRAMED_BIRTH;
        }
        if (unwalkableBirth) {
            return GuardFail.UNWALKABLE_BIRTH;
        }
        if (heapInstances > 0) {
            return GuardFail.HEAP_INSTANCE;
        }
        if (births == 0) {
            return GuardFail.NO_FRAMED_BIRTH;
        }
        if (births > MAX_BIRTHS) {
            return GuardFail.TOO_MANY_BIRTHS;
        }
        if (classConstants > 0) {
            return GuardFail.CLASS_CONSTANT;
        }
        if (classHolders > 0) {
            return GuardFail.CLASS_HOLDER;
        }
        if (registered) {
            return GuardFail.REGISTERED;
        }
        if (pendingNotAllowed > 0) {
            return GuardFail.PENDING_SLOT;
        }
        return null;
    }

    /**
     * The sound declared-type closure: the types whose instances a slot of the declared types {@code roots} may reach without leaving the slot's (unscanned) subtree: the roots, the component of
     * an array, and the declared type of every reference instance field of the type or of any of its subtypes in the
     * universe, transitively. Word types and primitives hold nothing. Null = the closure reaches {@code Object} (the slot
     * may hold anything). Heap values conform to their declared Java types (a build-time Unsafe write that breaks Java
     * typing is the named raw-memory residual). Structural only, no names.
     */
    static Set<AnalysisType> slotClosure(Collection<AnalysisType> roots) {
        Set<AnalysisType> seen = new LinkedHashSet<>();
        ArrayDeque<AnalysisType> work = new ArrayDeque<>();
        for (AnalysisType r : roots) {
            if (r == null) {
                return null; // an unknown declared type: fail closed (may hold anything)
            }
            work.add(r);
        }
        while (!work.isEmpty()) {
            AnalysisType t = work.poll();
            if (t.getJavaKind() != JavaKind.Object || t.isWordType() || !seen.add(t)) {
                continue;
            }
            if (t.isJavaLangObject()) {
                return null;
            }
            if (t.isArray()) {
                AnalysisType ct = t.getComponentType();
                if (ct == null) {
                    return null;
                }
                work.add(ct);
                continue;
            }
            List<AnalysisType> sub = new ArrayList<>(t.getAllSubtypes());
            sub.add(t);
            for (AnalysisType s : sub) {
                for (ResolvedJavaField f : s.getInstanceFields(true)) {
                    if (f.getJavaKind() == JavaKind.Object) {
                        AnalysisType ft = f instanceof AnalysisField af ? af.getType() : null;
                        if (ft == null) {
                            return null; // an unresolvable field type: fail closed
                        }
                        work.add(ft);
                    }
                }
            }
        }
        return seen;
    }

    /** Whether a slot with the declared-type {@code closure} ({@link #slotClosure}; null = anything) may hold a {@code target}. */
    static boolean mayHold(Set<AnalysisType> closure, AnalysisType target) {
        if (closure == null) {
            return true;
        }
        for (AnalysisType t : closure) {
            if (t.isAssignableFrom(target)) {
                return true;
            }
        }
        return false;
    }

    /** The registration primitive of {@link #wireUnion} (production: the census-counting RT register). */
    interface Registrar {
        void register(EntryList<?> list, Object key, Consumer<Integer> onEntry, Consumer<RTrackRefusal> onRefusal);
    }

    /**
     * The production wiring of the identity caller set (the return and the parameter hooks): one waiter per birth's
     * entry list; every entry of every list is delivered ({@code onEntry}; the precise deliveries stay registered after a
     * fallback: a pure union); the first refusal of any birth's table (before registration, after deliveries, or
     * inherited later: the replay of {@link EntryList#register} and {@code Table.refuse} wake every waiter) runs
     * {@code fanOnce} exactly once. Returns the one-shot flag (set = the fan ran).
     */
    static <T> AtomicBoolean wireUnion(List<EntryList<T>> lists, Function<EntryList<T>, Object> keyOf, Registrar reg, BiConsumer<EntryList<T>, Integer> onEntry,
                    BiConsumer<EntryList<T>, RTrackRefusal> fanOnce) {
        return wireUnion(new AtomicBoolean(), lists, keyOf, reg, onEntry, fanOnce);
    }

    /** As above with the caller's one-shot flag (shared with another fallback trigger of the same hook, e.g. a fold entry). */
    static <T> AtomicBoolean wireUnion(AtomicBoolean fell, List<EntryList<T>> lists, Function<EntryList<T>, Object> keyOf, Registrar reg,
                    BiConsumer<EntryList<T>, Integer> onEntry, BiConsumer<EntryList<T>, RTrackRefusal> fanOnce) {
        for (EntryList<T> l : lists) {
            reg.register(l, keyOf.apply(l), idx -> onEntry.accept(l, idx), r -> {
                if (fell.compareAndSet(false, true)) {
                    fanOnce.accept(l, r);
                }
            });
        }
        return fell;
    }

    /**
     * The PRECISE(empty) rule (pure, for the JUnit): at the fixpoint, every hook whose one-shot flag is clear and whose entry
     * lists are all empty runs its fallback once (the flag is shared with {@link #wireUnion}'s refusal fallback: at most
     * one fallback per hook). Returns whether any hook fell back (the drain continues).
     */
    static <H> boolean emptyRule(List<H> hooks, Function<H, AtomicBoolean> fell, java.util.function.ToIntFunction<H> entries, Consumer<H> fallback) {
        boolean any = false;
        for (H h : hooks) {
            if (fell.apply(h).get()) {
                continue;
            }
            if (entries.applyAsInt(h) == 0 && fell.apply(h).compareAndSet(false, true)) {
                fallback.accept(h);
                any = true;
            }
        }
        return any;
    }

    /**
     * The delivered caller set at quiescence (for the JUnit and the dump): the union of the births' entry lists, plus the
     * path-less caller fan iff any birth's table is refused. Never removes an entry (the precise deliveries stay registered
     * after the fallback).
     */
    static <E> List<E> callerUnion(List<? extends Collection<E>> entriesPerBirth, List<Boolean> refusedPerBirth, Collection<E> m3bFan) {
        Set<E> out = new LinkedHashSet<>();
        boolean fell = false;
        for (int i = 0; i < entriesPerBirth.size(); i++) {
            out.addAll(entriesPerBirth.get(i));
            fell |= refusedPerBirth.get(i);
        }
        if (fell) {
            out.addAll(m3bFan);
        }
        return new ArrayList<>(out);
    }

    /**
     * The allow-list of the pending-slot audit: the audited pending read slot kinds, the 9
     * {@code VarHandle*$FieldStaticReadOnly.base} kinds (the same computer as {@code staticBase}) and
     * {@code DynamicHubCompanion.jfrEventConfiguration} (argued at its entry): 38 in all, keyed as the census key
     * ({@code "field H.n"} / {@code "static H.n"}). Each is tagged A (contents-indexed: the value's referents are in the
     * analysis heap snapshot, or SVM-internal metadata whose readers only test membership / re-materialise analysed frame
     * values) or B (raw-memory kinds: they do hold C's hub or instances, read only by raw-memory decoders; the accepted
     * raw-memory residual, which reaches user code only through StackWalker with RETAIN_CLASS_REFERENCE +
     * SHOW_HIDDEN_FRAMES, SecurityManager.getClassContext, Reflection.getCallerClass and
     * Instrumentation.getAllLoadedClasses: exactly the APIs premise G1-G4 checks). A pending kind not on the list that
     * may hold C's Class or a C instance fails the guard closed (PENDING_SLOT).
     */
    static final java.util.Map<String, String> PENDING_ALLOW;

    /** The pending kind of a {@code --enable-monitoring=jfr} image. */
    static final String JFR_EVENT_CONFIGURATION = "field com.oracle.svm.core.hub.DynamicHubCompanion.jfrEventConfiguration";

    static {
        java.util.Map<String, String> m = new java.util.LinkedHashMap<>();
        m.put("field java.lang.invoke.DirectMethodHandle$StaticAccessor.staticBase", "A: SUBSTITUTED; static-fields base, the statics inside are indexed one by one");
        m.put("field java.lang.invoke.VarHandleReferences$FieldStaticReadOnly.base",
                        "A: SUBSTITUTED (VarHandleSupport VarHandleStaticBaseComputer, as staticBase); the static-fields base array (byte[] for primitives), also at run time (MethodHandleNatives.staticFieldBase substitution); the statics inside are indexed one by one");
        m.put("field java.lang.invoke.VarHandleBooleans$FieldStaticReadOnly.base",
                        "A: SUBSTITUTED (VarHandleSupport VarHandleStaticBaseComputer, as staticBase); the static-fields base array (byte[] for primitives), also at run time (MethodHandleNatives.staticFieldBase substitution); the statics inside are indexed one by one");
        m.put("field java.lang.invoke.VarHandleBytes$FieldStaticReadOnly.base",
                        "A: SUBSTITUTED (VarHandleSupport VarHandleStaticBaseComputer, as staticBase); the static-fields base array (byte[] for primitives), also at run time (MethodHandleNatives.staticFieldBase substitution); the statics inside are indexed one by one");
        m.put("field java.lang.invoke.VarHandleChars$FieldStaticReadOnly.base",
                        "A: SUBSTITUTED (VarHandleSupport VarHandleStaticBaseComputer, as staticBase); the static-fields base array (byte[] for primitives), also at run time (MethodHandleNatives.staticFieldBase substitution); the statics inside are indexed one by one");
        m.put("field java.lang.invoke.VarHandleDoubles$FieldStaticReadOnly.base",
                        "A: SUBSTITUTED (VarHandleSupport VarHandleStaticBaseComputer, as staticBase); the static-fields base array (byte[] for primitives), also at run time (MethodHandleNatives.staticFieldBase substitution); the statics inside are indexed one by one");
        m.put("field java.lang.invoke.VarHandleFloats$FieldStaticReadOnly.base",
                        "A: SUBSTITUTED (VarHandleSupport VarHandleStaticBaseComputer, as staticBase); the static-fields base array (byte[] for primitives), also at run time (MethodHandleNatives.staticFieldBase substitution); the statics inside are indexed one by one");
        m.put("field java.lang.invoke.VarHandleInts$FieldStaticReadOnly.base",
                        "A: SUBSTITUTED (VarHandleSupport VarHandleStaticBaseComputer, as staticBase); the static-fields base array (byte[] for primitives), also at run time (MethodHandleNatives.staticFieldBase substitution); the statics inside are indexed one by one");
        m.put("field java.lang.invoke.VarHandleLongs$FieldStaticReadOnly.base",
                        "A: SUBSTITUTED (VarHandleSupport VarHandleStaticBaseComputer, as staticBase); the static-fields base array (byte[] for primitives), also at run time (MethodHandleNatives.staticFieldBase substitution); the statics inside are indexed one by one");
        m.put("field java.lang.invoke.VarHandleShorts$FieldStaticReadOnly.base",
                        "A: SUBSTITUTED (VarHandleSupport VarHandleStaticBaseComputer, as staticBase); the static-fields base array (byte[] for primitives), also at run time (MethodHandleNatives.staticFieldBase substitution); the statics inside are indexed one by one");
        m.put("field java.lang.ClassLoader.packages", "A: SUBSTITUTED; rescanned Package map, Package not user-subclassable");
        m.put("field java.lang.ClassValue.values", "A: SUBSTITUTED; rescanned on every non-null value, keys never handed out");
        m.put("field java.lang.ThreadGroup.groups", "A: SUBSTITUTED; ThreadGroups each reachable through an indexed slot");
        m.put("static java.lang.invoke.MethodHandleImpl.ARRAYS", "A: pending static; filtered to reachable MHs");
        m.put("static javax.crypto.JceSecurity.verificationResults", "A: pending static; filtered copy, rescanned");
        m.put("static sun.security.jca.Providers.providerList", "A: pending static; rescanned ProviderList");
        m.put("field com.oracle.svm.core.jdk.RuntimeModuleSupport.bootLayer", "A: rescanned runtime boot layer");
        m.put("field java.lang.invoke.ClassSpecializer.cache", "A: filtered to reachable SpeciesData");
        m.put("field java.lang.invoke.ClassSpecializer$SpeciesData.transformHelpers", "A: filtered to reachable MHs");
        m.put("field com.oracle.svm.core.threadlocal.VMThreadLocalInfos.infos", "A: SVM-internal thread-local metadata, raw readers");
        m.put("field com.oracle.svm.core.code.ImageCodeInfo.objectConstants", "A: frame-state constants; deopt re-materialises analysed values");
        m.put("field com.oracle.svm.core.jni.access.JNIAccessibleMember.hidingSubclasses", "A: membership-only reader");
        // Pending only because JfrEventFeature's transformer is unavailable until the hosted universe is built.
        // Soundness rests on host-side identity stability, not on a sealed heap (the scanner is sealed only after
        // compilation, NativeImageGenerator.verifyAndSealShadowHeap): the value JfrEventFeature.beforeCompilation writes
        // is the object JfrEventSubstitution.initEventClass rescanned, because JfrJavaEvents.EVENT_CLASSES is filled only
        // there (registerEventClass) and the host value never changes once set (MetadataRepository.register calls
        // makeConfiguration, the only host JVM.setConfiguration caller, only when none exists; unregister only flips a
        // flag). Writer set pinned by ObjectIdentityTest.jfrEventConfigurationWriters. A JDK cone containing
        // EventConfiguration (the slot then holds a C instance) is closed by the pending-snapshot rule, not by this row:
        // the Object-typed slot sets pendingUnknownType, so a heap-birth atom refuses HEAP_SNAPSHOT_PENDING.
        m.put(JFR_EVENT_CONFIGURATION, "A: rescanned EventConfiguration (JDK final record), the only value: build time = the hosted JVM.getConfiguration(eventClass), " +
                        "rescanned during analysis (JfrEventSubstitution.initEventClass) and identity-stable on the host afterwards (set once by makeConfiguration); " +
                        "run time = SubstrateJVM.setConfiguration (typed EventConfiguration, analysed allocations); never a Class, hub or companion " +
                        "(JDK cones containing EventConfiguration: HEAP_SNAPSHOT_PENDING under the strict pending-snapshot rule)");
        m.put("field com.oracle.svm.core.code.ImageCodeInfo.classes", "B: raw-memory residual: frame decoder (StackWalker, getClassContext, getCallerClass)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.firstReadOnlyRegularObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.firstReadOnlyRelocatableObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.firstWritablePatchedObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.firstWritableRegularObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.firstWritableHugeObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.firstReadOnlyHugeObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.firstObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.lastReadOnlyRegularObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.lastReadOnlyRelocatableObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.lastWritablePatchedObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.lastWritableRegularObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.lastWritableHugeObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.lastReadOnlyHugeObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo.lastObject", "B: raw-memory residual: heap walker (Instrumentation.getAllLoadedClasses)");
        PENDING_ALLOW = java.util.Collections.unmodifiableMap(m);
    }

    /**
     * The named-class verdict of every PENDING_ALLOW kind (same 38 keys; the A/B tag above stays). The lambda audit
     * closed some rows with "not a lambda type"; a named cone class can be a user subclass of a JDK type, so each row is
     * re-argued: HOLDS (the slot cannot hand a named cone Class / instance to user code) or HOLDS-WITH-CONDITION (it holds
     * under the named premise). Every condition names its premise: G1-N / G2 / G3 / G4 / G5-N (the image premise), M-1
     * (the reverse navigation index), "contents indexed" (the slot's referents are in the snapshot index) or
     * "membership-only" (the reader only tests membership).
     */
    static final java.util.Map<String, String> PENDING_NAMED;

    static {
        java.util.Map<String, String> m = new java.util.LinkedHashMap<>();
        String base = "HOLDS: contents indexed (the static-fields base array; the statics inside are indexed one by one; raw base+offset = the Unsafe residual)";
        m.put("field java.lang.invoke.DirectMethodHandle$StaticAccessor.staticBase", base);
        for (String k : new String[]{"References", "Booleans", "Bytes", "Chars", "Doubles", "Floats", "Ints", "Longs", "Shorts"}) {
            m.put("field java.lang.invoke.VarHandle" + k + "$FieldStaticReadOnly.base", base);
        }
        m.put("field java.lang.ClassLoader.packages", "HOLDS: contents indexed (rescanned Package map; Package is not subclassable; packageInfo is an interface, never a cone member)");
        m.put("field java.lang.ClassValue.values",
                        "HOLDS-WITH-CONDITION: contents indexed (values rescanned: cone instances are heap births, Class values are holders); keys are never handed out");
        m.put("field java.lang.ThreadGroup.groups",
                        "HOLDS-WITH-CONDITION: contents indexed (changed argument: a user ThreadGroup subclass can be a cone; every element is also reachable through another indexed slot, HostedJavaThreadsFeature, sealed after analysis, so it is an indexed heap birth; not VM_REENTRY)");
        m.put("static java.lang.invoke.MethodHandleImpl.ARRAYS", "HOLDS: contents indexed (MethodHandle is not user-subclassable; captured values are reached through the MH's indexed fields)");
        m.put("static javax.crypto.JceSecurity.verificationResults",
                        "HOLDS: contents indexed (keys are WeakReference<Provider>: a Reference cone is VM_REENTRY; a user Provider instance is indexed through the rescanned map)");
        m.put("static sun.security.jca.Providers.providerList", "HOLDS: contents indexed (changed argument: a user Provider subclass can be a cone; the ProviderList is rescanned and indexed)");
        m.put("field com.oracle.svm.core.jdk.RuntimeModuleSupport.bootLayer", "HOLDS: contents indexed (rescanned; any Class inside is a CLASS_HOLDER hit, fail closed; ClassLoader.classes is Reset)");
        m.put("field java.lang.invoke.ClassSpecializer.cache",
                        "HOLDS: contents indexed (JDK-internal SpeciesData; its Class refs are species / primitive / Object classes, Object never forms a cone: Q-STR)");
        m.put("field java.lang.invoke.ClassSpecializer$SpeciesData.transformHelpers",
                        "HOLDS: contents indexed (MethodHandle is not user-subclassable; captured values are reached through the MH's indexed fields)");
        m.put("field com.oracle.svm.core.threadlocal.VMThreadLocalInfos.infos",
                        "HOLDS: G4 raw-memory readers only (VMThreadLocalInfo.valueClass is read only at build time, LoadVMThreadLocalNode; the run-time readers are raw thread-local / GC code)");
        m.put("field com.oracle.svm.core.code.ImageCodeInfo.objectConstants",
                        "HOLDS-WITH-CONDITION: contents indexed (deopt re-materialises IR constants the analysis saw: heap births / CLASS_CONSTANT; JDWP excluded)");
        m.put("field com.oracle.svm.core.jni.access.JNIAccessibleMember.hidingSubclasses", "HOLDS-WITH-CONDITION: membership-only reader (contains)");
        m.put(JFR_EVENT_CONFIGURATION, "HOLDS: contents indexed (the build-time EventConfiguration is rescanned during analysis, so a user SettingControl / any Class reachable " +
                        "inside is an indexed heap birth / CLASS_HOLDER hit; run-time values are analysed allocations; no API hands out a companion)");
        m.put("field com.oracle.svm.core.code.ImageCodeInfo.classes",
                        "HOLDS-WITH-CONDITION: the frame decoder hands Classes out only via G1-N (StackWalker RETAIN, use-based), G2 (getClassContext), G3 (application getCallerClass) and G5-N (Reflection.getCallerClass in a CSM called by a cone method); a CSM in a hidden nestmate of T (lookupClass().getNestHost()) is closed by M-1 (the reverse navigation index)");
        String heap = "HOLDS-WITH-CONDITION: G4 (the heap walker reaches Java only through Instrumentation.getAllLoadedClasses; JFR is internal)";
        for (String k : new String[]{"firstReadOnlyRegularObject", "firstReadOnlyRelocatableObject", "firstWritablePatchedObject", "firstWritableRegularObject", "firstWritableHugeObject",
                        "firstReadOnlyHugeObject", "firstObject", "lastReadOnlyRegularObject", "lastReadOnlyRelocatableObject", "lastWritablePatchedObject", "lastWritableRegularObject",
                        "lastWritableHugeObject", "lastReadOnlyHugeObject", "lastObject"}) {
            m.put("field com.oracle.svm.core.genscavenge.ImageHeapInfo." + k, heap);
        }
        PENDING_NAMED = java.util.Collections.unmodifiableMap(m);
    }

    /** The premise names a named verdict's condition must cite (one at least). */
    static final java.util.List<String> NAMED_PREMISES = java.util.List.of("G1-N", "G2", "G3", "G4", "G5-N", "M-1", "contents indexed", "membership-only");

    /** The allow-list tag of a pending slot kind (null = not on the list: fail closed). */
    static String pendingAllow(String where) {
        return where == null ? null : PENDING_ALLOW.get(where);
    }

    /** Whether a pending slot kind blocks a class: it may hold C's Class or a C instance and is not on the allow-list. */
    static boolean pendingSlotBlocks(boolean mayHoldClass, boolean mayHoldInstance, String where) {
        return (mayHoldClass || mayHoldInstance) && pendingAllow(where) == null;
    }

    // The per-image conditional premise.

    /** G1-G4: any image-level exposure of a lambda class's Class object = no lambda qualifies in this image. */
    static boolean premiseFails(int swHidden, int classCtx, int gccNonJdk, int instr) {
        return swHidden != 0 || classCtx != 0 || gccNonJdk != 0 || instr != 0;
    }

    /** The census verdict: FAIL (G1-G4), PASS-WITH-FLAGS (only G5 disqualifies some lambdas), PASS. */
    static String premiseVerdict(int swHidden, int classCtx, int gccNonJdk, int instr, int lambdaCsm) {
        if (premiseFails(swHidden, classCtx, gccNonJdk, instr)) {
            return "FAIL";
        }
        return lambdaCsm > 0 ? "PASS-WITH-FLAGS" : "PASS";
    }

    /**
     * G3's "not application code": a class defined by the boot or platform loader (the JDK) or by the image builder's
     * own loader ({@code builder}: SVM's run-time classes and substitutions). Everything else is application code.
     */
    static boolean isRuntimeClass(Class<?> c, ClassLoader builder) {
        ClassLoader l = c.getClassLoader();
        return l == null || l == ClassLoader.getPlatformClassLoader() || l == builder;
    }

    /**
     * G1: a method of the stack walker itself (its nest, or a substitution class nest whose {@code @TargetClass} is
     * {@code StackWalker}): it reads SHOW_HIDDEN_FRAMES only to test a walker's options, never to configure one.
     */
    static boolean isWalkerFamily(Class<?> c) {
        if (c == null) {
            return false;
        }
        Class<?> host = c.getNestHost();
        if (host == StackWalker.class) {
            return true;
        }
        com.oracle.svm.core.annotate.TargetClass tc = host.getAnnotation(com.oracle.svm.core.annotate.TargetClass.class);
        return tc != null && tc.value() == StackWalker.class;
    }

    /** G1 (b): whether a build-time StackWalker shows hidden frames (an unreadable walker answers true: fail closed). */
    static boolean showsHiddenFrames(StackWalker w) {
        try {
            Set<?> opts = com.oracle.svm.util.ReflectionUtil.readField(StackWalker.class, "options", w);
            return opts == null || opts.contains(StackWalker.Option.SHOW_HIDDEN_FRAMES);
        } catch (Throwable t) {
            return true;
        }
    }

    /** G4: the first instantiated proper subtype of {@code iface} (an Instrumentation implementation), or null. */
    static AnalysisType firstInstantiated(AnalysisType iface) {
        for (AnalysisType s : iface.getAllSubtypes()) {
            if (!s.equals(iface) && s.isInstantiated()) {
                return s;
            }
        }
        return null;
    }

    /** The JVMCI handles of the APIs the premise names (host view: the constant pools of the wrapped methods). */
    static final class PremiseApis {
        final ResolvedJavaType stackFrame;
        final ResolvedJavaType stackWalker;
        final ResolvedJavaType option;
        final ResolvedJavaType reflection;
        final ResolvedJavaType stackTraceUtils;
        final ResolvedJavaType instrumentation;
        /** G1 (c): the walker-construction APIs and the constant option-set factories. */
        final ResolvedJavaType liveStackFrame;
        final ResolvedJavaType enumSet;
        final ResolvedJavaType set;

        PremiseApis(MetaAccessProvider host) {
            this.liveStackFrame = lookupOptional(host, "java.lang.LiveStackFrame");
            this.enumSet = host.lookupJavaType(java.util.EnumSet.class);
            this.set = host.lookupJavaType(Set.class);
            this.stackFrame = host.lookupJavaType(StackWalker.StackFrame.class);
            this.stackWalker = host.lookupJavaType(StackWalker.class);
            this.option = host.lookupJavaType(StackWalker.Option.class);
            this.reflection = host.lookupJavaType(jdk.internal.reflect.Reflection.class);
            this.stackTraceUtils = host.lookupJavaType(com.oracle.svm.core.jdk.StackTraceUtils.class);
            this.instrumentation = host.lookupJavaType(java.lang.instrument.Instrumentation.class);
        }

        /** G2: {@code SecurityManager.getClassContext} or the SVM frame visitor behind it. */
        static boolean isClassContext(Class<?> declaring, String name) {
            return (declaring == SecurityManager.class || declaring == com.oracle.svm.core.jdk.StackTraceUtils.class) && "getClassContext".equals(name);
        }

        /** G1 (a): an enumeration of the walker options ({@code Option.values()} / {@code valueOf}). */
        static boolean isOptionEnumeration(Class<?> declaring, String name) {
            return declaring == StackWalker.Option.class && ("values".equals(name) || "valueOf".equals(name));
        }

        private static ResolvedJavaType lookupOptional(MetaAccessProvider host, String name) {
            try {
                return host.lookupJavaType(Class.forName(name, false, null));
            } catch (Throwable t) {
                return null;
            }
        }

        /**
         * G1 (c): a stack-walker factory, i.e. a static method of {@code StackWalker} or {@code LiveStackFrame} that
         * returns a {@code StackWalker} (the public {@code getInstance} overloads, the package-private
         * {@code newInstance} family, {@code LiveStackFrame.getStackWalker*}).
         */
        boolean isWalkerFactory(ResolvedJavaMethod t) {
            if (!t.isStatic()) {
                return false;
            }
            ResolvedJavaType h = t.getDeclaringClass();
            return (h.equals(stackWalker) || h.equals(liveStackFrame)) && t.getSignature().getReturnType(null).getName().equals(stackWalker.getName());
        }

        /** The factory's shape for the constant-option recognition (null = not a public getInstance overload). */
        String getInstanceShape(ResolvedJavaMethod t) {
            if (!t.getDeclaringClass().equals(stackWalker) || !"getInstance".equals(t.getName())) {
                return null;
            }
            jdk.vm.ci.meta.Signature sig = t.getSignature();
            int n = sig.getParameterCount(false);
            if (n == 0) {
                return "";
            }
            String p0 = sig.getParameterType(0, null).getName();
            if (n == 1 && p0.equals(option.getName())) {
                return "O";
            }
            if (n == 1 && p0.equals(set.getName())) {
                return "S";
            }
            if (n == 2 && p0.equals(set.getName()) && sig.getParameterKind(1) == JavaKind.Int) {
                return "SI";
            }
            return null;
        }

        /**
         * G1 (c): the arity of a constant option-set factory call ({@code EnumSet.of(E..)} / {@code Set.of(..)} with fixed
         * arity, no varargs array), or -1.
         */
        int constantSetArity(ResolvedJavaMethod t) {
            if (!t.isStatic() || !"of".equals(t.getName()) || !(t.getDeclaringClass().equals(enumSet) || t.getDeclaringClass().equals(set))) {
                return -1;
            }
            jdk.vm.ci.meta.Signature sig = t.getSignature();
            int n = sig.getParameterCount(false);
            for (int i = 0; i < n; i++) {
                if (sig.getParameterType(i, null).getName().startsWith("[")) {
                    return -1; // the varargs overload: the elements come from an array
                }
            }
            return n;
        }

        /**
         * A {@code StackWalker} constructor (private; reached only through the factories, unless reflection / JNI
         * registers it or a synthesised factory method calls it).
         */
        boolean isWalkerConstructor(ResolvedJavaMethod t) {
            return t.isConstructor() && t.getDeclaringClass().equals(stackWalker);
        }

        /**
         * The argument index of the first {@code java.util.Set} parameter of a walker factory (the option set),
         * -1 for a factory without one ({@code getInstance()}, {@code getInstance(Option)}), -2 for a non-factory.
         */
        int setParamIndex(ResolvedJavaMethod t) {
            if (!isWalkerFactory(t)) {
                return -2;
            }
            jdk.vm.ci.meta.Signature sig = t.getSignature();
            for (int i = 0; i < sig.getParameterCount(false); i++) {
                if (sig.getParameterType(i, null).getName().equals(set.getName())) {
                    return i;
                }
            }
            return -1;
        }

        boolean isCallerClass(ResolvedJavaType holder, String name) {
            return (holder.equals(reflection) || holder.equals(stackTraceUtils)) && "getCallerClass".equals(name);
        }
    }

    /** What one method's bytecode uses (the premise's per-method facts). */
    static final class BytecodeUses {
        /** G1 (a): reads {@code StackWalker.Option.SHOW_HIDDEN_FRAMES} or loads the {@code Option} class constant. */
        boolean showHidden;
        /** G3: invokes {@code Reflection.getCallerClass} / {@code StackTraceUtils.getCallerClass} directly. */
        boolean callerClass;
        /** G5: invokes a {@code @CallerSensitive} method directly. */
        boolean callerSensitive;
        /** The body (or an invoked method) cannot be read or resolved: the caller fails closed. */
        boolean unreadable;
        /** The first reason of {@link #unreadable} (census). */
        String why;
        /**
         * G1 (c): constructs a stack walker whose option set is not provably a constant set without {@code SHOW_HIDDEN_FRAMES} (keyed on the construction, not on how the option value is named).
         */
        boolean walkerBuild;
        /** The first reason of {@link #walkerBuild} (census). */
        String walkerWhy;
        /**
         * G1 (c): the bcis of the walker constructions proven constant. An analysis invoke of a walker factory is
         * accepted only at one of these positions (G1 d: a build-time intrinsified method handle, a body without
         * bytecode or an inlined call positioned elsewhere fails closed).
         */
        final Set<Integer> provenWalkerBcis = new java.util.HashSet<>();
        /**
         * The walker constructions not proven locally, each {@code {bci, the single resolved factory (null when the
         * call resolves to several methods)}}, in bytecode order (the derived-factory rule's candidate pending sites).
         */
        final List<Object[]> unprovenWalkerSites = new ArrayList<>();

        void walker(String why) {
            walkerBuild = true;
            walkerWhy = walkerWhy != null ? walkerWhy : why;
        }
    }

    /** G1 (c) tokens of the constant-option window (what one instruction pushed). */
    private static final int W_OTHER = 0;
    private static final int W_OPT = 1;
    private static final int W_SET = 2;
    private static final int W_INT = 3;

    /** Every bci that is a branch or switch target or an exception handler start. */
    static Set<Integer> jumpTargets(byte[] code, ResolvedJavaMethod w) {
        Set<Integer> out = new java.util.HashSet<>();
        BytecodeStream s = new BytecodeStream(code);
        while (s.currentBC() != Bytecodes.END) {
            int bc = s.currentBC();
            if (Bytecodes.isBranch(bc)) {
                out.add(s.readBranchDest());
            } else if (bc == Bytecodes.TABLESWITCH || bc == Bytecodes.LOOKUPSWITCH) {
                jdk.graal.compiler.bytecode.BytecodeSwitch sw = bc == Bytecodes.TABLESWITCH ? new jdk.graal.compiler.bytecode.BytecodeTableSwitch(s, s.currentBCI())
                                : new jdk.graal.compiler.bytecode.BytecodeLookupSwitch(s, s.currentBCI());
                out.add(sw.defaultTarget());
                for (int i = 0; i < sw.numberOfCases(); i++) {
                    out.add(sw.targetAt(i));
                }
            }
            s.next();
        }
        for (jdk.vm.ci.meta.ExceptionHandler h : w.getExceptionHandlers()) {
            out.add(h.getHandlerBCI());
        }
        return out;
    }

    /**
     * G1 (c): whether the walker factory call at {@code bci} is provably a constant option set without
     * SHOW_HIDDEN_FRAMES. {@code win} holds the {bci, token, arity} of the instructions just before the call (oldest
     * first). The window must lie in one basic block: no instruction after its first, nor the call, is a jump target.
     * A {@code W_OPT} token is a {@code getstatic} of an Option constant other than SHOW_HIDDEN_FRAMES.
     */
    static boolean provenConstantOptions(String shape, List<int[]> win, int bci, Set<Integer> targets) {
        if ("".equals(shape)) {
            return true;
        }
        if (shape == null || targets.contains(bci)) {
            return false;
        }
        int i = win.size() - 1;
        if ("SI".equals(shape)) {
            if (i < 0 || win.get(i)[1] != W_INT || targets.contains(win.get(i)[0])) {
                return false;
            }
            i--;
        }
        int need;
        if ("O".equals(shape)) {
            need = 1;
        } else {
            if (i < 0 || win.get(i)[1] != W_SET) {
                return false;
            }
            need = win.get(i)[2];
            if (need > 0 && targets.contains(win.get(i)[0])) {
                return false;
            }
            i--;
        }
        for (int k = 0; k < need; k++, i--) {
            if (i < 0 || win.get(i)[1] != W_OPT) {
                return false;
            }
            if (k < need - 1 && targets.contains(win.get(i)[0])) {
                return false; // only the window's first instruction may be a jump target
            }
        }
        return true; // Set.of() (need 0): the empty set is its own first instruction
    }

    /** One pass over a method's bytecode (abstract and native methods have none). */
    static BytecodeUses bytecodeUses(ResolvedJavaMethod w, PremiseApis apis) {
        BytecodeUses u = new BytecodeUses();
        if (w.isAbstract() || w.isNative()) {
            return u;
        }
        byte[] code;
        try {
            code = w.getCode();
        } catch (Throwable t) {
            code = null;
        }
        if (code == null) {
            u.unreadable = true;
            u.why = "no-bytecode";
            return u;
        }
        ConstantPool cp = w.getConstantPool();
        BytecodeStream s = new BytecodeStream(code);
        List<int[]> win = new ArrayList<>(); // G1 (c): {bci, token, arity} of the last instructions
        Set<Integer> targets = null;
        while (s.currentBC() != Bytecodes.END) {
            int bc = s.currentBC();
            int bci = s.currentBCI();
            int tok = W_OTHER;
            int arity = 0;
            try {
                switch (bc) {
                    case Bytecodes.GETSTATIC -> {
                        JavaField f = cp.lookupField(s.readCPI(), w, bc);
                        if (f != null && sameType(f.getDeclaringClass(), apis.option, w)) {
                            if ("SHOW_HIDDEN_FRAMES".equals(f.getName())) {
                                u.showHidden = true;
                            } else {
                                tok = W_OPT;
                            }
                        }
                    }
                    case Bytecodes.ICONST_M1, Bytecodes.ICONST_0, Bytecodes.ICONST_1, Bytecodes.ICONST_2, Bytecodes.ICONST_3, Bytecodes.ICONST_4, Bytecodes.ICONST_5, Bytecodes.BIPUSH,
                                    Bytecodes.SIPUSH, Bytecodes.ILOAD, Bytecodes.ILOAD_0, Bytecodes.ILOAD_1, Bytecodes.ILOAD_2, Bytecodes.ILOAD_3 -> tok = W_INT;
                    case Bytecodes.LDC, Bytecodes.LDC_W -> {
                        Object k = cp.lookupConstant(s.readCPI());
                        if (k instanceof JavaType jt && sameType(jt, apis.option, w)) {
                            u.showHidden = true;
                        } else if (k instanceof JavaType jt && (sameType(jt, apis.reflection, w) || sameType(jt, apis.stackTraceUtils, w))) {
                            u.callerClass = true; // G3: the getCallerClass holder named (a reflective / method-handle lookup)
                        } else if (k instanceof JavaConstant jk && jk.getJavaKind() == JavaKind.Int) {
                            tok = W_INT;
                        }
                    }
                    case Bytecodes.INVOKEVIRTUAL, Bytecodes.INVOKESPECIAL, Bytecodes.INVOKESTATIC, Bytecodes.INVOKEINTERFACE -> {
                        JavaMethod jm = cp.lookupMethod(s.readCPI(), bc, w);
                        ResolvedJavaType holder = jm == null ? null : resolveHolder(jm.getDeclaringClass(), w);
                        if (jm != null && holder == null) {
                            // the holder class cannot be loaded: the call can never link (NoClassDefFoundError), so it
                            // calls no caller-sensitive method; a getCallerClass reference is still matched by its descriptor
                            u.callerClass |= "getCallerClass".equals(jm.getName()) &&
                                            (sameType(jm.getDeclaringClass(), apis.reflection, w) || sameType(jm.getDeclaringClass(), apis.stackTraceUtils, w));
                            break;
                        }
                        List<ResolvedJavaMethod> ts = jm == null ? List.of() : resolveInvoked(jm, holder);
                        if (ts.isEmpty()) {
                            u.unreadable = true;
                            u.why = u.why != null ? u.why : "unresolved:" + (jm == null ? "?" : jm.format("%H.%n"));
                        }
                        for (ResolvedJavaMethod t : ts) {
                            u.callerClass |= apis.isCallerClass(t.getDeclaringClass(), t.getName());
                            u.callerSensitive |= isCallerSensitive(t);
                            int n = apis.constantSetArity(t);
                            if (n >= 0 && ts.size() == 1) {
                                boolean allOpt = win.size() >= n;
                                for (int k = 1; k <= n && allOpt; k++) {
                                    allOpt = win.get(win.size() - k)[1] == W_OPT;
                                }
                                if (allOpt) {
                                    tok = W_SET;
                                    arity = n;
                                }
                            }
                            if (apis.isWalkerFactory(t)) {
                                // G1 (c): a walker construction; only a provably constant option set without
                                // SHOW_HIDDEN_FRAMES is exempt
                                String shape = ts.size() == 1 ? apis.getInstanceShape(t) : null;
                                if (targets == null && shape != null && !shape.isEmpty()) {
                                    targets = jumpTargets(code, w);
                                }
                                if (provenConstantOptions(shape, win, bci, targets != null ? targets : Set.of())) {
                                    u.provenWalkerBcis.add(bci);
                                } else {
                                    u.walker(t.format("%H.%n(%p)") + "@" + bci);
                                    u.unprovenWalkerSites.add(new Object[]{bci, ts.size() == 1 ? t : null});
                                }
                            }
                        }
                    }
                    default -> {
                    }
                }
            } catch (Throwable t) {
                u.unreadable = true;
                u.why = u.why != null ? u.why : "bci" + s.currentBCI() + ":" + t.getClass().getSimpleName();
            }
            win.add(new int[]{bci, tok, arity});
            if (win.size() > 8) {
                win.remove(0);
            }
            s.next();
        }
        return u;
    }

    private static boolean sameType(JavaType t, ResolvedJavaType target, ResolvedJavaMethod accessing) {
        if (t instanceof ResolvedJavaType rt) {
            return rt.equals(target);
        }
        return t != null && t.getName().equals(target.getName()); // an unresolved reference: compared by descriptor
    }

    /** The holder type of a referenced member, or null when the class cannot be loaded. */
    private static ResolvedJavaType resolveHolder(JavaType ht, ResolvedJavaMethod accessing) {
        if (ht instanceof ResolvedJavaType r) {
            return r;
        }
        try {
            return ht.resolve(accessing.getDeclaringClass());
        } catch (Throwable t) {
            return null; // NoClassDefFoundError (an optional dependency absent from the class path)
        }
    }

    /**
     * The methods an invoke may link to: the resolved method, else every method of that name in the holder, its
     * superclasses and all its superinterfaces (a superset: a signature-polymorphic {@code MethodHandle.invokeExact} has
     * no method of the call's exact descriptor); for {@code <init>} the holder's constructors. Empty = unresolvable (the
     * caller fails closed).
     */
    private static List<ResolvedJavaMethod> resolveInvoked(JavaMethod jm, ResolvedJavaType holder) {
        if (jm instanceof ResolvedJavaMethod rm) {
            return List.of(rm);
        }
        List<ResolvedJavaMethod> out = new ArrayList<>();
        if ("<init>".equals(jm.getName())) {
            if (holder != null) {
                out.addAll(Arrays.asList(holder.getDeclaredConstructors(false))); // a constructor is not inherited
            }
            return out;
        }
        ArrayDeque<ResolvedJavaType> work = new ArrayDeque<>();
        Set<ResolvedJavaType> seen = new java.util.HashSet<>();
        if (holder != null) {
            work.add(holder);
        }
        while (!work.isEmpty()) {
            ResolvedJavaType t = work.poll();
            if (t == null || !seen.add(t)) {
                continue;
            }
            for (ResolvedJavaMethod m : t.getDeclaredMethods(false)) {
                if (m.getName().equals(jm.getName())) {
                    out.add(m);
                }
            }
            if (t.getSuperclass() != null) {
                work.add(t.getSuperclass());
            }
            work.addAll(Arrays.asList(t.getInterfaces()));
        }
        return out;
    }

    /** Whether {@code m} carries {@code @jdk.internal.reflect.CallerSensitive} (HotSpot's own flag; other views fail closed). */
    static boolean isCallerSensitive(ResolvedJavaMethod m) {
        if (m instanceof HotSpotResolvedJavaMethod h) {
            return h.isCallerSensitive();
        }
        return true;
    }

    // The G1 derived-factory rule. A walker factory call whose option set is not a locally proven constant is a pending
    // site; it passes iff the set argument is proven, across pure forwarding parameters and every caller, to be a
    // constant set without the forbidden option that never escapes before the factory's defensive copy. Bytecode facts
    // only (host JVMCI, as bytecodeUses); the callers come from the analysis invoke flows. Fail closed everywhere else.

    /** Bound of the upward proof and the downward purity closure (a bound, not a knob). */
    static final int FWD_DEPTH = 8;
    /** At most this many caller sites per forwarder (a bound, not a knob). */
    static final int FWD_FANCAP = 16;

    /** G1's forbidden option (G1-N will pass RETAIN_CLASS_REFERENCE too: the mask is kept per origin). */
    static final int FWD_FORBIDDEN = 1 << StackWalker.Option.SHOW_HIDDEN_FRAMES.ordinal();

    /** A symbolic operand-stack value of the per-method simulation. */
    record FwdVal(int kind, int x) {
        static final int OTHER = 0;
        /** The unmodified incoming declared parameter {@code x} (0-based, receiver excluded). */
        static final int PARAM = 1;
        /** A constant option set, {@code x} = the bitset of the option ordinals. */
        static final int CONST = 2;
        /** A {@code getstatic} of an Option constant other than SHOW_HIDDEN_FRAMES, {@code x} = its ordinal. */
        static final int OPT = 3;
        static final FwdVal ANY = new FwdVal(OTHER, 0);

        @Override
        public String toString() {
            return switch (kind) {
                case PARAM -> "PARAM(" + x + ")";
                case CONST -> "CONST" + optionNames(x);
                case OPT -> "OPT(" + x + ")";
                default -> "OTHER";
            };
        }
    }

    /** The option names of a bitset (census). */
    static String optionNames(int mask) {
        StringBuilder sb = new StringBuilder("{");
        for (StackWalker.Option o : StackWalker.Option.values()) {
            if ((mask & (1 << o.ordinal())) != 0) {
                sb.append(sb.length() > 1 ? "," : "").append(o.name());
            }
        }
        return sb.append('}').toString();
    }

    /** The forwarding facts of one method's bytecode. */
    static final class FwdFacts {
        /** No bytecode, abstract / native, or a read error: no PARAM is pure and no argument has an origin. */
        boolean unreadable;
        String why;
        final int params;
        /** Per declared parameter: a reference parameter. */
        final boolean[] reference;
        /** Per declared parameter: the slot is written, or a load of it reaches anything but an invoke argument. */
        final boolean[] escaped;
        /** Per declared parameter: the {bci, argument index} of each invoke argument it is passed as. */
        final List<List<int[]>> uses = new ArrayList<>();
        /** Per invoke bci: the single resolved target (absent = unresolved or several). */
        final java.util.Map<Integer, ResolvedJavaMethod> target = new java.util.HashMap<>();
        /** Per invoke bci: the origins of the declared arguments. */
        final java.util.Map<Integer, FwdVal[]> args = new java.util.HashMap<>();
        /** The invokes bound in the bytecode ({@code invokestatic} / {@code invokespecial}). */
        final Set<Integer> bound = new java.util.HashSet<>();

        FwdFacts(int params) {
            this.params = params;
            this.reference = new boolean[params];
            this.escaped = new boolean[params];
            for (int i = 0; i < params; i++) {
                uses.add(new ArrayList<>());
            }
        }

        /** The origin of argument {@code i} of the invoke at {@code bci} (OTHER when unknown). */
        FwdVal arg(int bci, int i) {
            FwdVal[] a = args.get(bci);
            return unreadable || a == null || i < 0 || i >= a.length ? FwdVal.ANY : a[i];
        }

        /** Whether parameter {@code k} is only ever passed on as invoke arguments (the local part of purity). */
        boolean localPure(int k) {
            return !unreadable && k >= 0 && k < params && reference[k] && !escaped[k];
        }
    }

    /** One pass over {@code w}'s bytecode with a symbolic operand stack reset at every basic-block start. */
    static FwdFacts forwardFacts(ResolvedJavaMethod w, PremiseApis apis) {
        jdk.vm.ci.meta.Signature sig = w.getSignature();
        int n = sig.getParameterCount(false);
        FwdFacts f = new FwdFacts(n);
        int[] slotOf = new int[n];
        int slot = w.isStatic() ? 0 : 1;
        for (int k = 0; k < n; k++) {
            JavaKind kind = sig.getParameterKind(k);
            f.reference[k] = kind == JavaKind.Object;
            slotOf[k] = slot;
            slot += kind.needsTwoSlots() ? 2 : 1;
        }
        byte[] code = null;
        try {
            code = w.isAbstract() || w.isNative() ? null : w.getCode();
        } catch (Throwable t) {
            code = null;
        }
        if (code == null) {
            f.unreadable = true;
            f.why = w.isAbstract() || w.isNative() ? "abstract-or-native" : "no-bytecode";
            return f;
        }
        try {
            simulate(w, code, apis, f, slotOf);
        } catch (Throwable t) {
            f.unreadable = true;
            f.why = "error:" + t.getClass().getSimpleName();
        }
        return f;
    }

    private static int paramOfSlot(int[] slotOf, int idx) {
        for (int k = 0; k < slotOf.length; k++) {
            if (slotOf[k] == idx) {
                return k;
            }
        }
        return -1;
    }

    private static void simulate(ResolvedJavaMethod w, byte[] code, PremiseApis apis, FwdFacts f, int[] slotOf) {
        ConstantPool cp = w.getConstantPool();
        // pre-pass: the written local slots (a written parameter slot is not the incoming argument)
        Set<Integer> written = new java.util.HashSet<>();
        BytecodeStream s = new BytecodeStream(code);
        while (s.currentBC() != Bytecodes.END) {
            int bc = s.currentBC();
            if (Bytecodes.isStore(bc) || bc == Bytecodes.IINC) {
                int idx = storeIndex(s, bc);
                written.add(idx);
                if (bc == Bytecodes.LSTORE || bc == Bytecodes.DSTORE || (bc >= Bytecodes.LSTORE_0 && bc <= Bytecodes.LSTORE_3) || (bc >= Bytecodes.DSTORE_0 && bc <= Bytecodes.DSTORE_3)) {
                    written.add(idx + 1); // a two-slot value also overwrites the next slot
                }
            }
            s.next();
        }
        for (int k = 0; k < slotOf.length; k++) {
            if (written.contains(slotOf[k])) {
                f.escaped[k] = true;
            }
        }
        Set<Integer> targets = jumpTargets(code, w);
        ArrayDeque<FwdVal> stack = new ArrayDeque<>();
        s = new BytecodeStream(code);
        while (s.currentBC() != Bytecodes.END) {
            int bc = s.currentBC();
            int bci = s.currentBCI();
            if (targets.contains(bci)) {
                flush(stack, f); // a basic-block start: a value live across the boundary escapes
            }
            switch (bc) {
                case Bytecodes.ALOAD, Bytecodes.ALOAD_0, Bytecodes.ALOAD_1, Bytecodes.ALOAD_2, Bytecodes.ALOAD_3 -> {
                    int k = paramOfSlot(slotOf, bc == Bytecodes.ALOAD ? s.readLocalIndex() : bc - Bytecodes.ALOAD_0);
                    stack.push(k >= 0 && f.reference[k] && !written.contains(slotOf[k]) ? new FwdVal(FwdVal.PARAM, k) : FwdVal.ANY);
                }
                case Bytecodes.ILOAD, Bytecodes.ILOAD_0, Bytecodes.ILOAD_1, Bytecodes.ILOAD_2, Bytecodes.ILOAD_3, Bytecodes.LLOAD, Bytecodes.LLOAD_0, Bytecodes.LLOAD_1,
                                Bytecodes.LLOAD_2, Bytecodes.LLOAD_3, Bytecodes.FLOAD, Bytecodes.FLOAD_0, Bytecodes.FLOAD_1, Bytecodes.FLOAD_2, Bytecodes.FLOAD_3, Bytecodes.DLOAD,
                                Bytecodes.DLOAD_0, Bytecodes.DLOAD_1, Bytecodes.DLOAD_2, Bytecodes.DLOAD_3, Bytecodes.ACONST_NULL, Bytecodes.ICONST_M1, Bytecodes.ICONST_0,
                                Bytecodes.ICONST_1, Bytecodes.ICONST_2, Bytecodes.ICONST_3, Bytecodes.ICONST_4, Bytecodes.ICONST_5, Bytecodes.LCONST_0, Bytecodes.LCONST_1,
                                Bytecodes.FCONST_0, Bytecodes.FCONST_1, Bytecodes.FCONST_2, Bytecodes.DCONST_0, Bytecodes.DCONST_1, Bytecodes.BIPUSH, Bytecodes.SIPUSH,
                                Bytecodes.LDC, Bytecodes.LDC_W, Bytecodes.LDC2_W ->
                    stack.push(FwdVal.ANY); // one value (the stack counts values, not slots)
                case Bytecodes.GETSTATIC -> {
                    JavaField fl = cp.lookupField(s.readCPI(), w, bc);
                    int ord = fl != null && sameType(fl.getDeclaringClass(), apis.option, w) ? optionOrdinal(fl.getName()) : -1;
                    stack.push(ord >= 0 && ord != StackWalker.Option.SHOW_HIDDEN_FRAMES.ordinal() ? new FwdVal(FwdVal.OPT, ord) : FwdVal.ANY);
                }
                case Bytecodes.GETFIELD -> {
                    consume(stack, f);
                    stack.push(FwdVal.ANY);
                }
                case Bytecodes.CHECKCAST -> {
                    // identity (a javac generic bridge forwards through a cast)
                }
                case Bytecodes.POP -> consume(stack, f);
                case Bytecodes.IADD, Bytecodes.LADD, Bytecodes.FADD, Bytecodes.DADD, Bytecodes.ISUB, Bytecodes.LSUB, Bytecodes.FSUB, Bytecodes.DSUB, Bytecodes.IMUL, Bytecodes.LMUL,
                                Bytecodes.FMUL, Bytecodes.DMUL, Bytecodes.IDIV, Bytecodes.LDIV, Bytecodes.FDIV, Bytecodes.DDIV, Bytecodes.IREM, Bytecodes.LREM, Bytecodes.FREM,
                                Bytecodes.DREM, Bytecodes.ISHL, Bytecodes.LSHL, Bytecodes.ISHR, Bytecodes.LSHR, Bytecodes.IUSHR, Bytecodes.LUSHR, Bytecodes.IAND, Bytecodes.LAND,
                                Bytecodes.IOR, Bytecodes.LOR, Bytecodes.IXOR, Bytecodes.LXOR, Bytecodes.LCMP, Bytecodes.FCMPL, Bytecodes.FCMPG, Bytecodes.DCMPL, Bytecodes.DCMPG -> {
                    consume(stack, f); // primitive arithmetic: two values in, one out
                    consume(stack, f);
                    stack.push(FwdVal.ANY);
                }
                case Bytecodes.INEG, Bytecodes.LNEG, Bytecodes.FNEG, Bytecodes.DNEG, Bytecodes.I2L, Bytecodes.I2F, Bytecodes.I2D, Bytecodes.L2I, Bytecodes.L2F, Bytecodes.L2D,
                                Bytecodes.F2I, Bytecodes.F2L, Bytecodes.F2D, Bytecodes.D2I, Bytecodes.D2L, Bytecodes.D2F, Bytecodes.I2B, Bytecodes.I2C, Bytecodes.I2S,
                                Bytecodes.ARRAYLENGTH, Bytecodes.INSTANCEOF -> {
                    consume(stack, f); // one value in, one out
                    stack.push(FwdVal.ANY);
                }
                case Bytecodes.NOP, Bytecodes.IINC -> {
                    // no operand-stack effect
                }
                case Bytecodes.INVOKESTATIC, Bytecodes.INVOKESPECIAL, Bytecodes.INVOKEVIRTUAL, Bytecodes.INVOKEINTERFACE -> invoke(w, cp, s, bc, bci, apis, f, stack);
                default -> flush(stack, f); // unmodelled (stores, dup, swap, returns, branches, ...): every tracked value escapes
            }
            s.next();
        }
        flush(stack, f);
    }

    private static int storeIndex(BytecodeStream s, int bc) {
        return switch (bc) {
            case Bytecodes.ISTORE_0, Bytecodes.LSTORE_0, Bytecodes.FSTORE_0, Bytecodes.DSTORE_0, Bytecodes.ASTORE_0 -> 0;
            case Bytecodes.ISTORE_1, Bytecodes.LSTORE_1, Bytecodes.FSTORE_1, Bytecodes.DSTORE_1, Bytecodes.ASTORE_1 -> 1;
            case Bytecodes.ISTORE_2, Bytecodes.LSTORE_2, Bytecodes.FSTORE_2, Bytecodes.DSTORE_2, Bytecodes.ASTORE_2 -> 2;
            case Bytecodes.ISTORE_3, Bytecodes.LSTORE_3, Bytecodes.FSTORE_3, Bytecodes.DSTORE_3, Bytecodes.ASTORE_3 -> 3;
            default -> s.readLocalIndex();
        };
    }

    private static int optionOrdinal(String name) {
        for (StackWalker.Option o : StackWalker.Option.values()) {
            if (o.name().equals(name)) {
                return o.ordinal();
            }
        }
        return -1;
    }

    /** A value consumed by something other than an invoke argument: a PARAM escapes. */
    private static void consume(ArrayDeque<FwdVal> stack, FwdFacts f) {
        FwdVal v = stack.isEmpty() ? FwdVal.ANY : stack.pop();
        if (v.kind() == FwdVal.PARAM) {
            f.escaped[v.x()] = true;
        }
    }

    private static void flush(ArrayDeque<FwdVal> stack, FwdFacts f) {
        while (!stack.isEmpty()) {
            consume(stack, f);
        }
    }

    private static void invoke(ResolvedJavaMethod w, ConstantPool cp, BytecodeStream s, int bc, int bci, PremiseApis apis, FwdFacts f, ArrayDeque<FwdVal> stack) {
        JavaMethod jm = cp.lookupMethod(s.readCPI(), bc, w);
        jdk.vm.ci.meta.Signature sig = jm.getSignature();
        int n = sig.getParameterCount(false);
        FwdVal[] a = new FwdVal[n];
        for (int i = n - 1; i >= 0; i--) {
            a[i] = stack.isEmpty() ? FwdVal.ANY : stack.pop();
        }
        if (bc != Bytecodes.INVOKESTATIC) {
            consume(stack, f); // the receiver (a set used as a receiver: add / addAll / ... = an escape)
        }
        ResolvedJavaType holder = resolveHolder(jm.getDeclaringClass(), w);
        List<ResolvedJavaMethod> ts = holder == null ? List.of() : resolveInvoked(jm, holder);
        ResolvedJavaMethod t = ts.size() == 1 ? ts.get(0) : null;
        if (t != null) {
            f.target.put(bci, t);
        }
        if (bc == Bytecodes.INVOKESTATIC || bc == Bytecodes.INVOKESPECIAL) {
            f.bound.add(bci);
        }
        f.args.put(bci, a);
        boolean allOpt = true;
        int mask = 0;
        for (int i = 0; i < n; i++) {
            if (a[i].kind() == FwdVal.PARAM) {
                if (t == null) {
                    f.escaped[a[i].x()] = true; // an unresolved callee: unknown use
                } else {
                    f.uses.get(a[i].x()).add(new int[]{bci, i});
                }
            }
            allOpt &= a[i].kind() == FwdVal.OPT;
            mask |= a[i].kind() == FwdVal.OPT ? 1 << a[i].x() : 0;
        }
        if (sig.getReturnKind() != JavaKind.Void) {
            stack.push(t != null && allOpt && apis.constantSetArity(t) == n ? new FwdVal(FwdVal.CONST, mask) : FwdVal.ANY);
        }
    }

    /** The methods {@code m} overrides or implements (a superset by name and descriptor; none for static / private / constructors). */
    static List<ResolvedJavaMethod> overridden(ResolvedJavaMethod m) {
        List<ResolvedJavaMethod> out = new ArrayList<>();
        if (m.isStatic() || m.isPrivate() || m.isConstructor()) {
            return out;
        }
        String desc = m.getSignature().toMethodDescriptor();
        ArrayDeque<ResolvedJavaType> work = new ArrayDeque<>();
        Set<ResolvedJavaType> seen = new java.util.HashSet<>();
        ResolvedJavaType d = m.getDeclaringClass();
        if (d.getSuperclass() != null) {
            work.add(d.getSuperclass());
        }
        work.addAll(Arrays.asList(d.getInterfaces()));
        while (!work.isEmpty()) {
            ResolvedJavaType t = work.poll();
            if (t == null || !seen.add(t)) {
                continue;
            }
            for (ResolvedJavaMethod c : t.getDeclaredMethods(false)) {
                if (!c.isStatic() && !c.isPrivate() && c.getName().equals(m.getName()) && c.getSignature().toMethodDescriptor().equals(desc)) {
                    out.add(c);
                }
            }
            if (t.getSuperclass() != null) {
                work.add(t.getSuperclass());
            }
            work.addAll(Arrays.asList(t.getInterfaces()));
        }
        return out;
    }

    /** A caller site: the position method (null = unpositioned) and the bci of an analysis invoke flow. */
    record FwdSite(ResolvedJavaMethod method, int bci) {
    }

    /**
     * The inverse of the analysis invoke flows: per callee, per declared target, and the callees per (position, declared
     * target). Host methods throughout (the bytecode facts' view). Positions
     * are outermost, so the flows of a body inlined at {@code (m, bci)} share that position with the bytecode invoke; the
     * callees of the bytecode invoke are only those of the flows whose declared target it may dispatch to.
     */
    static final class FwdIndex {
        private record Call(FwdSite at, ResolvedJavaMethod declared) {
        }

        final java.util.Map<ResolvedJavaMethod, Set<FwdSite>> byCallee = new java.util.HashMap<>();
        final java.util.Map<ResolvedJavaMethod, Set<FwdSite>> byDeclared = new java.util.HashMap<>();
        private final java.util.Map<FwdSite, java.util.Map<ResolvedJavaMethod, Set<ResolvedJavaMethod>>> calleesAt = new java.util.HashMap<>();
        /** Flows whose callees are unavailable. */
        private final Set<Call> unknownAt = new java.util.HashSet<>();

        /** One analysis invoke flow: its declared target, its position, its callees (null = unavailable). */
        void add(ResolvedJavaMethod declared, ResolvedJavaMethod pm, int bci, Collection<ResolvedJavaMethod> callees) {
            FwdSite at = new FwdSite(pm, bci);
            byDeclared.computeIfAbsent(declared, k -> new java.util.LinkedHashSet<>()).add(at);
            Set<ResolvedJavaMethod> cs = calleesAt.computeIfAbsent(at, k -> new java.util.LinkedHashMap<>()).computeIfAbsent(declared, k -> new java.util.LinkedHashSet<>());
            if (callees != null) {
                for (ResolvedJavaMethod h : callees) {
                    cs.add(h);
                    byCallee.computeIfAbsent(h, k -> new java.util.LinkedHashSet<>()).add(at);
                }
            } else {
                unknownAt.add(new Call(at, declared));
            }
        }

        /** The callers of {@code m}: its callee flows, the flows declaring it, and (CHA superset) those declaring a method it overrides. */
        Collection<FwdSite> callers(ResolvedJavaMethod m) {
            Set<FwdSite> out = new java.util.LinkedHashSet<>(byCallee.getOrDefault(m, Set.of()));
            out.addAll(byDeclared.getOrDefault(m, Set.of()));
            for (ResolvedJavaMethod t : overridden(m)) {
                out.addAll(byDeclared.getOrDefault(t, Set.of())); // the CHA superset (only adds callers)
            }
            return out;
        }

        /**
         * The callees of the flows at {@code (m, bci)} whose declared target {@code t} may dispatch to (equal, or an
         * override of {@code t}); null = no such flow (the bytecode invoke was inlined or folded) or one with unknown callees.
         */
        Collection<ResolvedJavaMethod> calleesAt(ResolvedJavaMethod m, int bci, ResolvedJavaMethod t) {
            FwdSite at = new FwdSite(m, bci);
            java.util.Map<ResolvedJavaMethod, Set<ResolvedJavaMethod>> byT = calleesAt.get(at);
            if (byT == null || t == null) {
                return null;
            }
            Set<ResolvedJavaMethod> out = null;
            for (java.util.Map.Entry<ResolvedJavaMethod, Set<ResolvedJavaMethod>> e : byT.entrySet()) {
                ResolvedJavaMethod d = e.getKey();
                if (d.equals(t) || overridden(d).contains(t)) {
                    if (unknownAt.contains(new Call(at, d))) {
                        return null;
                    }
                    out = out == null ? new java.util.LinkedHashSet<>() : out;
                    out.addAll(e.getValue());
                }
            }
            return out;
        }
    }

    /** What the derivation needs from the image (a synthetic world in JUnit). */
    interface FwdWorld {
        /** The forwarding facts of {@code m} (memoised by the implementation). */
        FwdFacts facts(ResolvedJavaMethod m);

        /** Every analysis invoke site that may dispatch to {@code m} (callees, declared target, CHA superset). */
        Collection<FwdSite> callers(ResolvedJavaMethod m);

        /** {@code m} or a method it overrides is a reflection / JNI / method-handle root. */
        boolean root(ResolvedJavaMethod m);

        /**
         * The possible callees of the bytecode invoke at {@code (m, bci)} whose declared target is {@code t}: only the
         * analysis flows positioned there whose declared target {@code t} may dispatch to (not the flows of a
         * body inlined at that position); null = no such flow / unavailable.
         */
        Collection<ResolvedJavaMethod> calleesAt(ResolvedJavaMethod m, int bci, ResolvedJavaMethod t);

        /** -2 not a walker factory, -1 a factory without an option-set parameter, else its argument index. */
        int factorySetParam(ResolvedJavaMethod t);

        /** Whether a call whose declared target is {@code t} may dispatch to {@code m}. */
        default boolean dispatchesTo(ResolvedJavaMethod t, ResolvedJavaMethod m) {
            return t.equals(m) || overridden(m).contains(t);
        }
    }

    /** The verdict of one argument proof: {@code reason} null = proven. */
    record FwdVerdict(String reason, String chain, int depth) {
        boolean ok() {
            return reason == null;
        }
    }

    /**
     * The derivation of one image (memo per (method, bci, argument) and per (forwarder, parameter)), keyed by the method
     * object, not its printable name (a bridge and its target, or overloads with same-simple-name parameter types, print
     * alike).
     */
    static final class FwdProver {
        private record ArgKey(ResolvedJavaMethod m, int bci, int i) {
        }

        record PureKey(ResolvedJavaMethod m, int k) {
        }

        /** The impurity reason prefix of a virtual invoke without callee information (fails closed). */
        static final String NO_CALLEES = "no-callees@";

        final FwdWorld world;
        private final java.util.Map<ArgKey, FwdVerdict> memo = new java.util.HashMap<>();
        /** Per (forwarder, parameter): null-free; "" = pure, else the impurity reason. */
        private final java.util.Map<PureKey, String> pure = new java.util.HashMap<>();

        FwdProver(FwdWorld world) {
            this.world = world;
        }

        /** The pending site {@code (m, bci)} (a walker factory call): its option-set argument. */
        FwdVerdict provePending(ResolvedJavaMethod m, int bci) {
            FwdFacts f = world.facts(m);
            ResolvedJavaMethod t = f.target.get(bci);
            int iw = t == null ? -2 : world.factorySetParam(t);
            if (iw < 0) {
                return new FwdVerdict("fwd:not-a-set-factory@" + name(m) + "@" + bci, name(m) + "@" + bci, 0);
            }
            return proveArg(m, bci, iw, 0, new LinkedHashSet<>());
        }

        /** Whether argument {@code i} of the invoke at {@code (m, bci)} is a proven constant option set. */
        FwdVerdict proveArg(ResolvedJavaMethod m, int bci, int i, int d, Set<ResolvedJavaMethod> path) {
            ArgKey key = new ArgKey(m, bci, i);
            FwdVerdict memoised = memo.get(key);
            if (memoised != null) {
                return memoised;
            }
            FwdVerdict v = prove(m, bci, i, d, path);
            memo.put(key, v);
            return v;
        }

        private FwdVerdict prove(ResolvedJavaMethod m, int bci, int i, int d, Set<ResolvedJavaMethod> path) {
            String here = name(m) + "@" + bci;
            FwdFacts f = world.facts(m);
            if (f.unreadable) {
                return new FwdVerdict("fwd:unreadable(" + f.why + ")@" + here, here, d);
            }
            FwdVal v = f.arg(bci, i);
            if (v.kind() == FwdVal.CONST) {
                return (v.x() & FWD_FORBIDDEN) == 0 ? new FwdVerdict(null, here + " CONST" + optionNames(v.x()), d) : new FwdVerdict("fwd:forbidden@" + here, here, d);
            }
            if (v.kind() != FwdVal.PARAM) {
                return new FwdVerdict("fwd:non-constant@" + here, here, d);
            }
            int k = v.x();
            String impure = impurity(m, k, 0, new java.util.HashSet<>());
            if (impure != null) {
                return new FwdVerdict(impure.startsWith(NO_CALLEES) ? "fwd:" + impure : "fwd:impure-param@" + here, here, d);
            }
            if (world.root(m)) {
                return new FwdVerdict("fwd:root@" + here, here, d);
            }
            if (d + 1 > FWD_DEPTH) {
                return new FwdVerdict("fwd:depth@" + here, here, d);
            }
            if (!path.add(m)) {
                return new FwdVerdict("fwd:cycle@" + here, here, d);
            }
            try {
                Collection<FwdSite> callers = world.callers(m);
                if (callers == null || callers.isEmpty()) {
                    return new FwdVerdict("fwd:unknown-caller@" + here, here, d);
                }
                if (callers.size() > FWD_FANCAP) {
                    return new FwdVerdict("fwd:fan@" + here, here, d);
                }
                StringBuilder chain = new StringBuilder(here).append(" <= ");
                int depth = d;
                boolean many = callers.size() > 1;
                chain.append(many ? "[" : "");
                int n = 0;
                for (FwdSite c : callers) {
                    String at = c.method() == null ? "?@" + c.bci() : name(c.method()) + "@" + c.bci();
                    ResolvedJavaMethod t = c.method() == null ? null : world.facts(c.method()).target.get(c.bci());
                    if (t == null || !world.dispatchesTo(t, m)) {
                        return new FwdVerdict("fwd:position@" + at, here, d);
                    }
                    FwdVerdict up = proveArg(c.method(), c.bci(), k, d + 1, path);
                    if (!up.ok()) {
                        return new FwdVerdict(up.reason(), here + " <= " + up.chain(), up.depth());
                    }
                    chain.append(n++ > 0 ? " | " : "").append(up.chain());
                    depth = Math.max(depth, up.depth());
                }
                return new FwdVerdict(null, chain.append(many ? "]" : "").toString(), depth);
            } finally {
                path.remove(m);
            }
        }

        /** {@code m} is a pure forwarder on its parameter {@code k} (downward closure, bounded, cycles impure). */
        boolean isPure(ResolvedJavaMethod m, int k, int d, Set<PureKey> visiting) {
            return impurity(m, k, d, visiting) == null;
        }

        /** Null = pure; else the reason ({@link #NO_CALLEES}{@code <method>@<bci>}, or "impure"). */
        String impurity(ResolvedJavaMethod m, int k, int d, Set<PureKey> visiting) {
            PureKey key = new PureKey(m, k);
            String known = pure.get(key);
            if (known != null) {
                return known.isEmpty() ? null : known;
            }
            if (d > FWD_DEPTH || !visiting.add(key)) {
                return "impure"; // not memoised: depends on the path
            }
            String why = pureNow(m, k, d, visiting);
            visiting.remove(key);
            if (why == null || d == 0) {
                pure.put(key, why == null ? "" : why);
            }
            return why;
        }

        private String pureNow(ResolvedJavaMethod m, int k, int d, Set<PureKey> visiting) {
            FwdFacts f = world.facts(m);
            if (!f.localPure(k)) {
                return "impure";
            }
            for (int[] u : f.uses.get(k)) {
                ResolvedJavaMethod t = f.target.get(u[0]);
                if (t == null) {
                    return "impure";
                }
                int iw = world.factorySetParam(t);
                if (iw != -2) {
                    if (iw != u[1]) {
                        return "impure"; // a factory's non-set argument (an Option parameter: the local rule)
                    }
                    continue;
                }
                Collection<ResolvedJavaMethod> callees = world.calleesAt(m, u[0], t);
                if (callees == null && f.bound.contains(u[0])) {
                    callees = List.of(t); // a bound invoke with no flow of its own (inlined / folded): its bytecode target
                }
                if (callees == null) {
                    return NO_CALLEES + name(m) + "@" + u[0]; // a virtual invoke without callee information: fail closed
                }
                for (ResolvedJavaMethod c : callees) {
                    if (!world.dispatchesTo(t, c)) {
                        return "impure";
                    }
                    String why = impurity(c, u[1], d + 1, visiting);
                    if (why != null) {
                        return why;
                    }
                }
            }
            return null;
        }

        static String name(ResolvedJavaMethod m) {
            return m == null ? "?" : m.format("%H.%n(%p)");
        }
    }
}
