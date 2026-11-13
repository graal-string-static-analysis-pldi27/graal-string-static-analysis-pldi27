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
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentSkipListSet;
import java.util.function.Function;

import com.oracle.graal.pointsto.heap.ImageHeapConstant;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.svm.core.SubstrateOptions;
import com.oracle.svm.core.util.VMError;
import com.oracle.svm.hosted.image.NativeImageHeap;
import com.oracle.svm.hosted.meta.HostedField;

import jdk.graal.compiler.core.common.type.CompressibleConstant;
import jdk.vm.ci.meta.JavaConstant;

/**
 * The two build-time checks behind the direct-call soundness argument. A rep is any strict subclass of
 * {@code java.lang.String}. The builder JDK's String is {@code public non-sealed class String}, so any class compiled
 * against it could extend it; the only subclasses the project has are the rep classes of
 * {@code com.oracle.svm.core.stringrep} (pinned by JUnit tests that scan that package and the svm class files for
 * String subclasses). Treating every String subclass as a rep is the safe reading: the heap check fails the build for
 * a foreign subclass in the heap too, and the reachability check reports its type.
 * <ul>
 * <li><b>The heap check</b> ({@link #checkImageHeap}): no rep object is in the image heap, except the instances of a
 * rep class's own static pool ({@link #POOL_FIELDS}: exactly {@code SingleByteString.POOL}). Reps come only from the
 * replacement factories at run time; a rep in the heap would reach every flow that loads it, and no tracked flow starts
 * there. The pool ({@code SingleByteString}'s build-time {@code <clinit>} fills it with 256 instances) is safe because
 * it is private and read only by the SBS factories ({@code create(byte)}, {@code create(char)},
 * {@code createFromSubstring}, {@code createFromChar}), which run only at replaced (tracked) sites; so a pool instance
 * enters the program only as the result of a replaced site, like a freshly allocated rep. The check follows every
 * recorded reference: a pool instance must be referenced only by the pool array, and the pool array only by that
 * static field and by compiled code (the folded load of the static final field). Any other reference fails the
 * build.</li>
 * <li><b>The reachability check</b> ({@link #recordChildRepTypes}): no rep type is reachable in the analysis child. The
 * child analyses the rep-free program (it replaces nothing), so its type states are the rep-free world's. REACHABLE
 * means no direct-call lists.</li>
 * </ul>
 */
public final class RepTypeChecks {

    private RepTypeChecks() {
    }

    /** A strict subclass of {@code java.lang.String}. */
    static boolean isRepClass(Class<?> c) {
        return c != null && c != String.class && String.class.isAssignableFrom(c);
    }

    /** A rep class or an array (of any dimension) of one: the heap objects whose references the heap check records. */
    public static boolean isRepOrRepArrayClass(Class<?> c) {
        Class<?> e = c;
        while (e != null && e.isArray()) {
            e = e.getComponentType();
        }
        return isRepClass(e);
    }

    /**
     * The class-initializer simulation parity rule: while the replacement is active, a {@code SimulateClassInitializer}
     * run that would allocate a rep instance (or array) is aborted, so the class initializes at run time, which is how
     * the analysis child models every {@code <clinit>}. Otherwise the simulation would publish the rep as an image-heap
     * constant (failing the heap check). Hook: {@code SimulateClassInitializerGraphDecoder#abortIfRepAllocation}. Active
     * iff the replacement plugin is installed.
     */
    public static boolean clinitSimulationParityActive() {
        return SubstrateOptions.StringAnalysis.getValue() || SubstrateOptions.StringRepProfile.getValue() != null || RepresentationProfileHolder.hasProfile();
    }

    /** The simulations aborted by the parity rule, as {@code <class>(<allocated rep type>)}; printed with the heap check. */
    private static final ConcurrentSkipListSet<String> CLINIT_SIM_REP_ABORTS = new ConcurrentSkipListSet<>();

    /** Record one aborted simulation. */
    public static void recordClinitSimulationRepAbort(String clinitClass, String repType) {
        CLINIT_SIM_REP_ABORTS.add(clinitClass + "(" + repType + ")");
    }

    /** The census line printed next to the heap check's (only while the rule is active). */
    static void printClinitSimulationRepAborts() {
        if (clinitSimulationParityActive()) {
            System.out.println("[string-analysis-dc] clinitsim-repaborts=" + CLINIT_SIM_REP_ABORTS.size() + (CLINIT_SIM_REP_ABORTS.isEmpty() ? "" : " " + CLINIT_SIM_REP_ABORTS));
        }
    }

    /**
     * The heap check's allowed pools, pinned by {@code RepHeapPoolTest}: rep class name -> its private static final array
     * field holding its own instances. SingleByteString is the only rep with a pool.
     */
    static final Map<String, String> POOL_FIELDS = Map.of("com.oracle.svm.core.stringrep.SingleByteString", "POOL");

    /** The kind of one reference to a heap object (a reason it was added to the heap with). */
    public enum RefKind {
        /** A field or array element of another heap object ({@link Ref#referrer}). */
        OBJECT,
        /** A static field ({@link Ref#name}: {@code declaringClass.field}). */
        STATIC_FIELD,
        /** A constant embedded in compiled code or in the data section. */
        CODE,
        /** Anything else (interned-strings table, resources, layered-image roots, ...): never allowed. */
        OTHER
    }

    /** One recorded reference to a rep object or rep array. */
    public record Ref(RefKind kind, Object referrer, String name) {
        public static Ref object(Object referrer) {
            return new Ref(RefKind.OBJECT, referrer, null);
        }

        public static Ref staticField(String qualifiedName) {
            return new Ref(RefKind.STATIC_FIELD, null, qualifiedName);
        }

        public static Ref code(String what) {
            return new Ref(RefKind.CODE, null, what);
        }

        public static Ref other(String what) {
            return new Ref(RefKind.OTHER, null, what);
        }
    }

    /**
     * The heap check's rule for one rep object: null if it may be in the heap, else why not. It may iff its class has a pool
     * ({@link #POOL_FIELDS}), it has at least one recorded reference, and every reference is an element of that pool:
     * the heap object {@code pools} maps the pool field to (the field's value), whose own references are all that
     * static field or compiled code. {@code refs} holds the references of every rep object and rep array;
     * {@code classOf} gives an object's class.
     */
    static <K> String disallowed(K rep, Map<K, List<Ref>> refs, Function<K, Class<?>> classOf, Map<String, K> pools) {
        Class<?> repClass = classOf.apply(rep);
        String poolField = POOL_FIELDS.get(repClass.getName());
        if (poolField == null) {
            return "not a pooled rep class";
        }
        String qualifiedPool = repClass.getName() + "." + poolField;
        K pool = pools.get(qualifiedPool);
        if (pool == null) {
            return qualifiedPool + " has no value in the heap";
        }
        List<Ref> own = refs.get(rep);
        if (own == null || own.isEmpty()) {
            return "no recorded reference";
        }
        for (Ref r : own) {
            if (r.kind() != RefKind.OBJECT) {
                return "referenced by " + r.kind() + " " + r.name();
            }
            K referrer = castKey(r.referrer());
            if (!referrer.equals(pool)) {
                return "referenced by a " + classOf.apply(referrer).getTypeName() + " that is not the value of " + qualifiedPool;
            }
        }
        List<Ref> poolRefs = refs.get(pool);
        if (poolRefs == null || poolRefs.isEmpty()) {
            return "its pool array has no recorded reference";
        }
        for (Ref pr : poolRefs) {
            boolean poolFieldRef = pr.kind() == RefKind.STATIC_FIELD && qualifiedPool.equals(pr.name());
            if (!poolFieldRef && pr.kind() != RefKind.CODE) {
                return "its pool array is referenced by " + pr.kind() + " " +
                                (pr.kind() == RefKind.OBJECT ? classOf.apply(RepTypeChecks.<K> castKey(pr.referrer())).getTypeName() : pr.name());
            }
        }
        return null;
    }

    @SuppressWarnings("unchecked")
    private static <K> K castKey(Object o) {
        return (K) o;
    }

    /** The child's reachability status: {@code "unreachable"}, {@code "REACHABLE:<types>"}, or null before the child's analysis. */
    private static volatile String childRepTypes;

    /** True iff the child recorded its status and no rep type was reachable (the direct-call precondition). */
    public static boolean childRepTypesUnreachable() {
        return "unreachable".equals(childRepTypes);
    }

    static String childRepTypesStatus() {
        return childRepTypes;
    }

    /** The reachable rep types of {@code universe}, by name. */
    static List<String> reachableRepTypes(AnalysisUniverse universe) {
        List<String> out = new ArrayList<>();
        for (AnalysisType t : universe.getTypes()) {
            if (t.isReachable() && isRepClass(t.getJavaClass())) {
                out.add(t.toJavaName(true) + (t.isInstantiated() ? "(instantiated)" : ""));
            }
        }
        out.sort(null);
        return out;
    }

    /** The reachability check, in the analysis child: record and print the status. */
    static void recordChildRepTypes(AnalysisUniverse universe) {
        List<String> reachable = reachableRepTypes(universe);
        childRepTypes = reachable.isEmpty() ? "unreachable" : "REACHABLE:" + String.join(",", reachable);
        System.out.println("[string-analysis-dc] rtypes=" + childRepTypes);
    }

    /**
     * The heap check: fail the build if a rep object is in the image heap, other than a pool instance allowed by {@link #disallowed}.
     * Prints one summary line when it passes. Returns the number of heap objects scanned.
     */
    static long checkImageHeap(NativeImageHeap heap) {
        for (Map.Entry<String, JavaConstant> e : poolFieldValues(heap).entrySet()) {
            JavaConstant pool = e.getValue();
            Integer length = heap.hConstantReflection.readArrayLength(pool);
            List<Class<?>> elements = new ArrayList<>();
            for (int i = 0; length != null && i < length; i++) {
                JavaConstant element = heap.hConstantReflection.readArrayElement(pool, i);
                elements.add(element == null || element.isNull() ? null : heap.hMetaAccess.lookupJavaType(element).getJavaClass());
            }
            String reason = poolContentViolation(e.getKey(), length == null ? null : elements);
            if (reason != null) {
                throw VMError.shouldNotReachHere("string-analysis heap check violated: " + reason);
            }
        }
        return checkImageHeap(heap.getObjects(), heap.getRepObjectRefs(), poolObjects(heap));
    }

    /**
     * The premise of the unchecked pool read ({@code SingleByteString.exactPoolEntry}): every element of the pool
     * held by {@code qualifiedPool} ({@code <rep class>.<field>}) is a non-null instance of exactly that rep class. Since
     * the pool is typed {@code String[]}, the Java type system does not guarantee it; the heap check does. {@code elements}: the
     * elements' classes (null = a null element), or null if the value is not an array. Null if the premise holds.
     */
    static String poolContentViolation(String qualifiedPool, List<Class<?>> elements) {
        String repClass = qualifiedPool.substring(0, qualifiedPool.lastIndexOf('.'));
        if (elements == null) {
            return "the value of " + qualifiedPool + " is not an array";
        }
        for (int i = 0; i < elements.size(); i++) {
            Class<?> c = elements.get(i);
            if (c == null || !c.getName().equals(repClass)) {
                return "element " + i + " of " + qualifiedPool + " is " + (c == null ? "null" : "a " + c.getTypeName()) + ", not a " + repClass +
                                " (the premise of the unchecked pool read SingleByteString.exactPoolEntry)";
            }
        }
        return null;
    }

    /** The heap object that is the value of each pool field of {@link #POOL_FIELDS}, if it is in the heap. */
    static Map<String, NativeImageHeap.ObjectInfo> poolObjects(NativeImageHeap heap) {
        Map<String, NativeImageHeap.ObjectInfo> out = new TreeMap<>();
        for (Map.Entry<String, JavaConstant> e : poolFieldValues(heap).entrySet()) {
            NativeImageHeap.ObjectInfo info = heap.getConstantInfo(e.getValue());
            if (info != null) {
                out.put(e.getKey(), info);
            }
        }
        return out;
    }

    /**
     * The heap check's recording rule (used by {@code NativeImageHeap.recordRepRef}): a heap object's references are
     * recorded iff it is a rep object or rep array, or it is the value of a pool field (by identity: the pool is typed
     * {@code String[]}, so its class does not select it). {@link #isRepOrRepArrayClass} itself is not widened: the
     * class-initializer simulation parity hook shares it.
     */
    public static boolean recordsRefsOf(Class<?> c, JavaConstant constant, Collection<JavaConstant> poolValues) {
        return isRepOrRepArrayClass(c) || poolValues.contains(constant);
    }

    /** The image-heap value of each pool field of {@link #POOL_FIELDS} (qualified field name -> constant), when non-null. */
    public static Map<String, JavaConstant> poolFieldValues(NativeImageHeap heap) {
        Map<String, JavaConstant> out = new TreeMap<>();
        for (Map.Entry<String, String> e : POOL_FIELDS.entrySet()) {
            HostedField field;
            try {
                field = heap.hMetaAccess.optionalLookupJavaField(Class.forName(e.getKey(), false, RepTypeChecks.class.getClassLoader()).getDeclaredField(e.getValue()));
            } catch (ReflectiveOperationException ex) {
                throw VMError.shouldNotReachHere("string-analysis heap check: the pool field " + e + " does not exist", ex);
            }
            if (field == null || !field.isValueAvailable()) {
                continue;
            }
            JavaConstant value = heap.hConstantReflection.readFieldValue(field, null, true);
            if (value instanceof ImageHeapConstant && value.isNonNull()) {
                out.put(e.getKey() + "." + e.getValue(), CompressibleConstant.uncompress(value));
            }
        }
        return out;
    }

    static long checkImageHeap(Collection<NativeImageHeap.ObjectInfo> objects, Map<NativeImageHeap.ObjectInfo, List<Ref>> refs, Map<String, NativeImageHeap.ObjectInfo> pools) {
        TreeMap<String, Integer> reps = new TreeMap<>();
        TreeMap<String, Integer> pooled = new TreeMap<>();
        TreeMap<String, String> why = new TreeMap<>();
        long scanned = 0;
        for (NativeImageHeap.ObjectInfo info : objects) {
            scanned++;
            Class<?> c = info.getObjectClass();
            if (isRepClass(c)) {
                String reason = disallowed(info, refs, NativeImageHeap.ObjectInfo::getObjectClass, pools);
                if (reason == null) {
                    pooled.merge(c.getName() + "." + POOL_FIELDS.get(c.getName()), 1, Integer::sum);
                } else {
                    reps.merge(c.getName(), 1, Integer::sum);
                    why.putIfAbsent(c.getName(), reason);
                }
            }
        }
        if (!reps.isEmpty()) {
            throw VMError.shouldNotReachHere("string-analysis heap check violated: the image heap holds custom string representation objects " + reps +
                            " (first reason per class: " + why + "). A rep must never be a heap constant: no tracked flow starts at a heap load" +
                            " (the only exception is a rep class's own static pool, " + POOL_FIELDS + ", referenced by nothing else).");
        }
        int poolReps = pooled.values().stream().mapToInt(Integer::intValue).sum();
        // the references of the pool arrays, by kind (audit: a static field and compiled code only)
        TreeMap<String, Integer> arrayRefs = new TreeMap<>();
        for (NativeImageHeap.ObjectInfo pool : pools.values()) {
            if (refs.containsKey(pool)) {
                for (Ref r : refs.get(pool)) {
                    arrayRefs.merge(r.kind() + (r.kind() == RefKind.STATIC_FIELD ? ":" + r.name() : ""), 1, Integer::sum);
                }
            }
        }
        System.out.println("[string-analysis-dc] heapreps=0 poolreps=" + poolReps + (pooled.isEmpty() ? "" : " " + pooled + " poolarrayrefs=" + arrayRefs) + " scanned=" + scanned);
        return scanned;
    }
}
