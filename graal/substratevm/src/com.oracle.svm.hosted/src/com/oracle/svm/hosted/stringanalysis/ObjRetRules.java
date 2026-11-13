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

import java.util.Set;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.vm.ci.meta.JavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The pure decision rules of the named-class identity caller set, pinned by {@code ObjRetNamedClassTest}. Structural only: no
 * rule reads an application class or method name (the JDK API names below are the premise's fixed API list, as in
 * {@link ObjIdRules}).
 * <ul>
 * <li>{@link #qualifies}: the class part. Q-STR first: an owner comparable with {@code String} (a supertype of String,
 * String itself or a rep) never qualifies; then a cone ({@code every instantiated concrete T ⊑ C}) must exist. The frame
 * part (static, native entry / address-taken) is checked per frame by the caller.</li>
 * <li>{@link #guard}: the cone's birth set (framed allocations plus image heap instances, at most {@link #MAX_BIRTHS})
 * is complete under the premise P-FB-N.</li>
 * <li>The observation list: the harmless uses of a query object's / a cone constant's Class object.</li>
 * </ul>
 */
final class ObjRetRules {
    private ObjRetRules() {
    }

    /** At most this many births (framed allocations + heap instances) per cone. */
    static final int MAX_BIRTHS = 16;

    /** Why a class's cone does not qualify (null = it qualifies). Checked in this order. */
    enum NoQualifyN {
        /** Q-STR: the owner is a supertype of String, String itself or a rep (every rep extends String). */
        STRING_CONE,
        /** No instantiated concrete type in the cone. */
        EMPTY_CONE,
        /** The class or its subtypes cannot be read (fail closed). */
        UNREADABLE
    }

    /** The frame part (per frame, before the class query). */
    enum FrameNoQualify {
        STATIC,
        /** A native entry or an address-taken method keeps refusing eagerly (never qualifies). */
        NATIVE_OR_ADDRESS
    }

    /**
     * Why a qualifying cone's birth set is not usable (null = the guard passes), checked in this order. NEST_EXPOSED and
     * CONE_ARRAY go beyond the premise's clauses (fail closed): a nested class's Class object reaches its enclosing class
     * / nest host ({@code getDeclaringClass}, {@code getEnclosingClass}, {@code getNestHost}: kept for every hub), and an
     * array of a cone type reaches the cone type ({@code getComponentType()}); neither route is a query atom's
     * {@code getClass()}.
     */
    enum GuardFailN {
        /** The image premise: G1-N (use-based), G2 CLASSCTX, G3 GCC_NONJDK or G4 INSTR fails. */
        PREMISE,
        /** P-FB-N (f): a cone member is a Reference, a Thread or a Throwable (the VM re-enters such instances). */
        VM_REENTRY,
        /** The birth index failed (as in {@link ObjIdRules}). */
        INDEX_FAILED,
        /** No birth at all (framed or heap). */
        NO_BIRTH,
        /** More than {@link #MAX_BIRTHS} births. */
        TOO_MANY_BIRTHS,
        /** An instantiated cone member with no framed or heap birth (reflection, JNI, Unsafe, a feature, serialization). */
        NO_MEMBER_BIRTH,
        /** A reachable method declared by an exposed type has no frame. */
        UNFRAMED_METHOD,
        /** A reachable unframed method allocates or loads (ldc) an exposed type. */
        UNFRAMED_BIRTH,
        /** A framed birth no walk can start from (as in {@link ObjIdRules}). */
        UNWALKABLE_BIRTH,
        /** A reachable nested class's Class object leads to a cone member (an addition beyond the premise's clauses, fail closed). */
        NEST_EXPOSED,
        /** A reachable array type of an exposed type (an addition beyond the premise's clauses, fail closed). */
        CONE_ARRAY,
        /** G5-N: a method declared by an exposed type calls a {@code @CallerSensitive} method directly. */
        CONE_CSM,
        /** P-FB-N (b): a framed Class constant of an exposed type (or an array of it) with a use outside the observation list. */
        CLASS_CONSTANT,
        /** P-FB-N (d): an image-heap slot holds an exposed type's Class object. */
        CLASS_HOLDER,
        /** P-FB-N (c): an exposed type (or its nest host / enclosing class / a sealed supertype) is registered. */
        REGISTERED,
        /** P-FB-N (c''): an exposed type appears in the reflection metadata of a registered element. */
        METADATA_TYPE,
        /** P-FB-N (d'): a pending heap slot kind not on the allow-list may hold a Class object or a cone instance. */
        PENDING_SLOT
    }

    /**
     * Q-STR: {@code c} is comparable with String (a supertype such as {@code Object}, {@code CharSequence},
     * {@code Comparable}, ..., String itself or a rep). Such a cone is never a query: a candidate string or a rep is never
     * a query object.
     */
    static boolean stringCone(ResolvedJavaType c, ResolvedJavaType string) {
        return c.isAssignableFrom(string) || string.isAssignableFrom(c);
    }

    static NoQualifyN qualifies(boolean stringCone, boolean emptyCone) {
        if (stringCone) {
            return NoQualifyN.STRING_CONE;
        }
        if (emptyCone) {
            return NoQualifyN.EMPTY_CONE;
        }
        return null;
    }

    static FrameNoQualify frameQualifies(boolean isStatic, boolean nativeOrAddress) {
        if (isStatic) {
            return FrameNoQualify.STATIC;
        }
        if (nativeOrAddress) {
            return FrameNoQualify.NATIVE_OR_ADDRESS;
        }
        return null;
    }

    static GuardFailN guard(boolean premiseFails, boolean vmReentry, boolean indexFailed, int births, boolean memberWithoutBirth, int unframedMethods, boolean unframedBirth,
                    boolean unwalkableBirth, boolean nestExposed, boolean coneArray, boolean csm, int harmfulConstants, int classHolders, boolean registered, boolean metadata,
                    int pendingNotAllowed) {
        if (premiseFails) {
            return GuardFailN.PREMISE;
        }
        if (vmReentry) {
            return GuardFailN.VM_REENTRY;
        }
        if (indexFailed) {
            return GuardFailN.INDEX_FAILED;
        }
        if (births == 0) {
            return GuardFailN.NO_BIRTH;
        }
        if (births > MAX_BIRTHS) {
            return GuardFailN.TOO_MANY_BIRTHS;
        }
        if (memberWithoutBirth) {
            return GuardFailN.NO_MEMBER_BIRTH;
        }
        if (unframedMethods > 0) {
            return GuardFailN.UNFRAMED_METHOD;
        }
        if (unframedBirth) {
            return GuardFailN.UNFRAMED_BIRTH;
        }
        if (unwalkableBirth) {
            return GuardFailN.UNWALKABLE_BIRTH;
        }
        if (nestExposed) {
            return GuardFailN.NEST_EXPOSED;
        }
        if (coneArray) {
            return GuardFailN.CONE_ARRAY;
        }
        if (csm) {
            return GuardFailN.CONE_CSM;
        }
        if (harmfulConstants > 0) {
            return GuardFailN.CLASS_CONSTANT;
        }
        if (classHolders > 0) {
            return GuardFailN.CLASS_HOLDER;
        }
        if (registered) {
            return GuardFailN.REGISTERED;
        }
        if (metadata) {
            return GuardFailN.METADATA_TYPE;
        }
        if (pendingNotAllowed > 0) {
            return GuardFailN.PENDING_SLOT;
        }
        return null;
    }

    /**
     * Whether a type of the subtype closure of the cone root is exposed, i.e. its Class object leads to a cone member's
     * Class: it is a cone member, it is sealed ({@code getPermittedSubclasses} goes down), or it is a class with a cone
     * member among its proper superclasses ({@code getSuperclass} goes up). An unsealed interface or an abstract class
     * with no cone member above it leads only upward to non-cone types.
     */
    static boolean exposed(boolean coneMember, boolean sealed, boolean isInterface, boolean coneMemberAbove) {
        return coneMember || sealed || (!isInterface && coneMemberAbove);
    }

    // The observation list: the harmless uses of a Class object (a query atom's getClass() / hub, a cone Class constant,
    // a StackFrame.getDeclaringClass() result for G1-N). Same method, through Pis only.

    /** Graph node kinds that only observe a Class value (identity compare, null check, type tests). */
    static final Set<String> HARMLESS_NODES = Set.of("ObjectEqualsNode", "PointerEqualsNode", "IsNullNode", "InstanceOfNode", "InstanceOfDynamicNode", "ClassIsAssignableFromNode",
                    "ClassIsArrayNode", "GetClassNode", "LoadHubNode", "LoadHubOrNullNode", "IdentityHashCodeNode");

    /** Node kinds that pass the same Class object on (followed): Pis; in SVM a hub is the Class object. */
    static final Set<String> FOLLOW_NODES = Set.of("PiNode", "ClassGetHubNode");

    /** Class methods whose receiver may be the Class (they return a String, a boolean, an int or the argument object). */
    static final Set<String> RECEIVER_OK = Set.of("getName", "getSimpleName", "getTypeName", "getCanonicalName", "getPackageName", "toString", "hashCode", "equals",
                    "isInstance", "isAssignableFrom", "cast", "isArray", "isPrimitive", "isInterface", "isEnum", "isRecord", "isHidden", "isSealed", "isAnonymousClass",
                    "isLocalClass", "isMemberClass", "isSynthetic", "isAnnotation", "getModifiers", "desiredAssertionStatus");

    /** The holders whose methods a Class receiver dispatches to (Class is final; SVM's hub substitutes Class). */
    static boolean classHolder(String holder) {
        return "java.lang.Class".equals(holder) || "com.oracle.svm.core.hub.DynamicHub".equals(holder);
    }

    /**
     * Whether a call is a harmless use of the Class value at argument {@code argIndex} (0 = receiver): a receiver of a
     * {@link #RECEIVER_OK} method of Class (or Object's identity {@code equals}/{@code hashCode}/{@code toString} on a
     * Class receiver), or the argument of {@code isAssignableFrom} / {@code equals} / {@code isInstance} on another Class
     * receiver ({@code receiverIsClass}: the call's receiver is a Class; for argument 0 the value itself). Anything
     * else (returning a Class or reflective object, any other argument position, any other holder) is not harmless.
     */
    static boolean harmlessCall(String holder, String name, int argIndex, boolean receiverIsClass) {
        boolean onClass = classHolder(holder) || ("java.lang.Object".equals(holder) && receiverIsClass && ("equals".equals(name) || "hashCode".equals(name) || "toString".equals(name)));
        if (!onClass) {
            return false;
        }
        if (argIndex == 0) {
            return RECEIVER_OK.contains(name);
        }
        // the argument of another Class's isAssignableFrom / equals / isInstance (observations); cast(x) returns x: no
        return argIndex == 1 && receiverIsClass && ("isAssignableFrom".equals(name) || "equals".equals(name) || "isInstance".equals(name));
    }

    // Unframed causes, the lookahead trigger, the navigation link kinds and the G1-N bytecode check. Not all
    // print-only: unframedCause feeds the INLINED_ONLY exception, readsStatic feeds G1-N, NavLink the navigation index.

    /**
     * Why a reachable method has no frame (UNFRAMED_METHOD / UNFRAMED_BIRTH diagnostics), first match in this order:
     * a class initializer (already run at build time / simulated / run at run time), a native method, an intrinsic, a
     * method that is only inlined (its body lives in its callers' graphs), a non-points-to method, no flows graph, a
     * stub flows graph, a frame whose IR could not be decoded, anything else.
     */
    enum UnframedCause {
        CLINIT_BUILD_TIME,
        CLINIT_SIMULATED,
        CLINIT_RUNTIME,
        NATIVE,
        INTRINSIC,
        INLINED_ONLY,
        NOT_POINTSTO,
        NO_FLOWS,
        STUB,
        NO_IR,
        OTHER
    }

    static UnframedCause unframedCause(boolean clinit, boolean initializedAtBuildTime, boolean simulated, boolean isNative, boolean intrinsic, boolean implInvoked, boolean inlined,
                    boolean pointsTo, boolean flowsCreated, boolean stub, boolean hasFrame) {
        if (clinit) {
            return initializedAtBuildTime ? UnframedCause.CLINIT_BUILD_TIME : simulated ? UnframedCause.CLINIT_SIMULATED : UnframedCause.CLINIT_RUNTIME;
        }
        if (isNative) {
            return UnframedCause.NATIVE;
        }
        if (intrinsic) {
            return UnframedCause.INTRINSIC;
        }
        if (inlined && !implInvoked) {
            return UnframedCause.INLINED_ONLY;
        }
        if (!pointsTo) {
            return UnframedCause.NOT_POINTSTO;
        }
        if (!flowsCreated) {
            return UnframedCause.NO_FLOWS;
        }
        if (stub) {
            return UnframedCause.STUB;
        }
        if (hasFrame) {
            return UnframedCause.NO_IR;
        }
        return UnframedCause.OTHER;
    }

    /**
     * Whether a teachable exception for this cause is a candidate (print-only; not implemented, the guard stays): a class
     * initializer that already ran at build time (or was simulated) never executes at run time, and everything it did
     * is in the heap snapshot (heap births, holders); an inlined-only body is walked inside its callers' frames. Every
     * other cause is code that runs without a frame.
     */
    static boolean teachableCandidate(UnframedCause c) {
        return c == UnframedCause.CLINIT_BUILD_TIME || c == UnframedCause.CLINIT_SIMULATED || c == UnframedCause.INLINED_ONLY;
    }

    /**
     * The lookahead trigger's pure-forwarder test (option (a), print-only): the value of {@code v} (an invoke's result)
     * reaches only Return nodes, through Phis, value proxies and conditionals (frame and virtual states ignored), and at
     * least one Return. These are exactly the uses the walk follows unconditionally for every atom kind
     * ({@code classifyUsage}: no Pi, whose arm test depends on the atom; no call, store or compare).
     */
    static boolean pureForwarder(jdk.graal.compiler.nodes.ValueNode v0) {
        java.util.ArrayDeque<jdk.graal.compiler.nodes.ValueNode> work = new java.util.ArrayDeque<>();
        java.util.Set<jdk.graal.compiler.graph.Node> seen = new java.util.HashSet<>();
        work.add(v0);
        boolean ret = false;
        while (!work.isEmpty()) {
            jdk.graal.compiler.nodes.ValueNode v = work.poll();
            if (!seen.add(v)) {
                continue;
            }
            for (jdk.graal.compiler.graph.Node u : v.usages()) {
                if (u instanceof jdk.graal.compiler.nodes.VirtualState) {
                    continue;
                }
                if (u instanceof jdk.graal.compiler.nodes.ReturnNode r && r.result() == v) {
                    ret = true;
                    continue;
                }
                if (u instanceof jdk.graal.compiler.nodes.PhiNode phi && phi.values().contains(v)) {
                    work.add(phi);
                    continue;
                }
                if (u instanceof jdk.graal.compiler.nodes.PiNode) {
                    return false; // a Pi is a LimitedValueProxy too, but the walk may stop at it (piArmDead: atom-dependent)
                }
                if (u instanceof jdk.graal.compiler.nodes.spi.LimitedValueProxy p && p.getOriginalNode() == v && u instanceof jdk.graal.compiler.nodes.ValueNode pv) {
                    work.add(pv);
                    continue;
                }
                if (u instanceof jdk.graal.compiler.nodes.calc.ConditionalNode c && (c.trueValue() == v || c.falseValue() == v)) {
                    work.add(c);
                    continue;
                }
                return false;
            }
        }
        return ret;
    }

    /** The lookahead's recursion bound (frames below the first forwarder; e.g. {@code Objects.toString} -> {@code valueOf}). */
    static final int LOOKAHEAD_DEPTH = 3;

    /**
     * The certain-refusal test of one path-less, unknown-context return of a frame F, from fixed facts: F's class is not
     * hidden (where the lambda identity hook could deliver) and the fan rule refuses (callers incomplete, fan over the cap,
     * an outside caller under E2), or (recursively) F's own fan reaches a certain refusal.
     */
    static boolean certainRefusal(boolean hidden, boolean incomplete, int fan, int cap, boolean outside, boolean lookaheadBelow) {
        if (hidden) {
            return false;
        }
        return incomplete || fan > cap || outside || lookaheadBelow;
    }

    /** How a Class object of type N leads to a type T (nest navigation, hidden nestmates included). */
    enum NavLink {
        /** N.getNestHost() == T (nest member, or a hidden nestmate such as a lambda class). */
        NEST_HOST,
        /** N is in T's nest (or T's host's nest): N.getNestMembers() lists T. */
        NEST_MEMBER,
        /** N.getDeclaringClass() == T (InnerClasses: also pre-Java-11 class files without NestMembers). */
        DECLARING,
        /** N.getEnclosingClass() == T (local / anonymous classes; EnclosingMethod). */
        ENCLOSING,
        /** N is T's declaring class: N.getDeclaredClasses() / getClasses() list T. */
        MEMBER_LIST,
        /** N is a sealed supertype of T: N.getPermittedSubclasses() lists T. */
        PERMITTED,
        /** N is an array of T: N.getComponentType() == T. */
        COMPONENT
    }

    /** The Class / DynamicHub navigation methods (receiver = a Class) that answer a Class (or Class[], or an executable) of a link. */
    static Set<String> navApis(NavLink l) {
        switch (l) {
            case NEST_HOST:
                return Set.of("getNestHost");
            case NEST_MEMBER:
                return Set.of("getNestMembers");
            case DECLARING:
                return Set.of("getDeclaringClass", "getEnclosingClass");
            case ENCLOSING:
                return Set.of("getEnclosingClass", "getEnclosingMethod", "getEnclosingConstructor");
            case MEMBER_LIST:
                return Set.of("getDeclaredClasses", "getClasses");
            case PERMITTED:
                return Set.of("getPermittedSubclasses");
            case COMPONENT:
                return Set.of("getComponentType", "componentType");
            default:
                throw new IllegalArgumentException(String.valueOf(l));
        }
    }

    /** Every navigation API name (the census scans the reachable calls of these on a Class / DynamicHub receiver). */
    static final Set<String> NAV_APIS = Set.of("getNestHost", "getNestMembers", "getDeclaringClass", "getEnclosingClass", "getEnclosingMethod", "getEnclosingConstructor",
                    "getDeclaredClasses", "getClasses", "getPermittedSubclasses", "getComponentType", "componentType");

    /**
     * The hub-internal holder slots of a Class object that only a navigation API reads (the use-based census):
     * {@code DynamicHubCompanion.nestHost} (getNestHost), {@code .declaringClass} (getDeclaringClass / getEnclosingClass)
     * and {@code DynamicHub.componentType} (getComponentType). Any other holder stays a CLASS_HOLDER.
     */
    static boolean navHolderSlot(String holderType, String field) {
        if ("com.oracle.svm.core.hub.DynamicHubCompanion".equals(holderType)) {
            return "nestHost".equals(field) || "declaringClass".equals(field);
        }
        return "com.oracle.svm.core.hub.DynamicHub".equals(holderType) && "componentType".equals(field);
    }

    /** The refusal names a nested query could remove (the trigger refusals): the nesting estimate. */
    static final Set<String> NESTABLE = Set.of("RETURN_FAN_CAP", "WORLD_TOP_EXIT", "CALLER_FAN_CAP", "WORLD_TOP_ENTRY");

    /**
     * G1-N construction half: whether {@code w}'s bytecode reads the static field {@code name} of {@code holder}
     * ({@code getstatic}); an unreadable body answers true (fail closed). Abstract and native methods read nothing.
     */
    static boolean readsStatic(ResolvedJavaMethod w, ResolvedJavaType holder, String name) {
        if (w.isAbstract() || w.isNative()) {
            return false;
        }
        byte[] code;
        try {
            code = w.getCode();
        } catch (Throwable t) {
            return true;
        }
        if (code == null) {
            return true;
        }
        BytecodeStream s = new BytecodeStream(code);
        jdk.vm.ci.meta.ConstantPool cp = w.getConstantPool();
        while (s.currentBC() != Bytecodes.END) {
            if (s.currentBC() == Bytecodes.GETSTATIC) {
                try {
                    JavaField f = cp.lookupField(s.readCPI(), w, Bytecodes.GETSTATIC);
                    if (f != null && name.equals(f.getName()) && f.getDeclaringClass().getName().equals(holder.getName())) {
                        return true;
                    }
                } catch (Throwable t) {
                    return true;
                }
            }
            s.next();
        }
        return false;
    }

    // The production navigation index, the class-metadata scan, the self-slot and the INLINED_ONLY exceptions. Pure
    // parts (pinned by ObjRetIdentityRulesTest).

    /** One link of the reverse navigation index: a Class object of {@code from} leads to {@code target} through {@code kind}. */
    interface NavSink<N> {
        void link(Class<?> target, N from, NavLink kind);
    }

    /**
     * The links out of one type {@code jc} (its analysis handle {@code n}; {@code lookup} maps a class to its handle, null =
     * not in the universe): hidden nestmates ({@code getNestHost} of a lambda class), pre-11 classes
     * ({@code getDeclaringClass} from InnerClasses without NestMembers), the enclosing class, the member lists, the sealed
     * supertypes and every component level of an array. A {@link LinkageError} of a hub query is stored in the hub and
     * thrown at run time (no Class object): no link. Any other exception propagates (the caller fails closed).
     */
    static <N> void navLinksOf(Class<?> jc, N n, java.util.function.Function<Class<?>, N> lookup, NavSink<N> out) {
        if (jc == null || jc.isPrimitive()) {
            return;
        }
        if (jc.isArray()) {
            for (Class<?> c = jc.getComponentType(); c != null; c = c.getComponentType()) {
                out.link(c, n, NavLink.COMPONENT);
            }
            return;
        }
        Class<?> nh = jc.getNestHost();
        if (nh != jc) {
            out.link(nh, n, NavLink.NEST_HOST);
            out.link(nh, n, NavLink.NEST_MEMBER);
        }
        Class<?>[] members;
        try {
            members = nh.getNestMembers();
        } catch (LinkageError e) {
            members = new Class<?>[0]; // SVM's encoder (getNestMembers) would fail the build on it: no metadata route
        }
        for (Class<?> mem : members) {
            if (mem != jc) {
                out.link(mem, n, NavLink.NEST_MEMBER);
            }
        }
        Class<?> dc = null;
        try {
            dc = jc.getDeclaringClass();
        } catch (LinkageError e) {
            // stored in the hub, thrown at run time: no Class
        }
        if (dc != null) {
            out.link(dc, n, NavLink.DECLARING);
            N dn = lookup.apply(dc);
            if (dn != null) {
                out.link(jc, dn, NavLink.MEMBER_LIST);
            }
        }
        try {
            Class<?> ec = jc.getEnclosingClass();
            if (ec != null && ec != dc) {
                out.link(ec, n, NavLink.ENCLOSING);
            }
        } catch (LinkageError e) {
            // as above
        }
        java.util.ArrayDeque<Class<?>> up = new java.util.ArrayDeque<>();
        up.add(jc);
        Set<Class<?>> seen = new java.util.HashSet<>();
        while (!up.isEmpty()) {
            Class<?> u = up.poll();
            if (u == null || !seen.add(u)) {
                continue;
            }
            if (u != jc && u.isSealed()) {
                N un = lookup.apply(u);
                if (un != null) {
                    out.link(jc, un, NavLink.PERMITTED);
                }
            }
            if (u.getSuperclass() != null) {
                up.add(u.getSuperclass());
            }
            up.addAll(java.util.Arrays.asList(u.getInterfaces()));
        }
    }

    /**
     * Whether a link is hub data in SVM, readable for every hub without any registration (NEST_EXPOSED): the nest host
     * ({@code companion.nestHost}), the declaring class ({@code companion.declaringClass}) and the enclosing class (the
     * enclosing-method info, encoded for every heap hub). The member lists, the nest members and the permitted
     * subclasses are encoded only under a reflection flag of the link's source class ({@link #metadataNavLink}: REGISTERED
     * via the linked registrations); COMPONENT is CONE_ARRAY.
     *
     * <p>The MEMBER_LIST link ({@code getDeclaredClasses()} / {@code getClasses()}) is not closed by the source flag
     * alone. {@code ReflectionDataBuilder.innerClasses} has two filling routes not gated by a flag on the source class:
     * (a) {@code registerAllClassesQuery} on X adds the public member classes of X's superclasses to their declaring
     * class's list, (b) the non-strict {@code registerClass(..., allowForName)} adds every registered class to its
     * enclosing class's list. Both are closed by METADATA_TYPE, whose scan adds every value of
     * {@code getReflectionInnerClasses()} (RT {@code metadataClasses}); route (b) is also REGISTERED (forName). Do not
     * narrow that scan without re-closing these routes.
     */
    static boolean hubNavLink(NavLink k) {
        return k == NavLink.NEST_HOST || k == NavLink.DECLARING || k == NavLink.ENCLOSING;
    }

    static boolean metadataNavLink(NavLink k) {
        return k == NavLink.NEST_MEMBER || k == NavLink.MEMBER_LIST || k == NavLink.PERMITTED;
    }

    /** NEST_EXPOSED over the index: the first hub-data link into an exposed type from another type, or null. */
    static <N> String nestExposed(java.util.Map<Class<?>, java.util.List<java.util.Map.Entry<N, NavLink>>> links, java.util.List<java.util.Map.Entry<Class<?>, N>> exposed) {
        for (java.util.Map.Entry<Class<?>, N> t : exposed) {
            for (java.util.Map.Entry<N, NavLink> l : links.getOrDefault(t.getKey(), java.util.List.of())) {
                if (hubNavLink(l.getValue()) && !l.getKey().equals(t.getValue())) {
                    return l.getKey() + "." + l.getValue() + "->" + t.getKey().getName();
                }
            }
        }
        return null;
    }

    /** Thrown by the metadata scan for a value it cannot read (the caller fails closed: every class METADATA_TYPE). */
    static final class UnreadableMetadata extends RuntimeException {
        private static final long serialVersionUID = 1L;

        UnreadableMetadata(String what, Throwable cause) {
            super(what, cause);
        }
    }

    /**
     * The Class values of an annotation, recursively: its type, Class / Class[] members, nested
     * annotations and annotation arrays. A member whose class is missing at build time ({@link TypeNotPresentException})
     * has no Class object in the image (SVM encodes the error); any other unreadable member throws
     * {@link UnreadableMetadata} (fail closed; adding a marker such as {@code Object.class} instead would fail open).
     */
    static void annotationClasses(java.lang.annotation.Annotation a, Set<Class<?>> out) {
        if (a == null) {
            return;
        }
        out.add(a.annotationType());
        for (java.lang.reflect.Method am : a.annotationType().getDeclaredMethods()) {
            if (am.getParameterCount() != 0 || am.isSynthetic() || java.lang.reflect.Modifier.isStatic(am.getModifiers())) {
                continue;
            }
            Class<?> rt = am.getReturnType();
            Class<?> e = rt;
            while (e.isArray()) {
                e = e.getComponentType();
            }
            if (e != Class.class && !e.isAnnotation()) {
                continue;
            }
            Object v;
            try {
                am.setAccessible(true);
                v = am.invoke(a);
            } catch (java.lang.reflect.InvocationTargetException ex) {
                if (ex.getCause() instanceof TypeNotPresentException) {
                    continue; // the class is missing at build time: no Class object at run time
                }
                throw new UnreadableMetadata(a.annotationType().getName() + "." + am.getName(), ex);
            } catch (ReflectiveOperationException | RuntimeException ex) {
                throw new UnreadableMetadata(a.annotationType().getName() + "." + am.getName(), ex);
            }
            annotationValue(v, out);
        }
    }

    private static void annotationValue(Object v, Set<Class<?>> out) {
        if (v instanceof Class<?> k) {
            out.add(k);
        } else if (v instanceof java.lang.annotation.Annotation n) {
            annotationClasses(n, out);
        } else if (v instanceof Object[] arr) {
            for (Object x : arr) {
                annotationValue(x, out);
            }
        }
    }

    /** The annotations of an annotated type, recursively (type arguments, array components, wildcard / variable bounds). */
    static void annotatedTypeClasses(java.lang.reflect.AnnotatedType t, Set<Class<?>> out, Set<Object> seen) {
        if (t == null || !seen.add(t)) {
            return;
        }
        for (java.lang.annotation.Annotation a : t.getDeclaredAnnotations()) {
            annotationClasses(a, out);
        }
        annotatedTypeClasses(t.getAnnotatedOwnerType(), out, seen);
        if (t instanceof java.lang.reflect.AnnotatedParameterizedType p) {
            for (java.lang.reflect.AnnotatedType x : p.getAnnotatedActualTypeArguments()) {
                annotatedTypeClasses(x, out, seen);
            }
        } else if (t instanceof java.lang.reflect.AnnotatedArrayType a) {
            annotatedTypeClasses(a.getAnnotatedGenericComponentType(), out, seen);
        } else if (t instanceof java.lang.reflect.AnnotatedWildcardType w) {
            for (java.lang.reflect.AnnotatedType x : w.getAnnotatedUpperBounds()) {
                annotatedTypeClasses(x, out, seen);
            }
            for (java.lang.reflect.AnnotatedType x : w.getAnnotatedLowerBounds()) {
                annotatedTypeClasses(x, out, seen);
            }
        } else if (t instanceof java.lang.reflect.AnnotatedTypeVariable v) {
            for (java.lang.reflect.AnnotatedType x : v.getAnnotatedBounds()) {
                annotatedTypeClasses(x, out, seen);
            }
        }
    }

    /**
     * The class-level metadata SVM encodes for every heap hub (NativeImageCodeCache addClassMetadata scope): the
     * class annotations (recursive) and the type annotations (super class, interfaces, type parameters).
     */
    static void classMetadataClasses(Class<?> k, Set<Class<?>> out) {
        for (java.lang.annotation.Annotation a : k.getDeclaredAnnotations()) {
            annotationClasses(a, out);
        }
        Set<Object> seen = new java.util.HashSet<>();
        annotatedTypeClasses(k.getAnnotatedSuperclass(), out, seen);
        for (java.lang.reflect.AnnotatedType x : k.getAnnotatedInterfaces()) {
            annotatedTypeClasses(x, out, seen);
        }
        for (java.lang.reflect.TypeVariable<?> v : k.getTypeParameters()) {
            for (java.lang.annotation.Annotation a : v.getDeclaredAnnotations()) {
                annotationClasses(a, out);
            }
            for (java.lang.reflect.AnnotatedType x : v.getAnnotatedBounds()) {
                annotatedTypeClasses(x, out, seen);
            }
        }
    }

    /** The executable-level metadata: parameter annotations and the type annotations of parameters, return, exceptions, receiver. */
    static void executableMetadataClasses(java.lang.reflect.Executable ex, Set<Class<?>> out) {
        for (java.lang.annotation.Annotation a : ex.getDeclaredAnnotations()) {
            annotationClasses(a, out);
        }
        for (java.lang.annotation.Annotation[] ps : ex.getParameterAnnotations()) {
            for (java.lang.annotation.Annotation a : ps) {
                annotationClasses(a, out);
            }
        }
        Set<Object> seen = new java.util.HashSet<>();
        for (java.lang.reflect.AnnotatedType x : ex.getAnnotatedParameterTypes()) {
            annotatedTypeClasses(x, out, seen);
        }
        annotatedTypeClasses(ex.getAnnotatedReturnType(), out, seen);
        for (java.lang.reflect.AnnotatedType x : ex.getAnnotatedExceptionTypes()) {
            annotatedTypeClasses(x, out, seen);
        }
        annotatedTypeClasses(ex.getAnnotatedReceiverType(), out, seen);
    }

    // The observation-list graph walk (here for the JUnit).
    /**
     * Whether every use of the Class value {@code v0} (same method, through Pis / hub reads) is an observation on the observation
     * list ({@link #HARMLESS_NODES}, {@link #harmlessCall}). Frame states are not uses. {@code why} (optional) receives the
     * first harmful use.
     */
    static boolean harmlessClassUses(jdk.graal.compiler.nodes.ValueNode v0, String[] why) {
        java.util.ArrayDeque<jdk.graal.compiler.nodes.ValueNode> work = new java.util.ArrayDeque<>();
        Set<jdk.graal.compiler.graph.Node> seen = new java.util.HashSet<>();
        work.add(v0);
        while (!work.isEmpty()) {
            jdk.graal.compiler.nodes.ValueNode v = work.poll();
            if (!seen.add(v)) {
                continue;
            }
            for (jdk.graal.compiler.graph.Node u : v.usages()) {
                if (u instanceof jdk.graal.compiler.nodes.VirtualState) {
                    continue;
                }
                String k = u.getClass().getSimpleName();
                if (u instanceof jdk.graal.compiler.nodes.DynamicPiNode dp) {
                    if (dp.object() == v) {
                        work.add(dp); // the object passes on (a Pi of the Class value itself)
                    }
                    continue; // as the type mirror: an observation (cast)
                }
                if (classCastMessageArgument(u, v)) {
                    continue; // the Class only names the ClassCastException message
                }
                if (FOLLOW_NODES.contains(k) && u instanceof jdk.graal.compiler.nodes.ValueNode uv) {
                    work.add(uv);
                    continue;
                }
                if (HARMLESS_NODES.contains(k)) {
                    continue;
                }
                if (u instanceof jdk.graal.compiler.nodes.java.MethodCallTargetNode mct) {
                    ResolvedJavaMethod t = mct.targetMethod();
                    String holder = t == null ? "?" : t.getDeclaringClass().toJavaName(true);
                    java.util.List<jdk.graal.compiler.nodes.ValueNode> args = mct.arguments();
                    boolean recvClass = !args.isEmpty() && isClassStamp(args.get(0));
                    for (int i = 0; i < args.size(); i++) {
                        if (args.get(i) == v && (t == null || !harmlessCall(holder, t.getName(), i, i == 0 || recvClass))) {
                            if (why != null) {
                                why[0] = "call:" + holder + "." + (t == null ? "?" : t.getName()) + "#" + i;
                            }
                            return false;
                        }
                    }
                    continue;
                }
                if (why != null) {
                    why[0] = "node:" + k;
                }
                return false;
            }
        }
        return true;
    }

    /**
     * The CLASS_CAST exception: {@code v} is argument 1 (and not argument 0) of a 2-argument {@code BytecodeExceptionNode} / {@code ThrowBytecodeExceptionNode} of kind CLASS_CAST. Every
     * lowering passes the Class only to {@code ImplicitExceptions.createClassCastException(Object, Object)}, which keeps
     * {@code getTypeName()} as the message (the Class object is not stored), or drops the arguments (the cached / OPT
     * variants); SVM itself treats exactly this use as not making the Class reachable
     * ({@code MethodTypeFlowBuilder.ignoreConstant}). Every other kind stays harmful.
     */
    static boolean classCastMessageArgument(jdk.graal.compiler.graph.Node u, jdk.graal.compiler.nodes.ValueNode v) {
        java.util.List<jdk.graal.compiler.nodes.ValueNode> args;
        jdk.graal.compiler.nodes.extended.BytecodeExceptionNode.BytecodeExceptionKind kind;
        if (u instanceof jdk.graal.compiler.nodes.extended.BytecodeExceptionNode b) {
            args = b.getArguments();
            kind = b.getExceptionKind();
        } else if (u instanceof com.oracle.svm.core.graal.nodes.ThrowBytecodeExceptionNode b) {
            args = b.getArguments();
            kind = b.getExceptionKind();
        } else {
            return false;
        }
        return classCastMessageArgument(kind, args, v);
    }

    /** The pure row test of {@link #classCastMessageArgument(jdk.graal.compiler.graph.Node, jdk.graal.compiler.nodes.ValueNode)} (JUnit). */
    static <V> boolean classCastMessageArgument(jdk.graal.compiler.nodes.extended.BytecodeExceptionNode.BytecodeExceptionKind kind, java.util.List<V> args, V v) {
        return kind == jdk.graal.compiler.nodes.extended.BytecodeExceptionNode.BytecodeExceptionKind.CLASS_CAST && args.size() == 2 && args.get(1) == v && args.get(0) != v;
    }

    static boolean isClassStamp(jdk.graal.compiler.nodes.ValueNode n) {
        ResolvedJavaType t = jdk.graal.compiler.nodes.type.StampTool.typeOrNull(n);
        return t != null && classHolder(t.toJavaName(true));
    }

    // The self-slot CLASS_HOLDER exception.
    /** The holder type and field of the only discountable hub-internal slot: T's own companion's nest host. */
    static final String COMPANION_TYPE = "com.oracle.svm.core.hub.DynamicHubCompanion";
    static final String NEST_HOST_FIELD = "nestHost";

    /**
     * A holder record {@code (h, f)} of T's hub is discounted iff f is {@code DynamicHubCompanion.nestHost}, h is
     * a {@code DynamicHubCompanion} instance, h is T's own companion (the value of T's hub field {@code companion}),
     * T's hub is the companion's only holder in the heap, no pending slot kind off the allow-list may hold a companion,
     * every run-time reader of {@code DynamicHub.companion} / {@code getCompanion()} is audited, and the build mode is the
     * closed world (not layered, no runtime class loading). Any false = no discount.
     */
    static boolean selfSlotDiscount(String holderType, String field, boolean companionIsTs, boolean soleHolder, boolean pendingOk, boolean readersOk, boolean buildOk) {
        return COMPANION_TYPE.equals(holderType) && NEST_HOST_FIELD.equals(field) && companionIsTs && soleHolder && pendingOk && readersOk && buildOk;
    }

    /**
     * The audited SVM-internal consumers of a companion object outside DynamicHub / DynamicHubCompanion
     * themselves. {@code MultiThreadedMonitorSupport.replaceObject}: the companion is a Class's lock replacement ("never
     * exposed to user code", MultiThreadedMonitorSupport.java:430-438).
     */
    static final Set<String> COMPANION_READERS = Set.of("com.oracle.svm.core.hub.DynamicHub", "java.lang.Class", "com.oracle.svm.core.hub.DynamicHubCompanion",
                    "com.oracle.svm.core.monitor.MultiThreadedMonitorSupport", "java.lang.Class$Atomic");

    /**
     * Whether a companion read in a method of {@code declaringClass} is audited: DynamicHub itself (in the
     * analysis universe it substitutes {@code java.lang.Class}), its companion, its private static accessor classes
     * ({@code DynamicHub$...Accessors}, DynamicHub.java:2230-2270: field offsets / slot accessors of the companion), the
     * {@code Class$Atomic} substitution (DynamicHub.java:2479-2512: Unsafe CAS on the companion's reflectionData /
     * annotationType / annotationData slots, the companion is the CAS base only) and MultiThreadedMonitorSupport
     * (the lock replacement of a Class, "never exposed to user code"). Any other reader fails the discount closed unless
     * the companion value is only a field-access base ({@code companionFieldUseOnly}).
     */
    static boolean companionReaderAudited(String declaringClass) {
        return COMPANION_READERS.contains(declaringClass) || declaringClass.startsWith("com.oracle.svm.core.hub.DynamicHub$");
    }

    // The INLINED_ONLY exception.
    /** The recursion bound of {@link #inlinedOnlyOk} (an inlined-only caller whose callers are framed, ... up to 3 levels). */
    static final int INLINED_ONLY_DEPTH = 3;

    /** The facts of one method for {@link #inlinedOnlyOk} (a hand-built table in the JUnit; the RT index in production). */
    interface InlinedFacts<M> {
        /** The unframed cause of {@code m}, or null when m has a frame with a decodable graph. */
        UnframedCause causeOf(M m);

        /** (ii) m is native, an intrinsic, a root, reflection / JNI registered, or has a non-ORIGINAL multi-method variant. */
        boolean excluded(M m);

        /** The bytecode callers of m (an over-approximation), or null = the index failed (fail closed). */
        java.util.Collection<M> callers(M m);

        /**
         * The CLINIT exception: {@code m} is a class initializer that never runs at run time: not implementation-invoked, not a root, its hub's ClassInitializationInfo initialized with no
         * initializer pointer, consistent with the hosted initialized / simulated state, in a closed-world non-layered
         * build without run-time class loading and without a run-time-compiled variant. Default false (fail closed).
         */
        default boolean deadClinit(M m) {
            return false;
        }

        /**
         * Whether every wildcard caller (a method holding an {@code invokedynamic} or a signature-polymorphic
         * MethodHandle invoke, {@link #methodHandleInvoker}: a constant MethodHandle / call site intrinsified there can
         * inline any method without a bytecode invoke naming it) passes {@link ObjRetRules#wildcardOk}. Image-level (the
         * same answer for every x). Default true: a hand-built table has no such site; production computes it.
         */
        default boolean wildcardsOk() {
            return true;
        }
    }

    /**
     * {@code x} is INLINED_ONLY, not excluded, has callers, and every caller is framed or itself passes
     * (recursively, bounded by {@link #INLINED_ONLY_DEPTH}; a cycle or the bound = false). The CLINIT
     * exception: a CLINIT_BUILD_TIME / CLINIT_SIMULATED caller that is {@link InlinedFacts#deadClinit
     * dead} (never runs at run time) is skipped; the non-empty-callers rule stays (the dead clinit is positive evidence).
     * Any caller with another unframed cause (CLINIT_RUNTIME included), an index failure or an exception = false (fail
     * closed).
     */
    static <M> boolean inlinedOnlyOk(M x, InlinedFacts<M> f) {
        try {
            return inlinedOnlyOk(x, f, INLINED_ONLY_DEPTH, new java.util.HashSet<>()) && f.wildcardsOk();
        } catch (RuntimeException e) {
            return false;
        }
    }

    /**
     * One wildcard caller {@code w} (see {@link InlinedFacts#wildcardsOk}) cannot run an inlined body
     * unwalked: w is framed (its graph holds the inlined body), a dead class initializer, or itself INLINED_ONLY with
     * every bytecode caller passing (recursively, the same bound). Wildcard callers of w are not expanded again: each of
     * them is checked by this same test (the image-level conjunction), so every host of a chain of inlinings is checked.
     * Any other cause, or an exception = false.
     */
    static <M> boolean wildcardOk(M w, InlinedFacts<M> f) {
        try {
            UnframedCause c = f.causeOf(w);
            if (c == null) {
                return true;
            }
            if ((c == UnframedCause.CLINIT_BUILD_TIME || c == UnframedCause.CLINIT_SIMULATED) && f.deadClinit(w)) {
                return true;
            }
            return c == UnframedCause.INLINED_ONLY && inlinedOnlyOk(w, f, INLINED_ONLY_DEPTH, new java.util.HashSet<>());
        } catch (RuntimeException e) {
            return false;
        }
    }

    /**
     * Pure (JUnit): the wildcard set closed upward along inlining. A wildcard W that is itself inlined
     * somewhere ({@code inlined}) may carry its MethodHandle / call-site intrinsification (and so the inlined target's body)
     * into every host it is inlined into; those hosts are found among W's bytecode callers, so each of them is a wildcard
     * too, transitively. Bounded like {@link #inlinedOnlyOk} ({@code depth} levels above the seeds): an inlined member at
     * the bound, or an inlined member whose callers are unknown or empty ({@code callers} answers null or an empty set),
     * fails the closure (null = fail closed: the INLINED_ONLY exception is then off image-wide).
     */
    static <M> Set<M> wildcardClosure(java.util.Collection<M> seeds, java.util.function.Predicate<M> inlined, java.util.function.Function<M, java.util.Collection<M>> callers, int depth) {
        Set<M> out = new java.util.LinkedHashSet<>(seeds);
        java.util.List<M> level = new java.util.ArrayList<>(out);
        for (int l = 0; !level.isEmpty(); l++) {
            java.util.List<M> next = new java.util.ArrayList<>();
            for (M w : level) {
                if (!inlined.test(w)) {
                    continue;
                }
                if (l >= depth) {
                    return null; // an inlining chain above the bound: fail closed
                }
                java.util.Collection<M> cs = callers.apply(w);
                if (cs == null || cs.isEmpty()) {
                    // An inlined wildcard with no known host (inlined through a plugin / substitution that does not name
                    // it in bytecode, or an index gap) fails closed, as inlinedOnlyOk
                    return null;
                }
                for (M c : cs) {
                    if (out.add(c)) {
                        next.add(c);
                    }
                }
            }
            level = next;
        }
        return out;
    }

    private static <M> boolean inlinedOnlyOk(M x, InlinedFacts<M> f, int depth, Set<M> path) {
        if (depth <= 0 || !path.add(x)) {
            return false; // the bound or a cycle
        }
        try {
            if (f.causeOf(x) != UnframedCause.INLINED_ONLY || f.excluded(x)) {
                return false;
            }
            java.util.Collection<M> cs = f.callers(x);
            if (cs == null || cs.isEmpty()) {
                return false;
            }
            for (M c : cs) {
                UnframedCause cc = f.causeOf(c);
                if (cc == null) {
                    continue; // a framed caller: the inlined body is in its graph
                }
                if ((cc == UnframedCause.CLINIT_BUILD_TIME || cc == UnframedCause.CLINIT_SIMULATED) && f.deadClinit(c)) {
                    continue; // the CLINIT exception: the inlined copy lives in a graph that never runs at run time
                }
                if (cc != UnframedCause.INLINED_ONLY || !inlinedOnlyOk(c, f, depth - 1, path)) {
                    return false;
                }
            }
            return true;
        } finally {
            path.remove(x);
        }
    }

    /**
     * The caller-matching rule of the INLINED_ONLY index (RT {@code bytecodeCallers}), pure. A bytecode
     * invoke site with x's name + descriptor and referenced holder h may reach x when: h is unresolved (null); x is a
     * constructor and h == x's class; an {@code invokestatic} / {@code invokespecial} resolves upward from h (x's class
     * is h or a supertype of h); an {@code invokevirtual} / {@code invokeinterface} also dispatches downward (h is a
     * supertype of x's class).
     */
    static boolean bytecodeCallerMatch(boolean holderUnresolved, boolean ctor, boolean staticOrSpecial, boolean holderIsXClass, boolean xClassAssignableFromHolder,
                    boolean holderAssignableFromXClass) {
        if (holderUnresolved) {
            return true;
        }
        if (ctor) {
            return holderIsXClass;
        }
        if (staticOrSpecial) {
            return xClassAssignableFromHolder;
        }
        return xClassAssignableFromHolder || holderAssignableFromXClass;
    }

    /**
     * The signature-polymorphic {@code java.lang.invoke.MethodHandle} methods through which a constant
     * MethodHandle can be intrinsified into a direct call (and the callee inlined) without a bytecode invoke naming it.
     * A method holding such a site, or an {@code invokedynamic}, is a caller of every INLINED_ONLY method (a wildcard).
     */
    static boolean methodHandleInvoker(String holderBinaryName, String name) {
        if (!"java.lang.invoke.MethodHandle".equals(holderBinaryName)) {
            return false;
        }
        return name.equals("invoke") || name.equals("invokeExact") || name.equals("invokeBasic") || name.equals("invokeWithArguments") || name.startsWith("linkTo");
    }
}
