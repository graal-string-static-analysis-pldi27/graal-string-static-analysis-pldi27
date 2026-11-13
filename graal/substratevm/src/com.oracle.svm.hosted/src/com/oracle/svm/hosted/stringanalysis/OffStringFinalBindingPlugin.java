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
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Predicate;

import com.oracle.svm.core.ParsingReason;
import com.oracle.svm.core.SubstrateOptions;
import com.oracle.svm.core.hub.RuntimeClassLoading;
import com.oracle.svm.core.imagelayer.ImageLayerBuildingSupport;
import com.oracle.svm.core.util.UserError;

import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.java.BytecodeParser;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration.Plugins;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.graal.compiler.nodes.type.StampTool;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The OFF parse-time String binding (inlining parity with stock): in an image without string analysis and without a
 * profile ("OFF"), bind every String call at parse time as stock GraalVM does with a final {@code java.lang.String}.
 * <p>
 * The builder JDK's String is {@code public non-sealed class String} (for the reps only), so the parser cannot bind
 * {@code invokevirtual String.m} and a String receiver stamp is not exact. Stock binds both at parse time: (R1) the
 * bytecode target is declared by String; (R2) the receiver stamp's type is String (any owner: {@code CharSequence},
 * {@code Comparable}, {@code Object} …). This plugin turns such an invoke into
 * {@code handleReplacedInvoke(Special, String.resolveConcreteMethod(m), args)}, the direct call stock would have, so the
 * stock intrinsics ({@code String.equals}/{@code hashCode}/{@code intern}), parse-time inlining and the IBA decisions
 * apply as in stock. It is prepended at {@code registerGraphBuilderPlugins}, so every other node plugin sees only the
 * bound form (a node plugin prepended later would run first; none is today in the analysis parse).
 * <p>
 * Soundness: no subtype of String can be instantiated in such an image; {@link #checkNoInstantiatedStringSubtype}
 * (afterAnalysis) fails the build otherwise. Registered only when no string-analysis mode or profile is active, the
 * type world is closed, the build is not layered and runtime class loading is off ({@link #appliesTo}); knob
 * {@code svm.stringanalysis.off.stringfinal=0} disables the binding and the check.
 * <p>
 * Skipped (counted): a caller declared by an interface (a Special call there would get the invokespecial
 * super-interface receiver check of {@code appendInvoke}, which a String receiver fails); a parse that is not the
 * bytecode parser or parses an intrinsic; a receiver stamp that is a strict subtype of String (rep code, dead in OFF);
 * a null-constant receiver (the parser's own path deoptimizes); a target String does not resolve concretely.
 */
public final class OffStringFinalBindingPlugin implements NodePlugin {

    /**
     * Knob {@code off.stringfinal} (default 2 = the binding in OFF and zero-admit images, see
     * {@link ZeroAdmitStock}; 1 = OFF images only; 0 = off, also disables the afterAnalysis check).
     */
    static final boolean ENABLED = ZeroAdmitStock.MODE != 0;

    /** Set when the plugin is registered for this build: the afterAnalysis check and the census apply. */
    static volatile boolean registered;
    /** The OFF registration ({@link #registerIfApplies}) happened in this build. */
    static volatile boolean offRegistered;

    static final AtomicLong BOUND_R1 = new AtomicLong();
    static final AtomicLong BOUND_R2 = new AtomicLong();
    static final AtomicLong SKIP_INTERFACE_CALLER = new AtomicLong();
    static final AtomicLong SKIP_NOT_PARSER = new AtomicLong();
    static final AtomicLong SKIP_REP_RECEIVER = new AtomicLong();
    static final AtomicLong SKIP_UNRESOLVED = new AtomicLong();
    /** The interface callers whose String calls stay unbound (named in the census; at most 20). */
    static final java.util.Set<String> SKIPPED_INTERFACE_CALLERS = java.util.concurrent.ConcurrentHashMap.newKeySet();

    /**
     * True iff the OFF binding applies: the knob is on, no string-analysis mode, fork/child role or profile is active,
     * and the type world is closed and complete: a closed type world, no layered build (a later layer could instantiate a
     * String subtype) and no runtime class loading (a class loaded at run time could subclass the non-final String).
     */
    static boolean appliesTo(boolean knob, boolean stringAnalysis, boolean fork, boolean childOnly, boolean modeOnly, String profileOption, boolean profileLoaded,
                    boolean closedTypeWorld, boolean layeredBuild, boolean runtimeClassLoading) {
        return knob && !stringAnalysis && !fork && !childOnly && !modeOnly && profileOption == null && !profileLoaded &&
                        closedTypeWorld && !layeredBuild && !runtimeClassLoading;
    }

    /**
     * The zero-admit registration condition (the profile itself is checked per invoke by
     * {@link ZeroAdmitStock#active}, since it is loaded at beforeAnalysis, after plugin registration): knob 2, the parent
     * of an analysis build or a build with an explicit profile, and the closed, complete type world of {@link #appliesTo}.
     */
    static boolean appliesToZeroAdmit(int mode, boolean stringAnalysis, boolean fork, boolean childOnly, String profileOption, boolean closedTypeWorld, boolean layeredBuild,
                    boolean runtimeClassLoading) {
        return mode >= 2 && !fork && !childOnly && (stringAnalysis || profileOption != null) && closedTypeWorld && !layeredBuild && !runtimeClassLoading;
    }

    static boolean appliesToZeroAdmitThisBuild() {
        return appliesToZeroAdmit(ZeroAdmitStock.MODE, SubstrateOptions.StringAnalysis.getValue(), SubstrateOptions.StringAnalysisFork.getValue(),
                        SubstrateOptions.StringAnalysisChildOnly.getValue(), SubstrateOptions.StringRepProfile.getValue(), SubstrateOptions.useClosedTypeWorld(),
                        ImageLayerBuildingSupport.buildingImageLayer(), RuntimeClassLoading.isSupported());
    }

    /** {@link #appliesTo} on this build's options. */
    static boolean appliesToThisBuild() {
        return appliesTo(ENABLED, SubstrateOptions.StringAnalysis.getValue(), SubstrateOptions.StringAnalysisFork.getValue(), SubstrateOptions.StringAnalysisChildOnly.getValue(),
                        SubstrateOptions.StringAnalysisSingleByteOnly.getValue() || SubstrateOptions.StringAnalysisStringViewOnly.getValue() ||
                                        SubstrateOptions.StringAnalysisLazyConcatOnly.getValue(),
                        SubstrateOptions.StringRepProfile.getValue(), RepresentationProfileHolder.hasProfile(),
                        SubstrateOptions.useClosedTypeWorld(), ImageLayerBuildingSupport.buildingImageLayer(), RuntimeClassLoading.isSupported());
    }

    /**
     * Registration from {@code StringAnalysisFeature.registerGraphBuilderPlugins}: for the analysis parse only and only
     * when {@code applies} holds, prepends a new instance and marks the plugin registered. Returns whether it registered.
     */
    static boolean registerIfApplies(ParsingReason reason, java.util.function.BooleanSupplier applies, Plugins plugins) {
        if (reason != ParsingReason.PointsToAnalysis || !applies.getAsBoolean()) {
            return false;
        }
        registered = true;
        offRegistered = true;
        plugins.prependNodePlugin(new OffStringFinalBindingPlugin(false));
        return true;
    }

    /** The zero-admit registration: binds only while {@link ZeroAdmitStock#active}; marks the build registered once. */
    static boolean registerZeroAdmitIfApplies(ParsingReason reason, java.util.function.BooleanSupplier applies, Plugins plugins) {
        if (reason != ParsingReason.PointsToAnalysis || !applies.getAsBoolean()) {
            return false;
        }
        plugins.prependNodePlugin(new OffStringFinalBindingPlugin(true));
        return true;
    }

    /** True for the zero-admit instance: it binds only while {@link ZeroAdmitStock#active}. */
    private final boolean zeroAdmitOnly;

    /** True once a zero-admit instance saw an open gate (census tag). */
    static volatile boolean zeroAdmit;

    OffStringFinalBindingPlugin(boolean zeroAdmitOnly) {
        this.zeroAdmitOnly = zeroAdmitOnly;
    }

    static String censusLine() {
        return "[string-analysis] off-stringfinal" + (zeroAdmit ? " (zero-admit profile)" : "") + ": bound String-declared target=" + BOUND_R1.get() + " String receiver stamp=" +
                        BOUND_R2.get() +
                        "; skipped: interface caller=" + SKIP_INTERFACE_CALLER.get() + " not the bytecode parser/intrinsic=" + SKIP_NOT_PARSER.get() +
                        " rep receiver=" + SKIP_REP_RECEIVER.get() + " unresolved=" + SKIP_UNRESOLVED.get() +
                        (SKIPPED_INTERFACE_CALLERS.isEmpty() ? "" : "; interface callers " + new java.util.TreeSet<>(SKIPPED_INTERFACE_CALLERS));
    }

    private volatile ResolvedJavaType stringType;

    private ResolvedJavaType stringType(GraphBuilderContext b) {
        ResolvedJavaType s = stringType;
        if (s == null) {
            s = b.getMetaAccess().lookupJavaType(String.class);
            stringType = s;
        }
        return s;
    }

    /** The per-invoke outcome of {@link #decide}: leave the invoke ({@code NOT_*}/{@code SKIP_*}) or bind it. */
    enum Decision {
        /** Static or already bound (final/private target, exact receiver): nothing to do, not counted. */
        NOT_INDIRECT,
        /** Neither R1 nor R2: not a String call, not counted. */
        NOT_STRING,
        /** The receiver stamp is a strict subtype of String (rep code, dead in OFF). */
        SKIP_REP_RECEIVER,
        /** Not the bytecode parser, or parsing an intrinsic (no {@code handleReplacedInvoke} with a kind there). */
        SKIP_NOT_PARSER,
        /** A null-constant receiver: the parser's own {@code appendInvoke} deoptimizes, as in stock; not counted. */
        SKIP_NULL_CONSTANT,
        /** The caller (or its host class) is an interface: a Special call would get the super-interface check. */
        SKIP_INTERFACE_CALLER,
        /** String does not resolve the target concretely. */
        SKIP_UNRESOLVED,
        /** Bind: the bytecode target is declared by String. */
        BIND_R1,
        /** Bind: the receiver stamp's type is String (any other owner). */
        BIND_R2;

        boolean binds() {
            return this == BIND_R1 || this == BIND_R2;
        }
    }

    /** The receiver stamp's type relative to String. */
    enum Receiver {
        /** No type reference, or a type unrelated to / a supertype of String. */
        OTHER,
        /** Exactly String. */
        STRING,
        /** A strict subtype of String. */
        STRICT_SUBTYPE
    }

    /**
     * The binding decision for one invoke, pure, in the order of the checks {@link #handleInvoke} relies on;
     * {@code targetConcrete} is consulted only when every other check passed.
     */
    static Decision decide(InvokeKind kind, int argCount, boolean declaredByString, Receiver receiver, boolean bytecodeParser, boolean parsingIntrinsic,
                    boolean nullConstantReceiver, boolean callerIsInterface, java.util.function.BooleanSupplier targetConcrete) {
        if (kind == null || !kind.isIndirect() || argCount == 0) {
            return Decision.NOT_INDIRECT;
        }
        boolean r1 = declaredByString;
        boolean r2 = !r1 && receiver == Receiver.STRING;
        if (!r1 && !r2) {
            return Decision.NOT_STRING;
        }
        if (receiver == Receiver.STRICT_SUBTYPE) {
            return Decision.SKIP_REP_RECEIVER;
        }
        if (!bytecodeParser || parsingIntrinsic) {
            return Decision.SKIP_NOT_PARSER;
        }
        if (nullConstantReceiver) {
            return Decision.SKIP_NULL_CONSTANT;
        }
        if (callerIsInterface) {
            return Decision.SKIP_INTERFACE_CALLER;
        }
        if (!targetConcrete.getAsBoolean()) {
            return Decision.SKIP_UNRESOLVED;
        }
        return r1 ? Decision.BIND_R1 : Decision.BIND_R2;
    }

    @Override
    public boolean handleInvoke(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (InlineCacheTrivialMethodNodePlugin.isFlatReentry(b, method)) {
            return false; // never active in OFF (no IC plugin); the uniform first check of every string-analysis plugin
        }
        InvokeKind kind = b.getInvokeKind();
        if (kind == null || !kind.isIndirect() || args.length == 0) {
            return false; // the NOT_INDIRECT case of decide, before anything else is computed
        }
        if (zeroAdmitOnly) {
            if (!ZeroAdmitStock.active()) {
                return false;
            }
            if (!registered) {
                zeroAdmit = true;
                registered = true; // the afterAnalysis subtype check applies
            }
        }
        ResolvedJavaType string = stringType(b);
        TypeReference recv = StampTool.typeReferenceOrNull(args[0]);
        Receiver receiver = recv == null ? Receiver.OTHER
                        : recv.getType().equals(string) ? Receiver.STRING : string.isAssignableFrom(recv.getType()) ? Receiver.STRICT_SUBTYPE : Receiver.OTHER;
        boolean declaredByString = string.equals(method.getDeclaringClass());
        if (!declaredByString && receiver != Receiver.STRING) {
            return false; // the NOT_STRING case of decide (the common case: no further inputs computed)
        }
        ResolvedJavaType caller = b.getMethod().getDeclaringClass();
        @SuppressWarnings("deprecation")
        ResolvedJavaType host = caller.getHostClass();
        ResolvedJavaMethod[] target = new ResolvedJavaMethod[1];
        Decision d = decide(kind, args.length, declaredByString, receiver, b instanceof BytecodeParser, b.parsingIntrinsic(), args[0].isNullConstant(),
                        (host != null ? host : caller).isInterface(), () -> {
                            target[0] = string.resolveConcreteMethod(method, caller);
                            return target[0] != null && !target[0].isAbstract();
                        });
        switch (d) {
            case SKIP_REP_RECEIVER -> SKIP_REP_RECEIVER.incrementAndGet();
            case SKIP_NOT_PARSER -> SKIP_NOT_PARSER.incrementAndGet();
            case SKIP_INTERFACE_CALLER -> {
                SKIP_INTERFACE_CALLER.incrementAndGet();
                if (SKIPPED_INTERFACE_CALLERS.size() < 20) {
                    SKIPPED_INTERFACE_CALLERS.add(b.getMethod().format("%H.%n(%p)") + "->" + method.format("%h.%n"));
                }
            }
            case SKIP_UNRESOLVED -> SKIP_UNRESOLVED.incrementAndGet();
            default -> {
            }
        }
        if (!d.binds()) {
            return false;
        }
        /*
         * The Special call target gets no referencedType (stock keeps the invokeinterface owner on the call target for
         * R2 sites, BytecodeParser.createNonInlinedInvoke); a Special call target never reads it.
         */
        b.handleReplacedInvoke(InvokeKind.Special, target[0], args, false);
        (d == Decision.BIND_R1 ? BOUND_R1 : BOUND_R2).incrementAndGet();
        return true;
    }

    /** The binding's soundness check (afterAnalysis, when registered): no strict subtype of String is instantiated. */
    static <T extends ResolvedJavaType> void checkNoInstantiatedStringSubtype(Iterable<T> types, ResolvedJavaType string, Predicate<T> instantiated) {
        List<String> bad = instantiatedStringSubtypes(types, string, instantiated);
        if (!bad.isEmpty()) {
            throw UserError.abort("string analysis OFF parse-time String binding: String calls were bound at parse time as if java.lang.String were final, " +
                            "but these subtypes of java.lang.String are instantiated: %s. Build with -J-Dsvm.stringanalysis.off.stringfinal=0 to disable the binding.", bad);
        }
    }

    static <T extends ResolvedJavaType> List<String> instantiatedStringSubtypes(Iterable<T> types, ResolvedJavaType string, Predicate<T> instantiated) {
        List<String> bad = new ArrayList<>();
        for (T t : types) {
            if (!t.equals(string) && string.isAssignableFrom(t) && instantiated.test(t)) {
                bad.add(t.toJavaName());
            }
        }
        return bad;
    }
}
