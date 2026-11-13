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
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import com.oracle.svm.core.graal.snippets.DeoptHostedSnippets;

import jdk.graal.compiler.core.common.type.ObjectStamp;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.FixedGuardNode;
import jdk.graal.compiler.nodes.LogicConstantNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ShortCircuitOrNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.ConditionalNode;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;
import jdk.graal.compiler.nodes.extended.BytecodeExceptionNode.BytecodeExceptionKind;
import jdk.graal.compiler.nodes.extended.GuardingNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.ProfileData.BranchProbabilityData;
import jdk.vm.ci.meta.DeoptimizationAction;
import jdk.vm.ci.meta.DeoptimizationReason;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.JavaTypeProfile;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Type-check IC, parent side: at a {@code checkcast}/{@code instanceof java.lang.String} whose key
 * ({@code SiteKeys.profileKey} of the parsed method and bci; every inlined copy carries its lowering) carries a child
 * {@code TYPE_CHECK} line of the same kind, the stock type-ID range check is replaced by exact hub compares:
 * {@code exact String} for a rep-free line (UNKNOWN/EXACT_STRING; stock's final-String code),
 * {@code exact String || exact R1 || ...} for a rep list of at most {@code svm.stringanalysis.typecheck.ic.list} reps.
 * Trusted (no run-time fallback): a hub outside {String} ∪ R fails the check (a ClassCastException for a cast, false for
 * instanceof). Null semantics are stock. The check is in the parse graph, so points-to sees it. Stock: no line, a kind
 * mismatch, UNPROVEN, an unmarked line inside a terminal body ({@link StringAnalysisPolicy#alwaysVirtJdkTrivialApplies}),
 * an unknown rep name, a list over the cap, a stock condition that is already constant. Knob
 * {@code svm.stringanalysis.typecheck.ic}: 0 = stock, 1 = on (default), 2 = CHECK (debug only): the stock check is kept
 * and a guard after it throws ("TYPECHECK-IC key") when a value passes stock but not the exact set. Analysis parse only.
 */
final class TypeCheckIcNodePlugin implements NodePlugin {

    static final int MODE = TypeCheckLines.MODE;
    /** {@code svm.stringanalysis.typecheck.ic.list}: the rep-list cap; default 2; 0 = rep-free sites only. */
    static final int LIST_CAP = Integer.getInteger("svm.stringanalysis.typecheck.ic.list", 2);
    static final String CHECK_MESSAGE = "TYPECHECK-IC";

    enum Decision {
        LOWER_EXACT,
        LOWER_LIST,
        STOCK_OFF,
        STOCK_NO_LINE,
        STOCK_KIND_MISMATCH,
        STOCK_KT_ONLY,
        STOCK_UNPROVEN,
        STOCK_UNKNOWN_REP,
        STOCK_LIST_CAP
    }

    /**
     * Pure (JUnit): {@code line} = the loaded "CAST|INST variant" (null: no line); {@code jdkTerminal} = the parsed
     * method is a terminal body (only KT-marked lines apply there).
     */
    static Decision decide(int mode, int listCap, String line, boolean isCast, boolean jdkTerminal) {
        if (mode == 0) {
            return Decision.STOCK_OFF;
        }
        if (line == null) {
            return Decision.STOCK_NO_LINE;
        }
        int sp = line.indexOf(' ');
        String kind = line.substring(0, sp);
        String variant = line.substring(sp + 1);
        if (!kind.equals(isCast ? TypeCheckLines.CAST : TypeCheckLines.INST)) {
            return Decision.STOCK_KIND_MISMATCH;
        }
        String unmarked = TerminalBodyKinds.stripMarker(variant);
        if (unmarked == null && jdkTerminal) {
            return Decision.STOCK_KT_ONLY;
        }
        List<String> reps = TypeCheckLines.repNames(unmarked != null ? unmarked : variant);
        if (reps == null) {
            return Decision.STOCK_UNPROVEN;
        }
        for (String r : reps) {
            if (InlineCacheRegistry.getRepClass(r) == null) {
                return Decision.STOCK_UNKNOWN_REP;
            }
        }
        if (reps.isEmpty()) {
            return Decision.LOWER_EXACT;
        }
        return reps.size() <= listCap ? Decision.LOWER_LIST : Decision.STOCK_LIST_CAP;
    }

    /** The reps of a line (KT marker stripped; null for UNPROVEN). */
    static List<String> lineReps(String line) {
        String variant = line.substring(line.indexOf(' ') + 1);
        String unmarked = TerminalBodyKinds.stripMarker(variant);
        return TypeCheckLines.repNames(unmarked != null ? unmarked : variant);
    }

    /**
     * The exact condition: {@code exact String} (null allowed iff {@code allowNull}) or-ed with {@code exact R} per rep
     * (each false on null). Unregistered nodes; the caller appends.
     */
    static LogicNode exactCondition(MetaAccessProvider meta, ValueNode object, List<Class<?>> reps, boolean allowNull) {
        TypeReference exactString = TypeReference.createExactTrusted(meta.lookupJavaType(String.class));
        LogicNode cond = allowNull ? InstanceOfNode.createAllowNull(exactString, object, null, null) : InstanceOfNode.create(exactString, object);
        for (Class<?> r : reps) {
            LogicNode isRep = InstanceOfNode.create(TypeReference.createExactTrusted(meta.lookupJavaType(r)), object);
            cond = ShortCircuitOrNode.create(cond, false, isRep, false, BranchProbabilityData.unknown());
        }
        return cond;
    }

    static final Map<Decision, AtomicLong> CAST_BY = new ConcurrentHashMap<>();
    static final Map<Decision, AtomicLong> INST_BY = new ConcurrentHashMap<>();
    static final AtomicLong CHECK_GUARDS = new AtomicLong();
    static final AtomicLong STOCK_CONSTANT = new AtomicLong();

    private static void count(boolean isCast, Decision d) {
        (isCast ? CAST_BY : INST_BY).computeIfAbsent(d, k -> new AtomicLong()).incrementAndGet();
    }

    static String summary() {
        Map<Decision, Long> c = new TreeMap<>();
        Map<Decision, Long> i = new TreeMap<>();
        CAST_BY.forEach((k, v) -> c.put(k, v.get()));
        INST_BY.forEach((k, v) -> i.put(k, v.get()));
        return "[string-analysis] typecheck-ic: mode=" + MODE + " list=" + LIST_CAP + " lowered exact=" + c.getOrDefault(Decision.LOWER_EXACT, 0L) + "/" + i.getOrDefault(Decision.LOWER_EXACT, 0L) +
                        " list=" + c.getOrDefault(Decision.LOWER_LIST, 0L) + "/" + i.getOrDefault(Decision.LOWER_LIST, 0L) + " (cast/inst parses) stock: no-line=" +
                        c.getOrDefault(Decision.STOCK_NO_LINE, 0L) + "/" + i.getOrDefault(Decision.STOCK_NO_LINE, 0L) + " unproven=" + c.getOrDefault(Decision.STOCK_UNPROVEN, 0L) + "/" +
                        i.getOrDefault(Decision.STOCK_UNPROVEN, 0L) + " kt-only=" + c.getOrDefault(Decision.STOCK_KT_ONLY, 0L) + "/" + i.getOrDefault(Decision.STOCK_KT_ONLY, 0L) + " mismatch=" +
                        c.getOrDefault(Decision.STOCK_KIND_MISMATCH, 0L) + "/" + i.getOrDefault(Decision.STOCK_KIND_MISMATCH, 0L) + " list-cap=" + c.getOrDefault(Decision.STOCK_LIST_CAP, 0L) + "/" +
                        i.getOrDefault(Decision.STOCK_LIST_CAP, 0L) + " unknown-rep=" + c.getOrDefault(Decision.STOCK_UNKNOWN_REP, 0L) + "/" + i.getOrDefault(Decision.STOCK_UNKNOWN_REP, 0L) +
                        " constant=" + STOCK_CONSTANT.get() + " check-guards=" + CHECK_GUARDS.get() + " profile-lines=" +
                        (RepresentationProfileHolder.hasProfile() ? RepresentationProfileHolder.getInstance().getTypeCheckSites().size() : 0);
    }

    static void resetCensus() {
        CAST_BY.clear();
        INST_BY.clear();
        CHECK_GUARDS.set(0);
        STOCK_CONSTANT.set(0);
    }

    /** The flat re-entry contract (FlatStockPathTest): every string-analysis node plugin steps aside in a flat re-entry; no invoke is handled here. */
    @Override
    public boolean handleInvoke(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (InlineCacheTrivialMethodNodePlugin.isFlatReentry(b, method)) {
            return false;
        }
        return false;
    }

    @Override
    public boolean handleCheckCast(GraphBuilderContext b, ValueNode object, ResolvedJavaType type, JavaTypeProfile profile) {
        return handle(b, object, type, true);
    }

    @Override
    public boolean handleInstanceOf(GraphBuilderContext b, ValueNode object, ResolvedJavaType type, JavaTypeProfile profile) {
        return handle(b, object, type, false);
    }

    private static boolean handle(GraphBuilderContext b, ValueNode objectIn, ResolvedJavaType type, boolean isCast) {
        if (MODE == 0 || !RepresentationProfileHolder.hasProfile() || b.getMethod() == null) {
            return false;
        }
        ResolvedJavaType stringType = b.getMetaAccess().lookupJavaType(String.class);
        if (!stringType.equals(type)) {
            return false;
        }
        String key = SiteKeys.profileKey(b.getMethod(), b.bci());
        String line = RepresentationProfileHolder.getInstance().getTypeCheck(key);
        Decision d = decide(MODE, LIST_CAP, line, isCast, StringAnalysisPolicy.alwaysVirtJdkTrivialApplies(b));
        if (d != Decision.LOWER_EXACT && d != Decision.LOWER_LIST) {
            count(isCast, d);
            return false;
        }
        ValueNode object = objectIn;
        if (object.isUnregistered()) {
            object = b.add(object);
        }
        TypeReference stockType = TypeReference.createTrusted(b.getAssumptions(), stringType);
        LogicNode stock = isCast ? InstanceOfNode.createAllowNull(stockType, object, null, null) : InstanceOfNode.create(stockType, object);
        if (stock instanceof LogicConstantNode) {
            STOCK_CONSTANT.incrementAndGet();
            return false; // already decided (a tautology or a contradiction): stock
        }
        List<Class<?>> reps = new ArrayList<>();
        for (String r : lineReps(line)) {
            reps.add(InlineCacheRegistry.getRepClass(r));
        }
        count(isCast, d);
        boolean nonNull = ((ObjectStamp) object.stamp(NodeView.DEFAULT)).nonNull();
        if (MODE == 2) {
            emitCheckMode(b, object, stock, reps, isCast, key, stockType, nonNull, type);
            return true;
        }
        LogicNode cond = b.append(exactCondition(b.getMetaAccess(), object, reps, isCast));
        if (isCast) {
            GuardingNode guard = castGuard(b, cond, object, type);
            if (guard == null) {
                b.push(JavaKind.Object, object); // the exact condition folded to true (stock: castNode = object)
                return true;
            }
            TypeReference piType = reps.isEmpty() ? TypeReference.createExactTrusted(stringType) : stockType;
            b.addPush(JavaKind.Object, PiNode.create(object, StampFactory.object(piType, nonNull), guard.asNode()));
        } else {
            b.addPush(JavaKind.Int, ConditionalNode.create(cond, NodeView.DEFAULT));
        }
        return true;
    }

    /** The stock tail of {@code BytecodeParser.genCheckCast}: the explicit CCE edge (AOT) or a deopting guard. */
    private static GuardingNode castGuard(GraphBuilderContext b, LogicNode cond, ValueNode object, ResolvedJavaType type) {
        if (b.needsExplicitException()) {
            ConstantNode clazz = ConstantNode.forConstant(b.getConstantReflection().asJavaClass(type), b.getMetaAccess(), b.getGraph());
            return b.emitBytecodeExceptionCheck(cond, true, BytecodeExceptionKind.CLASS_CAST, object, clazz);
        }
        return b.add(new FixedGuardNode(cond, DeoptimizationReason.ClassCastException, DeoptimizationAction.InvalidateReprofile, false));
    }

    /**
     * CHECK mode (typecheck.ic=2, debug only): the stock check, then a guard that the value is null, not a String, or in
     * {String} ∪ R; a failing guard throws "Code that was considered unreachable ... TYPECHECK-IC key" at run time.
     */
    private static void emitCheckMode(GraphBuilderContext b, ValueNode object, LogicNode stockIn, List<Class<?>> reps, boolean isCast, String key, TypeReference stockType,
                    boolean nonNull, ResolvedJavaType type) {
        LogicNode stock = b.append(stockIn);
        DeoptHostedSnippets.AnalysisSpeculation spec = new DeoptHostedSnippets.AnalysisSpeculation(new DeoptHostedSnippets.AnalysisSpeculationReason(CHECK_MESSAGE + " " + key));
        ValueNode result;
        if (isCast) {
            GuardingNode guard = castGuard(b, stock, object, type);
            ValueNode pi = guard == null ? object : b.add(PiNode.create(object, StampFactory.object(stockType, nonNull), guard.asNode()));
            LogicNode ok = b.append(exactCondition(b.getMetaAccess(), object, reps, true));
            b.add(new FixedGuardNode(ok, DeoptimizationReason.UnreachedCode, DeoptimizationAction.None, spec, false));
            result = pi;
            b.push(JavaKind.Object, result);
        } else {
            LogicNode exact = exactCondition(b.getMetaAccess(), object, reps, false);
            LogicNode ok = b.append(ShortCircuitOrNode.create(stock, true, exact, false, BranchProbabilityData.injected(BranchProbabilityNode.LIKELY_PROBABILITY)));
            b.add(new FixedGuardNode(ok, DeoptimizationReason.UnreachedCode, DeoptimizationAction.None, spec, false));
            b.addPush(JavaKind.Int, ConditionalNode.create(stock, NodeView.DEFAULT));
        }
        CHECK_GUARDS.incrementAndGet();
    }
}
