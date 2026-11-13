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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.LoadIndexedNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.java.StoreIndexedNode;
import jdk.graal.compiler.replacements.nodes.BasicArrayCopyNode;
import jdk.graal.compiler.replacements.nodes.ObjectClone;

/**
 * The STRING atom kind of the container engine ({@link RecursiveTracking}): one atom per creation site of an activated
 * heuristic, walked by the container engine's own walk. It differs from a container atom only in the use
 * classification: it records field usages ({@code value}/{@code coder}) and terminal usages (a receiver call whose
 * resolved target is declared by a stringy type) and does not enter a stringy method it is the receiver of; argument
 * positions are entered; a store is the container ESCAPE; derived values are not followed; everything else is a named
 * refusal.
 * <p>
 * This class holds the non-state pieces: knobs, the seed identity, the hand-list lookup, the pure row decisions (pinned
 * by JUnit) and the {@link Sites} adapter (implemented by {@link ForwardFixpoint}) through which the walk records usages.
 */
final class StringAtoms {

    private StringAtoms() {
    }

    /** The rep classes whose {@code instanceof} answers {@link #repInvariantClassLabel} compares with String's. */
    static final List<Class<?>> TYPESWITCH_REPS = typeSwitchReps();

    private static List<Class<?>> typeSwitchReps() {
        List<Class<?>> l = new java.util.ArrayList<>(InlineCacheRegistry.REP_CLASSES.values());
        l.add(com.oracle.svm.core.stringrep.TrivialString.class);
        return List.copyOf(l);
    }

    /** The exact bootstrap identity the {@code typeSwitch} model applies to. */
    static final String TYPESWITCH_OWNER = "java.lang.runtime.SwitchBootstraps";
    static final String TYPESWITCH_NAME = "typeSwitch";
    static final String TYPESWITCH_DESCRIPTOR = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;";

    /** Print-only census: the typeSwitch sites the recogniser saw, by outcome ({@code modelled} or the refusal reason). */
    static final java.util.concurrent.ConcurrentHashMap<String, java.util.concurrent.atomic.LongAdder> TYPESWITCH_SITES = new java.util.concurrent.ConcurrentHashMap<>();

    static void countTypeSwitchSite(String outcome) {
        TYPESWITCH_SITES.computeIfAbsent(outcome, k -> new java.util.concurrent.atomic.LongAdder()).increment();
    }

    /** The typeSwitch census value {@code outcome:count,...} (sorted; {@code none} when empty). */
    static String typeSwitchCensus() {
        StringBuilder sb = new StringBuilder();
        new java.util.TreeMap<>(TYPESWITCH_SITES).forEach((k, v) -> sb.append(sb.length() > 0 ? "," : "").append(k).append(':').append(v.sum()));
        return sb.length() > 0 ? sb.toString() : "none";
    }

    /**
     * Pure: true when the bootstrap method is exactly {@code SwitchBootstraps.typeSwitch} (owner, name and
     * descriptor). No other bootstrap (enumSwitch, ObjectMethods, ...) is modelled.
     */
    static boolean isTypeSwitchBootstrap(String owner, String name, String descriptor) {
        return TYPESWITCH_OWNER.equals(owner) && TYPESWITCH_NAME.equals(name) && TYPESWITCH_DESCRIPTOR.equals(descriptor);
    }

    /**
     * Pure: the label {@code l} is a {@code Class} whose generated test is an {@code instanceof} that a String and every
     * rep answer identically. JDK 25 {@code generateTypeSwitchSkeleton}: a nominal reference Class label compiles to
     * {@code instanceof L} (or no test when {@code L} is the selector type); a hidden label (or array of one) compiles to
     * {@code Class.isInstance} (refused: a strict class check, {@code SugNameTables.isStrictClassCheckName}); a primitive
     * label to an unboxing test (refused). The reps extend the non-sealed {@code String} and declare no interface of
     * their own, so {@code rep instanceof L == "" instanceof L} for every {@code L} outside the String cone and for
     * {@code L == String}; a label strictly below String is refused, and the equality is also checked per rep class
     * ({@code reps}) so that a future rep with an extra interface refuses by itself.
     */
    static boolean repInvariantClassLabel(Object l, java.util.Collection<Class<?>> reps) {
        if (!(l instanceof Class<?> c) || c.isPrimitive()) {
            return false;
        }
        Class<?> leaf = c;
        while (leaf.isArray()) {
            leaf = leaf.getComponentType();
        }
        if (leaf.isHidden()) {
            return false;
        }
        if (c != String.class && String.class.isAssignableFrom(c)) {
            return false; // a label in the String cone below String: a rep (or a subclass of one) diverges
        }
        boolean stringAnswer = c.isAssignableFrom(String.class);
        for (Class<?> r : reps) {
            if (c.isAssignableFrom(r) != stringAnswer) {
                return false;
            }
        }
        return true;
    }

    /**
     * The static arguments of a {@code typeSwitch} indy as host objects, or null when there are none; a null constant is
     * a null element and a primitive constant its boxed value (both refused).
     */
    static List<Object> typeSwitchLabels(List<jdk.vm.ci.meta.JavaConstant> sa, java.util.function.Function<jdk.vm.ci.meta.JavaConstant, Object> asObject) {
        if (sa == null) {
            return null;
        }
        List<Object> labels = new java.util.ArrayList<>(sa.size());
        for (jdk.vm.ci.meta.JavaConstant c : sa) {
            if (c == null || c.isNull()) {
                labels.add(null);
            } else if (c.getJavaKind() == jdk.vm.ci.meta.JavaKind.Object) {
                labels.add(asObject.apply(c));
            } else {
                labels.add(c.asBoxedPrimitive());
            }
        }
        return labels;
    }

    /**
     * Pure: the reason a {@code typeSwitch} site is not modelled, or null when it is. Requires invocation type
     * {@code (reference, int)int}, the F1 shape with 2 dynamic arguments ({@link #f1Shape}) and readable, rep-invariant
     * Class labels.
     *
     * <p>The typeSwitch model (sound): an INVOKEDYNAMIC site whose bootstrap
     * is exactly {@code SwitchBootstraps.typeSwitch}, in the F1 form {@code linkToTargetMethod(selector, restart,
     * appendix)}, with a reference selector and only rep-invariant {@code Class} labels ({@link #repInvariantClassLabel})
     * is crossed by the model: the selector is only null-tested and {@code instanceof}-tested against the labels (JDK 25
     * {@code SwitchBootstraps.generateTypeSwitchSkeleton}), which a String and every rep answer identically, so no
     * usage, no escape, and the generated switch is not entered. Every other {@code typeSwitch} site (value labels,
     * primitive or hidden Class labels, labels below String, other shapes) and every container atom keep the ordinary
     * crossing.
     */
    static String typeSwitchRefusal(Class<?>[] params, Class<?> returnType, String irTarget, int nargs, boolean lastConst, List<Object> labels,
                    java.util.Collection<Class<?>> reps) {
        if (params == null || params.length != 2 || params[0].isPrimitive() || params[1] != int.class || returnType != int.class) {
            return "invocation-type";
        }
        if (f1Shape(irTarget, nargs, lastConst, 2) != ConcatKind.F1) {
            return "not-f1";
        }
        if (labels == null) {
            return "labels-unreadable";
        }
        for (Object l : labels) {
            if (!(l instanceof Class<?>)) {
                return "label-" + (l == null ? "unreadable" : l.getClass().getSimpleName()); // String, Integer, EnumDesc, ...: value compares
            }
            if (!repInvariantClassLabel(l, reps)) {
                return "label-class-not-rep-invariant";
            }
        }
        return null;
    }

    /**
     * The seed identity: the site component of a STRING atom's key, its own key space, so a container sink minted at the
     * same IR node can never collide with a string atom (RAtomKey compares sites by identity). One per creation-site SUG
     * vertex (heuristics at the same vertex share it); {@code births} are the IR invokes at the site.
     */
    static final class StringSeed {
        final SugVertex vertex;
        final String heuristics;
        final LocalFlowGraph frame;
        final List<ValueNode> births;
        /** Non-null when the seed cannot be walked (no frame / no IR invoke at the site): the atom is refused by this name. */
        final ContainerTables.RTrackRefusal unwalkable;
        /** The atom's dispatch block when it is not the String cone (an accumulator seed: the builder class), else null. */
        final ForwardFixpoint.Block block;

        StringSeed(SugVertex vertex, String heuristics, LocalFlowGraph frame, List<ValueNode> births, ContainerTables.RTrackRefusal unwalkable) {
            this(vertex, heuristics, frame, births, unwalkable, null);
        }

        StringSeed(SugVertex vertex, String heuristics, LocalFlowGraph frame, List<ValueNode> births, ContainerTables.RTrackRefusal unwalkable,
                        ForwardFixpoint.Block block) {
            this.vertex = vertex;
            this.heuristics = heuristics;
            this.frame = frame;
            this.births = births;
            this.unwalkable = unwalkable;
            this.block = block;
        }

        @Override
        public String toString() {
            return "sseed[" + heuristics + " " + vertex.getSourceLocation() + "]";
        }
    }

    // ------------------------------------------------------------------
    // The hand list (StringTerminalHandList): the terminals that may return `this`.
    // ------------------------------------------------------------------
    private static final Map<String, StringTerminalHandList.Entry> HAND = new HashMap<>();

    static {
        for (StringTerminalHandList.Entry e : StringTerminalHandList.STRING_ENTRIES) {
            HAND.put(e.declaringClass() + "#" + e.name() + "(" + e.signature() + ")", e);
        }
    }

    /** The hand-list entry of a resolved method (declaring class, name, usage-site signature), or null. */
    static StringTerminalHandList.Entry handEntry(String declaringClass, String name, String signature) {
        return HAND.get(declaringClass + "#" + name + "(" + signature + ")");
    }

    /**
     * Does the walk continue at this terminal's result (treated as an assignment of the receiver)? A hand-list String
     * entry with {@code returnsThis}, or a builder-type method whose declared return type is a builder type (a String
     * atom never reaches a builder target through the String-cone receiver filter).
     */
    static boolean continuesAtResult(String declaringClass, String name, String signature, String returnTypeName) {
        StringTerminalHandList.Entry e = handEntry(declaringClass, name, signature);
        if (e != null) {
            return e.returnsThis();
        }
        return StringTerminalHandList.BUILDER_TYPES.contains(declaringClass) && returnTypeName != null &&
                        (returnTypeName.equals(declaringClass) || StringTerminalHandList.BUILDER_TYPES.contains(returnTypeName) ||
                                        returnTypeName.equals("java.lang.Appendable") || returnTypeName.equals("java.io.Writer"));
    }

    static boolean continuesAtResult(AnalysisMethod t) {
        if (t == null || t.getDeclaringClass() == null) {
            return false;
        }
        String ret;
        try {
            ret = t.getSignature().getReturnType(null).toJavaName(true);
        } catch (Throwable ex) {
            ret = null;
        }
        return continuesAtResult(t.getDeclaringClass().toJavaName(true), t.getName(), SiteKeys.formatSignature(t), ret);
    }

    /** Slot 0 of a non-static call into a stringy-declared resolved target that is not a constructor. */
    static boolean isTerminalTarget(AnalysisMethod t) {
        return t != null && isTerminalTarget(t.isStatic(), t.isConstructor(), t.getDeclaringClass() != null ? t.getDeclaringClass().toJavaName(true) : null);
    }

    /** The pure form of {@link #isTerminalTarget(AnalysisMethod)} (pinned by JUnit). */
    static boolean isTerminalTarget(boolean isStatic, boolean isConstructor, String declaringClass) {
        if (isConstructor && !isStatic && declaringClass != null && StringTerminalHandList.BUILDER_TYPES.contains(declaringClass)) {
            // A builder constructor is a terminal usage of its receiver (only an accumulator atom can be that receiver);
            // its body only initialises the content
            return true;
        }
        return !isStatic && !isConstructor && declaringClass != null && ForwardFixpoint.isStringyDeclaringType(declaringClass);
    }

    /**
     * The invoke row of one argument slot holding the walked STRING (pure); {@code f4} is
     * {@code String.concat(String)}.
     */
    enum SlotRow {
        /** Slot 0 of a terminal: the terminal usage (and the hand-list continuation at the result); the body is not entered. */
        TERMINAL,
        /** Slot 1 of F4: the concat operand usage (recorded by the adapter); not entered. */
        CONCAT_OPERAND,
        /** Any other slot holding the string (a static call's argument, the self-argument rule): the callee is entered there. */
        ENTER
    }

    static SlotRow invokeSlotRow(int slot, boolean terminalTarget, boolean f4) {
        if (terminalTarget && slot == 0) {
            return SlotRow.TERMINAL;
        }
        if (f4 && slot == 1) {
            return SlotRow.CONCAT_OPERAND;
        }
        return SlotRow.ENTER;
    }

    /** The name of a strict field usage (a field other than {@code String.value/coder/hash/hashIsZero}). */
    static final String STRICT_FIELD_PREFIX = "field:";

    static String strictFieldUsageName(String fieldName) {
        return STRICT_FIELD_PREFIX + fieldName;
    }

    /** The resolved target is {@code java.lang.String#equals(Ljava/lang/Object;)Z} (never keyed on the name alone). */
    static boolean isStringEquals(jdk.vm.ci.meta.ResolvedJavaMethod m) {
        return m != null && m.getDeclaringClass() != null &&
                        isStringEquals(m.isStatic(), m.getDeclaringClass().toJavaName(true), m.getName(), m.getSignature().toMethodDescriptor());
    }

    /** The pure form of {@link #isStringEquals(jdk.vm.ci.meta.ResolvedJavaMethod)} (pinned by JUnit). */
    static boolean isStringEquals(boolean isStatic, String declaringClass, String name, String descriptor) {
        return !isStatic && "java.lang.String".equals(declaringClass) && "equals".equals(name) && "(Ljava/lang/Object;)Z".equals(descriptor);
    }

    /** The row of one argument slot holding the walked STRING at a resolved target, for the equals argument (pure; pinned by JUnit). */
    enum EqArgRow {
        /** Not the equals argument: the ordinary slot rules apply. */
        NONE,
        /** The equals argument at a call with a Phase-A site: the terminal usage; the body is not entered. */
        TERMINAL,
        /** The equals argument at a call without a Phase-A site: refused by name ({@code EQUALS_ARG_NO_SITE}). */
        NO_SITE
    }

    /**
     * The equals-argument terminal: a STRING atom at slot 1 of a call whose resolved
     * target is {@code String.equals(Object)} is a terminal PARAMETER usage at the call's Phase-A site, where the
     * equals matrix REDIRECTs it; the body is not entered. Other targets of the same call are entered as usual. Without
     * a Phase-A site the usage could not be REDIRECTed, so the atom is refused ({@code EQUALS_ARG_NO_SITE}).
     * {@code contentEquals(CharSequence)} is covered through its body's {@code this.equals(cs)} (an internal site that is
     * REDIRECTed).
     */
    static EqArgRow equalsArgRow(boolean stringAtom, int slot, boolean targetIsStringEquals, boolean hasPhaseASite) {
        if (!stringAtom || slot != 1 || !targetIsStringEquals) {
            return EqArgRow.NONE;
        }
        return hasPhaseASite ? EqArgRow.TERMINAL : EqArgRow.NO_SITE;
    }

    /** Builder-append mirror ({@link AppendMirror}): the row of one slot holding the walked STRING (pure; pinned by JUnit). */
    enum MirrorArgRow {
        /** Not the string slot of an entry point (or the mirror is off, or not a STRING atom): the ordinary slot rules apply. */
        NONE,
        /** The string slot at a mirrorable site: the adapter's PARAMETER usage there is the terminal usage; not entered. */
        TERMINAL,
        /** No mirrorable site: refused ({@code MIRROR_ARG_NO_SITE}); not entered. */
        NO_SITE
    }

    /**
     * {@code entrySlot}: {@link AppendMirror#stringSlot} of the resolved target (-1 for a non-entry); {@code mirrorSite}:
     * {@link AppendMirror#mirrorSite}.
     */
    static MirrorArgRow mirrorArgRow(boolean on, boolean stringAtom, int slot, int entrySlot, boolean mirrorSite) {
        if (!on || !stringAtom || entrySlot < 0 || slot != entrySlot) {
            return MirrorArgRow.NONE;
        }
        return mirrorSite ? MirrorArgRow.TERMINAL : MirrorArgRow.NO_SITE;
    }

    /** The resolved target is {@code java.lang.String#compareTo(Ljava/lang/String;)I} or the bridge {@code compareTo(Ljava/lang/Object;)I}. */
    static boolean isStringCompareTo(jdk.vm.ci.meta.ResolvedJavaMethod m) {
        return m != null && m.getDeclaringClass() != null &&
                        isStringCompareTo(m.isStatic(), m.getDeclaringClass().toJavaName(true), m.getName(), m.getSignature().toMethodDescriptor());
    }

    /** The pure form of {@link #isStringCompareTo(jdk.vm.ci.meta.ResolvedJavaMethod)} (pinned by JUnit). */
    static boolean isStringCompareTo(boolean isStatic, String declaringClass, String name, String descriptor) {
        return !isStatic && "java.lang.String".equals(declaringClass) && "compareTo".equals(name) &&
                        ("(Ljava/lang/String;)I".equals(descriptor) || "(Ljava/lang/Object;)I".equals(descriptor));
    }

    /** The resolved target is {@code java.lang.String#compareTo(Ljava/lang/String;)I} (the bridge excluded). */
    static boolean isStringCompareToString(jdk.vm.ci.meta.ResolvedJavaMethod m) {
        return isStringCompareTo(m) && "(Ljava/lang/String;)I".equals(m.getSignature().toMethodDescriptor());
    }

    /** The resolved target is the bridge {@code java.lang.String#compareTo(Ljava/lang/Object;)I}. */
    static boolean isStringCompareToBridge(jdk.vm.ci.meta.ResolvedJavaMethod m) {
        return isStringCompareTo(m) && "(Ljava/lang/Object;)I".equals(m.getSignature().toMethodDescriptor());
    }

    /** The compareTo mirror: the row of the slot holding the walked STRING at a resolved target (pure; pinned by JUnit). */
    enum CmpArgRow {
        /** Not a compareTo argument: the ordinary slot rules apply (the body is entered). */
        NONE,
        /** The argument of {@code compareTo(String)} at a call with a Phase-A site: the PARAMETER usage there (adapter). */
        TERMINAL,
        /**
         * The argument of the bridge {@code compareTo(Object)}: recorded at the bridge's internal {@code compareTo(String)}
         * Phase-A site (one image-wide site); refused when that site does not exist.
         */
        BRIDGE,
        /** No site the parent could REDIRECT: refused ({@code COMPARETO_ARG_NO_SITE}). */
        NO_SITE
    }

    /**
     * The compareTo-argument row. String map keys (the rep-aware compareTo rules): run-time comparisons are rep-aware;
     * bin-internal ordering and the worst case may differ, only result correctness is guaranteed. Gates:
     * (1) the compareTo-argument terminal: a STRING atom at slot 1 of a call whose resolved target is
     * {@code String.compareTo(String)} or its bridge {@code compareTo(Object)} is a terminal PARAMETER usage (the body,
     * whose {@code anotherString.value()} read is the hazard, is not entered), site-keyed (this row: at the call's
     * Phase-A site or the bridge's internal site, both REDIRECTed to {@code maybeCustomStringCompareTo}; otherwise
     * refused); (2) the receiver role: {@code compareTo} is in {@link LazyConcatWhitelist} (StringView overrides it); (3)
     * tree-bin class checks are representation-insensitive ({@link JdkModels.Family#repInsensitiveClassChecks}). Run
     * time for (1) and (2): the parent REDIRECTs every site an admitted rep argument reaches to
     * {@code String.maybeCustomStringCompareTo} (which deflects to the rep's own {@code compareTo}), and every value-null
     * rep overrides {@code compareTo} and {@code maybeCustomStringCompareTo}. (3) stays a modelling assumption: a tree bin
     * may order a rep key differently internally (result correctness only).
     *
     * <p>The LabsJDK {@code String.compareTo} is the stock body (no rep deflection): a rep argument is safe only at a call
     * the parent lowers to {@code String.maybeCustomStringCompareTo} (an {@code EQUALS_MATRIX REDIRECT} site), so the
     * compareTo-argument terminal is site-keyed like the equals argument; a global terminal would be unsound with the
     * stock body.
     */
    static CmpArgRow compareToArgRow(boolean stringAtom, int slot, boolean targetIsCompareToString, boolean targetIsBridge, boolean hasPhaseASite) {
        if (!stringAtom || slot != 1 || !(targetIsCompareToString || targetIsBridge)) {
            return CmpArgRow.NONE;
        }
        if (targetIsBridge) {
            return CmpArgRow.BRIDGE;
        }
        return hasPhaseASite ? CmpArgRow.TERMINAL : CmpArgRow.NO_SITE;
    }

    /**
     * Knob {@code sink.jmhblackhole} (default 1; 0 = the walk enters the Blackhole): the JMH Blackhole as a harness sink
     * model. A STRING atom passed as the argument of a call whose resolved target is
     * {@code org.openjdk.jmh.infra.Blackhole#consume(Object)}, or of its private helpers {@code consumeFull(Object)} /
     * {@code static consumeCompiler(Object)} (reached directly when {@code consume} is inlined at parse time), is a
     * terminal PARAMETER usage at the call's target usage site; the body is not entered; the usage counts as positive
     * downstream evidence like a safe-sink argument ({@code TransferFacts.isSafeSinkMethod}). Other targets, the
     * receiver slot and non-STRING atoms are handled as usual.
     * <p>
     * Why it is right at run time (JMH 1.37 bytecode): {@code consume(Object)} calls {@code consumeCompiler} (an empty
     * static method) or {@code consumeFull}, which stores {@code new WeakReference<>(obj)} into the public volatile field
     * {@code BlackholeL2.obj1}; no {@code getfield obj1} exists anywhere in JMH and the referent is read only by the GC. So
     * the value is never read: an identity-only sink with no usage.
     * <p>
     * Limitation: this is a model of the JMH harness, not a result of the generic analysis. The generic walk would need
     * member-sensitive reflection (the runner invokes the generated {@code *_jmhTest} methods reflectively), models of
     * {@code ConcurrentHashMap} and of the executors that call {@code BenchmarkTask.call()}, a
     * {@code MethodHandles.Lookup} / MemberName model, a per-field rule for the reflection-registered but never-read
     * {@code obj1}, and the no-usage admission policy ({@link AdmissionProof}) to reach the same verdict.
     */
    static final boolean JMH_BLACKHOLE_SINK = Integer.getInteger("svm.stringanalysis.sink.jmhblackhole", 1) != 0;

    /**
     * The builder classes an accumulator seed may allocate (the classes the parent's builder-view factories take).
     *
     * <p>The accumulator heuristic seeds user-code {@code new StringBuilder}/{@code new
     * StringBuffer} allocations as STRING atoms of kind "ACC" (pass 1: the builder's own usages; its constructors are
     * terminal usages), and after the first quiescence the {@code toString()} extractions of builders that pass the
     * only-growing table as kind "ACCX" (pass 2: the String View usage check). {@code java.io.StringWriter} is an
     * accumulator kind too (it wraps a private {@code StringBuffer buf}; its methods are judged by
     * {@link AccumulatorWhitelist#WRITER_GROWING_METHODS}; the parent lowers its {@code toString()} as
     * {@code StringView.create(writer.buf)}). An admitted, complete, escape-free accumulator extraction is emitted as
     * {@code ACCUMULATOR_VIEW_SHARED} (lowered to {@code StringView.createSkipCheck}, no occupancy check). An admitted
     * substring site whose string is stored ({@code strStored}, or a leak-marked usage outside W_view) is emitted as
     * {@code STRING_VIEW STORED} (lowered to {@code StringView.createStored}: a copy under 9 bytes or under half
     * occupancy).
     */
    static final java.util.Set<String> ACC_SEED_TYPES = AccumulatorWhitelist.withJoiner( // + StringJoiner
                    java.util.Set.of("java.lang.StringBuilder", "java.lang.StringBuffer", "java.io.StringWriter"));

    /**
     * The allocated class of an allocation node in the child's IR, else null. Covers the {@code AllocatedObjectNode} of a
     * materialised virtual object: the child's graphs are the analysed ones, so a builder allocation usually arrives as
     * CommitAllocation + AllocatedObject.
     */
    static jdk.vm.ci.meta.ResolvedJavaType allocatedType(Node n) {
        if (n instanceof jdk.graal.compiler.nodes.java.NewInstanceNode nin) {
            return nin.instanceClass();
        }
        if (n instanceof jdk.graal.compiler.nodes.java.NewInstanceWithExceptionNode niwe) {
            return niwe.instanceClass();
        }
        if (n instanceof jdk.graal.compiler.nodes.virtual.AllocatedObjectNode aon && aon.getVirtualObject() != null) {
            return aon.getVirtualObject().type();
        }
        return null;
    }

    /** The bytecode position of an allocation node ({@link #allocatedType}); the virtual object's / commit's as a fallback. */
    static jdk.graal.compiler.graph.NodeSourcePosition allocationPosition(Node n) {
        jdk.graal.compiler.graph.NodeSourcePosition p = n.getNodeSourcePosition();
        if (p == null && n instanceof jdk.graal.compiler.nodes.virtual.AllocatedObjectNode aon) {
            if (aon.getVirtualObject() != null) {
                p = aon.getVirtualObject().getNodeSourcePosition();
            }
            if (p == null && aon.getCommit() != null) {
                p = aon.getCommit().getNodeSourcePosition();
            }
        }
        return p;
    }

    /**
     * A vertex the literal seeding applies to (pure in the vertex fields).
     *
     * <p>The 1-char literal seed: a length-1 String literal (a
     * {@code STRING_LITERAL} vertex that is not a concat recipe constant) in user code is seeded as a STRING atom
     * (heuristic tag "SB") at its {@code ConstantNode}; the walk refuses identity observations ({@code LITERAL_IDENTITY});
     * the heuristic additionally demands positive downstream proof and the interaction rule (an {@code equals} with a
     * SINGLE_BYTE substring).
     * <p>
     * Soundness premise: the hazard uses of a seeded literal must be visible in the child's IR. The literal is a
     * compile-time String constant, so its direct same-frame hazard uses would fold at the child's graph parse
     * ({@code lit.getClass()} folds to a Class constant; {@code lit.intern()} folds to the constant, so
     * {@code lit.intern() == lit} folds to true), no usage fact would exist and
     * {@code SingleByteHeuristic.hasStrictClassCheck} / {@code reachesIntern} would be vacuous.
     * The {@code StringAnalysisChildNoFold} wrapper declines the {@code getClass}/{@code intern} graph-builder plugins
     * exactly for constant String receivers, so the invokes stay in the child IR and the strict class check /
     * {@code LITERAL_IDENTITY} rules fire unmodified. Without it the literal hazard uses would fold out of the child IR
     * and the two leak shapes would false-ADMIT.
     */
    static boolean isSeedableLiteral(SugVertex v) {
        return v.getNodeType() == SugNodeType.STRING_LITERAL && v.getLength() == 1 && v.getLiteralText() != null && v.getLiteralText().length() == 1 &&
                        !"concat-constant".equals(v.getLabel());
    }

    /** The resolved target is one of the three Blackhole Object sinks (see {@link #JMH_BLACKHOLE_SINK}). */
    static boolean isJmhBlackholeSink(jdk.vm.ci.meta.ResolvedJavaMethod m) {
        return m != null && m.getDeclaringClass() != null &&
                        isJmhBlackholeSink(m.isStatic(), m.getDeclaringClass().toJavaName(true), m.getName(), m.getSignature().toMethodDescriptor());
    }

    /** The pure form of {@link #isJmhBlackholeSink(jdk.vm.ci.meta.ResolvedJavaMethod)} (pinned by JUnit). */
    static boolean isJmhBlackholeSink(boolean isStatic, String declaringClass, String name, String descriptor) {
        if (!"org.openjdk.jmh.infra.Blackhole".equals(declaringClass) || !"(Ljava/lang/Object;)V".equals(descriptor)) {
            return false;
        }
        return isStatic ? "consumeCompiler".equals(name) : "consume".equals(name) || "consumeFull".equals(name);
    }

    /**
     * Pure; pinned by JUnit: the slot is the Blackhole sink argument (any slot but the receiver of an instance target).
     */
    static boolean jmhBlackholeSinkSlot(boolean on, boolean stringAtom, int slot, boolean targetIsStatic, boolean targetIsSink) {
        return on && stringAtom && targetIsSink && (targetIsStatic || slot != 0);
    }

    /**
     * Pure: may the {@code StringConcatFactory} strategy of this indy concat ({@code recipe} null for
     * {@code makeConcat}) copy an operand with {@code new String(String)}? Mirrors {@code makeSimpleConcat} (JDK 25): one
     * reference operand with empty constants ({@code newStringOf}), or two reference operands with all three constants
     * empty ({@code simpleConcat}). A {@code \2} constant tag or a malformed recipe answers {@code true}
     * (conservative).
     *
     * <p>Concat operands of a String View. The JDK's
     * {@code StringConcatFactory} ({@code makeSimpleConcat}, {@code InlineHiddenClassStrategy}; SVM runs the bootstrap
     * at build time and has no concat substitution) reads a String operand through {@code length()},
     * {@code isLatin1()}/{@code coder()}, {@code getBytes(byte[],int,byte)} and {@code toString()} (all supported by
     * StringView), except on two strategies that may copy an operand with {@code new String(String)} (which reads
     * {@code original.value()}, null for every custom rep, and the {@code hash}/{@code hashIsZero} fields):
     * {@code newStringOf} ({@code "" + s}) and {@code simpleConcat} ({@code a + b} copies {@code b} when {@code a} is
     * empty at run time). This method is that strategy test; a String View operand of a non-copying concat
     * is a supported usage; a copying concat, {@code String.concat} and an unrecognised site still reject (but see the
     * copy-site lowering, {@link #scfCopyShape}).
     */
    static boolean scfCopiesOperand(String bootName, String recipe, boolean[] primitive) {
        return scfCopyShape(bootName, recipe, primitive) != CopyShape.NONE;
    }

    /**
     * The copy shape of an indy concat's stock strategy: NONE never copies; UNARY = {@code newStringOf}; BINARY =
     * {@code simpleConcat}; UNKNOWN = a {@code \2} tag, malformed recipe or other bootstrap (conservatively copying,
     * never lowered).
     */
    enum CopyShape {
        NONE,
        UNARY,
        BINARY,
        UNKNOWN
    }

    /**
     * Pure; pinned by JUnit: {@link #scfCopiesOperand} with the shape.
     *
     * <p>A String View operand of a copying user-code indy concat (shape UNARY or BINARY) is a supported usage: the child
     * lists the site ({@code CONCAT_COPY}) and the parent replaces exactly that indy with
     * {@code com.oracle.svm.core.stringrep.RepConcat}, which copies a non-plain operand through its supported reads
     * instead of {@code new String(String)}. UNKNOWN keeps the reject.
     */
    static CopyShape scfCopyShape(String bootName, String recipe, boolean[] primitive) {
        int n = primitive.length;
        String[] constants = new String[n + 1];
        if ("makeConcat".equals(bootName)) {
            java.util.Arrays.fill(constants, "");
        } else if ("makeConcatWithConstants".equals(bootName) && recipe != null) {
            StringBuilder acc = new StringBuilder();
            int k = 0;
            for (int i = 0; i < recipe.length(); i++) {
                char c = recipe.charAt(i);
                if (c == '\u0001') {
                    if (k >= n) {
                        return CopyShape.UNKNOWN;
                    }
                    constants[k++] = acc.toString();
                    acc.setLength(0);
                } else if (c == '\u0002') {
                    return CopyShape.UNKNOWN;
                } else {
                    acc.append(c);
                }
            }
            if (k != n) {
                return CopyShape.UNKNOWN;
            }
            constants[n] = acc.toString();
        } else {
            return CopyShape.UNKNOWN;
        }
        if (n == 1) {
            return !primitive[0] && constants[0].isEmpty() && constants[1].isEmpty() ? CopyShape.UNARY : CopyShape.NONE;
        }
        if (n == 2) {
            return !primitive[0] && !primitive[1] && constants[0].isEmpty() && constants[1].isEmpty() && constants[2].isEmpty() ? CopyShape.BINARY : CopyShape.NONE;
        }
        return CopyShape.NONE;
    }

    /** F4: {@code String.concat(String)}. */
    static boolean isStringConcat(jdk.vm.ci.meta.ResolvedJavaMethod m) {
        return m != null && !m.isStatic() && "concat".equals(m.getName()) && m.getDeclaringClass() != null &&
                        "java.lang.String".equals(m.getDeclaringClass().toJavaName(true)) &&
                        "(Ljava/lang/String;)Ljava/lang/String;".equals(m.getSignature().toMethodDescriptor());
    }

    // ------------------------------------------------------------------
    // The string rows (pure decisions; the engine applies them in classifyUsage).
    // ------------------------------------------------------------------
    enum Row {
        /** A row both kinds share (carriers, escapes, returns, observations, refusals, …): the container code decides. */
        SHARED,
        /** A {@code LoadField} on the walked string: a field usage; stop (derived values are not followed). */
        FIELD_USAGE,
        /** A call target: terminal / entered / concat (the invoke rows). */
        INVOKE,
        /** {@code GetClass}, {@code LoadHub(OrNull)}, an exact non-fold-allowed {@code InstanceOf}: a CLASS_CHECK usage. */
        CLASS_CHECK,
        /** The string as the object/array of a store, an array load, a copy or a clone: {@code UNCLASSIFIED_ACCESS}. */
        UNCLASSIFIED
    }

    /** The class-check node classes (exact simple names, as the engine's observation list). */
    static final java.util.Set<String> CLASS_CHECK_NODES = java.util.Set.of("GetClassNode", "LoadHubNode", "LoadHubOrNullNode");

    /** The three {@code Class} name methods (all {@code ()Ljava/lang/String;}). */
    static final java.util.Set<String> CLASS_NAME_METHODS = java.util.Set.of("getName", "getSimpleName", "getTypeName");

    /**
     * The declaring class of a {@code Class} method in the child's IR. {@code java.lang.Class} is substituted by
     * {@code DynamicHub} in the image builder; both name the same type.
     */
    static final java.util.Set<String> CLASS_TYPE_NAMES = java.util.Set.of("java.lang.Class", "com.oracle.svm.core.hub.DynamicHub");

    /**
     * The {@code Class} value a getClass usage at {@code anchor} produces (a {@code GetClassNode} or an
     * {@code Object.getClass()} invoke result); null for any other anchor.
     */
    static ValueNode getClassResult(Node anchor) {
        if (anchor instanceof jdk.graal.compiler.nodes.extended.GetClassNode gc) {
            return gc;
        }
        if (anchor instanceof Invoke inv && inv.callTarget() instanceof MethodCallTargetNode ct && ct.targetMethod() != null) {
            var m = ct.targetMethod();
            if ("getClass".equals(m.getName()) && m.getSignature().getParameterCount(false) == 0 && !m.isStatic()) {
                return inv.asNode();
            }
        }
        return null;
    }

    /**
     * True when every use of the {@code Class} value {@code cls} (through Pi nodes) is a frame state or the
     * receiver of a {@code Class.getName/getSimpleName/getTypeName()} call. A pure local IR check; no tracking.
     *
     * <p>The class-name-only rule: a {@code getClass()} of a
     * walked value whose {@code Class} result is used, in the same method, only as the receiver of
     * {@code getName()}, {@code getSimpleName()} or {@code getTypeName()} is not a usage, for every heuristic alike (the
     * decision is taken in {@code RecursiveTracking.strUsage}, including in entered JDK bodies). Class-name observation
     * is out of scope by design, like identity: a representation reports its own class name, in every consequence of
     * the name (control flow included); the name String is not followed. Any other use of the {@code Class} keeps the
     * CLASS_CHECK usage. No lowering.
     * <p>
     * The {@code Class} value may also be the receiver of {@code Class.toString()} or the sole argument of
     * {@code String.valueOf(Object)} (the {@code "..." + x.getClass()} shape). JDK 25: {@code valueOf(obj)} is
     * {@code obj == null ? "null" : obj.toString()} and the Class is non-null and final; {@code Class.toString} and the
     * image's {@code DynamicHub.toString} are {@code (isInterface() ? "interface " : isPrimitive() ? "" : "class ") +
     * getName()}, reading only the class kind (identical for a String and every rep) and the out-of-scope class name.
     */
    static boolean classNameOnlyUses(ValueNode cls) {
        java.util.ArrayDeque<ValueNode> work = new java.util.ArrayDeque<>();
        java.util.Set<Node> seen = new java.util.HashSet<>();
        work.add(cls);
        seen.add(cls);
        boolean any = false;
        while (!work.isEmpty()) {
            ValueNode v = work.poll();
            for (Node u : v.usages()) {
                if (u instanceof jdk.graal.compiler.nodes.FrameState || u instanceof jdk.graal.compiler.nodes.VirtualState) {
                    continue;
                }
                if (u instanceof jdk.graal.compiler.nodes.PiNode pi && pi.object() == v) {
                    if (seen.add(pi)) {
                        work.add(pi);
                    }
                    continue;
                }
                if (u instanceof MethodCallTargetNode ct && (isClassNameCall(ct, v) || isClassToStringCall(ct, v))) {
                    any = true;
                    continue;
                }
                return false;
            }
        }
        return any;
    }

    /** {@code ct} is {@code v.getName()/getSimpleName()/getTypeName()} on {@code Class}, {@code v} only the receiver. */
    static boolean isClassNameCall(MethodCallTargetNode ct, ValueNode v) {
        var m = ct.targetMethod();
        if (m == null || m.isStatic() || ct.arguments().size() != 1 || ct.arguments().get(0) != v) {
            return false;
        }
        return isClassNameMethod(m.getDeclaringClass().toJavaName(true), m.getName(), m.getSignature().toMethodDescriptor());
    }

    /**
     * {@code ct} is {@code v.toString()} on {@code Class} ({@code v} only the receiver) or
     * {@code String.valueOf(v)} ({@code v} the only argument).
     */
    static boolean isClassToStringCall(MethodCallTargetNode ct, ValueNode v) {
        var m = ct.targetMethod();
        if (m == null || ct.arguments().size() != 1 || ct.arguments().get(0) != v) {
            return false;
        }
        return isClassToStringMethod(m.isStatic(), m.getDeclaringClass().toJavaName(true), m.getName(), m.getSignature().toMethodDescriptor());
    }

    /** The pure name test of {@link #isClassToStringCall}. */
    static boolean isClassToStringMethod(boolean isStatic, String declaringClass, String name, String descriptor) {
        if (isStatic) {
            return "java.lang.String".equals(declaringClass) && "valueOf".equals(name) && "(Ljava/lang/Object;)Ljava/lang/String;".equals(descriptor);
        }
        return CLASS_TYPE_NAMES.contains(declaringClass) && "toString".equals(name) && "()Ljava/lang/String;".equals(descriptor);
    }

    /** The pure name test of {@link #isClassNameCall}. */
    static boolean isClassNameMethod(String declaringClass, String name, String descriptor) {
        return CLASS_TYPE_NAMES.contains(declaringClass) && CLASS_NAME_METHODS.contains(name) && "()Ljava/lang/String;".equals(descriptor);
    }

    /** Census only: the smallest bci of a name call on {@code cls} (through Pi nodes), -1 if none. */
    static int classNameCallBci(ValueNode cls) {
        if (cls == null) {
            return -1;
        }
        int best = -1;
        java.util.ArrayDeque<ValueNode> work = new java.util.ArrayDeque<>();
        java.util.Set<Node> seen = new java.util.HashSet<>();
        work.add(cls);
        seen.add(cls);
        while (!work.isEmpty()) {
            ValueNode v = work.poll();
            for (Node u : v.usages()) {
                if (u instanceof jdk.graal.compiler.nodes.PiNode pi && pi.object() == v && seen.add(pi)) {
                    work.add(pi);
                } else if (u instanceof MethodCallTargetNode ct && isClassNameCall(ct, v) && ct.invoke() != null) {
                    int b = ct.invoke().bci();
                    best = best < 0 ? b : Math.min(best, b);
                }
            }
        }
        return best;
    }

    /** The whole class-name-only rule at a usage anchor. */
    static boolean isClassNameOnlyGetClass(Node anchor) {
        ValueNode cls = getClassResult(anchor);
        return cls != null && classNameOnlyUses(cls);
    }

    /**
     * The STRING atom's row for use {@code u} of the walked node {@code n}. {@code strictExactInstanceOf}: an exact
     * {@code InstanceOf} is a strict class check ({@code LfgWalk.instanceofSourceFoldAllowed} said no). A store whose
     * value is {@code n} is the shared ESCAPE row; when {@code n} is also its object the engine refuses that role too.
     */
    static Row rowOf(Node u, Node n, boolean strictExactInstanceOf) {
        if (u instanceof LoadFieldNode lfn) {
            return lfn.object() == n && !lfn.isStatic() ? Row.FIELD_USAGE : Row.SHARED;
        }
        if (u instanceof StoreFieldNode sfn) {
            return sfn.object() == n && !sfn.isStatic() && sfn.value() != n ? Row.UNCLASSIFIED : Row.SHARED;
        }
        if (u instanceof StoreIndexedNode sin) {
            return sin.array() == n && sin.value() != n ? Row.UNCLASSIFIED : Row.SHARED;
        }
        if (u instanceof LoadIndexedNode || u instanceof BasicArrayCopyNode || u instanceof ObjectClone) {
            return Row.UNCLASSIFIED;
        }
        if (u instanceof MethodCallTargetNode) {
            return Row.INVOKE;
        }
        if (CLASS_CHECK_NODES.contains(u.getClass().getSimpleName())) {
            return Row.CLASS_CHECK;
        }
        if (u instanceof InstanceOfNode ion && ion.type() != null && ion.type().isExact() && strictExactInstanceOf) {
            return Row.CLASS_CHECK;
        }
        return Row.SHARED;
    }

    // ------------------------------------------------------------------
    // The concat recogniser (F1; F4 is a resolved-target test; F2 never occurs).
    // ------------------------------------------------------------------
    enum ConcatKind {
        /** Not an SCF indy site. */
        NONE,
        /** The designed single-invoke form: {@code linkToTargetMethod(operands..., appendix)}. */
        F1,
        /** An SCF indy site whose IR the recogniser does not recognise (F2, the child rewrite, anything else): refused by name. */
        UNRECOGNISED,
        /** A modelled {@code SwitchBootstraps.typeSwitch} site (F1, rep-invariant Class labels only). */
        TYPESWITCH
    }

    /**
     * The F1 shape test (pure): the invoke targets {@code linkToTargetMethod} and carries the dynamic operands by position
     * (not by non-constness: a dynamic operand may be constant-folded) followed by the constant appendix.
     *
     * <p>The analysis child never applies StringRepresentationReplacementPlugin's concatTrace(String[]) rewrite: the concat
     * terminal sees the F1 form.
     */
    static ConcatKind f1Shape(String targetName, int nargs, boolean lastIsConstant, int dynamicParams) {
        if (!"linkToTargetMethod".equals(targetName) || dynamicParams < 0 || nargs != dynamicParams + 1 || !lastIsConstant) {
            return ConcatKind.UNRECOGNISED;
        }
        return ConcatKind.F1;
    }

    /** The concat crossing's row of one argument slot of a recognised F1 concat (pure). */
    enum ConcatSlot {
        /** A String-declared operand of a STRING atom: the usage "argument of the concat"; stop. */
        OPERAND_USAGE,
        /** A String-declared operand of a container atom: nothing is read of it (a container is never a String value). */
        NOTHING,
        /** A non-String reference operand: the desugared implicit {@code o.toString()} crossing, both kinds. */
        DESUGARED_TO_STRING,
        /** The appendix slot (after the dynamic operands): the ordinary crossing. */
        APPENDIX
    }

    static ConcatSlot concatSlot(Concat c, int slot, boolean stringAtom) {
        if (slot >= c.operandCount()) {
            return ConcatSlot.APPENDIX;
        }
        if (c.stringDeclared()[slot]) {
            return stringAtom ? ConcatSlot.OPERAND_USAGE : ConcatSlot.NOTHING;
        }
        return ConcatSlot.DESUGARED_TO_STRING;
    }

    /** The named refusal of a concat site ({@code UNRECOGNISED_CONCAT}), or null (NONE: ordinary; F1: crossed). */
    static ContainerTables.RTrackRefusal concatRefusal(Concat c) {
        return c != null && c.kind() == ConcatKind.UNRECOGNISED ? ContainerTables.RTrackRefusal.UNRECOGNISED_CONCAT : null;
    }

    /**
     * The desugared call's refusal by target count (pure); null = dispatch.
     */
    static ContainerTables.RTrackRefusal desugaredTargetRefusal(int size, int cap) {
        if (size < 0) {
            return ContainerTables.RTrackRefusal.UNRESOLVED_VALUE;
        }
        if (size == 0) {
            return ContainerTables.RTrackRefusal.NO_TARGET;
        }
        return size > cap ? ContainerTables.RTrackRefusal.CHA_FAN_CAP : null;
    }

    /**
     * Pure: the site's bytecode or bootstrap is unreadable. A known {@code INVOKEDYNAMIC} or a call to
     * {@code linkToTargetMethod} may be an unseen SCF concat: the named refusal, never a silent pass. Any other call is
     * not an indy site.
     */
    static ConcatKind unreadableSite(String irTargetName, boolean knownIndy) {
        return knownIndy || "linkToTargetMethod".equals(irTargetName) ? ConcatKind.UNRECOGNISED : ConcatKind.NONE;
    }

    /**
     * Pure: the bytecode at the bci is readable but not {@code INVOKEDYNAMIC}. A call to {@code linkToTargetMethod}
     * then carries a bci that does not index this frame's bytecode and may be an unseen SCF concat: the named refusal,
     * never a silent pass.
     */
    static ConcatKind nonIndyOpcodeSite(String irTargetName) {
        return "linkToTargetMethod".equals(irTargetName) ? ConcatKind.UNRECOGNISED : ConcatKind.NONE;
    }

    /**
     * A recognised concat: the kind, and per dynamic operand whether its declared type is {@code String} (read directly)
     * or another reference type (the desugared implicit {@code o.toString()} call), and that type.
     */
    record Concat(ConcatKind kind, boolean[] stringDeclared, AnalysisType[] operandTypes, CopyShape copyShape) {

        static final Concat NONE = new Concat(ConcatKind.NONE, null, null, CopyShape.UNKNOWN);
        static final Concat UNRECOGNISED = new Concat(ConcatKind.UNRECOGNISED, null, null, CopyShape.UNKNOWN);
        static final Concat TYPESWITCH = new Concat(ConcatKind.TYPESWITCH, null, null, CopyShape.UNKNOWN);

        Concat(ConcatKind kind, boolean[] stringDeclared, AnalysisType[] operandTypes) {
            this(kind, stringDeclared, operandTypes, CopyShape.UNKNOWN);
        }

        /** May the stock strategy copy an operand ({@link #scfCopiesOperand}): any shape but NONE. */
        boolean copiesOperand() {
            return copyShape != CopyShape.NONE;
        }

        int operandCount() {
            return stringDeclared != null ? stringDeclared.length : 0;
        }
    }

    // ------------------------------------------------------------------
    // The adapter to the verdict layer's SUG sites (implemented by ForwardFixpoint).
    // ------------------------------------------------------------------
    interface Sites {
        /** The Phase-A method-call usage site (STRING_METHOD_CALL / JDK_LIBRARY_CALL) of the invoke, or null. */
        SugVertex phaseACallSite(LocalFlowGraph frame, Invoke inv);

        /** The concat's CONCAT_EXPRESSION site: the Phase-A concat vertex, else a detached one keyed by (frame, bci). */
        SugVertex concatSite(LocalFlowGraph frame, Invoke inv);

        /** The resolved-target receiver usage site ({@code targetUsageSite}: frame, bci, target, full signature). */
        SugVertex targetSite(LocalFlowGraph frame, LocalFlowGraph.LocalVertex call, AnalysisMethod target);

        /** The field usage site of a load on the string ({@code value(raw)}, {@code coder(raw)}, strict otherwise); null = no usage. */
        SugVertex fieldSite(LocalFlowGraph frame, LoadFieldNode lfn);

        /** The CLASS_CHECK usage site (the Phase-A {@code Object.getClass} shape) at {@code node}. */
        SugVertex classCheckSite(LocalFlowGraph frame, ValueNode node, String label);

        /**
         * The CLASS_CHECK usage site of method {@code ctx} at {@code bci} (a JDK model's class check at an internal
         * site: the same detached shape as {@link #classCheckSite}); null = no usage site (a test fixture).
         */
        default SugVertex classCheckSiteAt(com.oracle.graal.pointsto.meta.AnalysisMethod ctx, int bci, String label) {
            return null;
        }

        /** The arm-liveness filter: the usage at {@code anchor} observing {@code observed} is provably dead for {@code block}. */
        boolean armDead(LocalFlowGraph frame, Node anchor, ValueNode observed, ForwardFixpoint.Block block);

        /**
         * The same guard-feasibility table, uncounted ({@code ForwardFixpoint.armDeadDirection}): 0 = keep, 1 = dead (a
         * vacuous guard always succeeds), 2 = dead (a never guard always fails); also used at a Pi
         * ({@code RecursiveTracking.piArmDead}).
         */
        int armFeasibility(LocalFlowGraph frame, Node anchor, ValueNode observed, ForwardFixpoint.Block block);

        /** An exact InstanceOf that is a strict class check (not a source-shape fold, {@code LfgWalk.instanceofSourceFoldAllowed}). */
        boolean strictExactInstanceOf(LocalFlowGraph frame, InstanceOfNode ion);

        /** The concat recogniser at one invoke (memoised; {@link Concat#NONE} at a non-SCF site). */
        Concat concatAt(LocalFlowGraph frame, Invoke inv);

        /**
         * Print-only census: {@code [read failures, of which refused, readable non-indy opcodes, of which refused]}.
         */
        long[] concatUnreadable();

        /** The STRING atoms' block σ.block: the widened String cone, a constant. */
        ForwardFixpoint.Block stringBlock();

        /** {@code Object.toString()} (the desugared implicit call's declared target); null = unavailable. */
        AnalysisMethod objectToString();
    }
}
