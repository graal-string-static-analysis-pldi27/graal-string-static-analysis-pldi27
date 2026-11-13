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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

import com.oracle.graal.pointsto.heap.ImageHeapObjectArray;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.svm.hosted.phases.StringAnalysisChildInlining;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.LoadEntry;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Sink;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.CallPath;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.MethodContext;
import com.oracle.svm.hosted.stringanalysis.JdkModels.Alias;
import com.oracle.svm.hosted.stringanalysis.JdkModels.Callback;
import com.oracle.svm.hosted.stringanalysis.JdkModels.ClassCheck;
import com.oracle.svm.hosted.stringanalysis.JdkModels.Effect;
import com.oracle.svm.hosted.stringanalysis.JdkModels.Fresh;
import com.oracle.svm.hosted.stringanalysis.JdkModels.Ir;
import com.oracle.svm.hosted.stringanalysis.JdkModels.Observe;
import com.oracle.svm.hosted.stringanalysis.JdkModels.Ref;
import com.oracle.svm.hosted.stringanalysis.JdkModels.Store;
import com.oracle.svm.hosted.stringanalysis.JdkModels.Unmodelled;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.AtomKind;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.Counter;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtom;

import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.type.StampTool;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The engine side of the JDK models ({@link JdkModels}, the tables). A resolved target that an enabled family lists is
 * never entered: the {@link RecursiveTracking} crossings call into this class, which desugars the entry's effects into
 * the engine's own events ({@code recordStore} / {@code escapeInto} / {@code recordLoad} / {@code loadCase} / a
 * continuation at the call's result / a desugared call / a mint).
 * <p>
 * Every effect reads operands ({@link Operand}: an IR node of the call's frame or a callback {@link Temp}, followed by a
 * member chain), evaluated in a {@link View} (the real invoke, the op's argument slots, and where its result goes). A
 * member chain is a chain of model loads (forward) or the load case over the chain (backward), so write-through views,
 * bulk copies, element-receiver callbacks and re-dispatch into another model with any slot map are the same code;
 * {@code fresh C} mints a new atom of the JDK class C born at the call.
 * <p>
 * The rules it owns: the closed-class rule (an unlisted method of a closed class refuses by name), the implementor rule
 * (an unlisted {@code java.*} method implementing a method of a family's interface refuses by name, unless its class is
 * a family template), the field rule (an IR access to an abstracted field refuses by name), the reflection rule (a
 * family whose abstracted field is Unsafe-, reflection- or JNI-accessed is off for the image), the collapse key (one
 * application per family operation in a fan, forward, backward and in callbacks) and the census.
 * <p>
 * Determinism: every memo is a pure function of its key (the family flags are final after the points-to fixpoint); a
 * model load's continuation is part of the load entry's identity ({@link ModelLoad}: a value-equal {@link Chain}), so no
 * delivery can miss it; views, operands and temps are value records, so every derived sink root, listener key and fresh
 * site is a pure function of the call and the op.
 */
final class JdkModelEngine {
    /** Any family on: every hook is behind it (off = no JDK model applies). */
    static final boolean ON = JdkModels.anyEnabled();
    /** Some enabled family abstracts a field (F7 does not: the field rule is then skipped). */
    private static final boolean FIELDS = JdkModels.anyAbstracted();

    /**
     * Knob {@code fwd.jdkmodel.depth} (default 4): the re-dispatch depth bound (a callback into a model whose callback
     * reaches another model, ...); census {@code depth={d=n}}, refusals at the bound {@code redispatch-depth}.
     */
    static final int MAX_DEPTH = Integer.getInteger("svm.stringanalysis.fwd.jdkmodel.depth", 4);

    /** The one depth bound, on a callback's view (depth = the modelled call's view + 1), forward and backward. */
    private boolean overDepth(int callbackViewDepth) {
        RecursiveTracking.bump(depths, String.valueOf(Math.min(callbackViewDepth, MAX_DEPTH + 1)));
        return callbackViewDepth > MAX_DEPTH;
    }

    private static final Object NONE = new Object();
    /** A view whose result nobody reads (a callback without {@code ->}). */
    static final Object NO_RESULT = new Object() {
        @Override
        public String toString() {
            return "no-result";
        }
    };

    private final RecursiveTracking rt;
    /*
     * The memos, one map per key kind: a computation of one may consult the next (a method's model -> its family's
     * switch -> a name), and a ConcurrentHashMap must never be updated from inside its own computeIfAbsent.
     */
    /** A resolved method: its Op, a {@link Refused} (closed / implementor rule), or NONE. */
    private final Map<ResolvedJavaMethod, Object> methods = new ConcurrentHashMap<>();
    /** A field: the enabled family that abstracts it, or NONE. */
    private final Map<AnalysisField, Object> fields = new ConcurrentHashMap<>();
    /** A model name ("Class.field" / "Class#name(desc)" / a class): the AnalysisField / AnalysisMethod / AnalysisType, or NONE. */
    private final Map<String, Object> names = new ConcurrentHashMap<>();
    private final Map<JdkModels.Family, String> familyOff = new ConcurrentHashMap<>();
    private final Map<List<Object>, ModelCall> modelCalls = new ConcurrentHashMap<>();
    /** A callback site string: its JDK-internal invoke resolved ({@link Site}), or NONE. */
    private final Map<String, Object> sites = new ConcurrentHashMap<>();
    /** Fresh objects: the site of each (view, op), and the reverse map from the site vertex (the atom key's site). */
    private final Map<List<Object>, FreshSite> freshSites = new ConcurrentHashMap<>();
    private final Map<LocalFlowGraph.LocalVertex, FreshSite> freshByVertex = new ConcurrentHashMap<>();
    /** (a heap constant's type, a slot): whether an array representation field of the type fills the slot. */
    private final Map<List<Object>, Boolean> heapFilled = new ConcurrentHashMap<>();
    /** Census (print-only): per family, applications and refusals by kind. */
    private final Map<String, Counter> by = new ConcurrentHashMap<>();
    /** The callback views reached per depth (the {@code depth} knob's census). */
    private final Map<String, Counter> depths = new ConcurrentHashMap<>();
    private final Counter chainLoads = new Counter();

    JdkModelEngine(RecursiveTracking rt) {
        this.rt = rt;
    }

    // ------------------------------------------------------------------
    // Operands, views, marks
    // ------------------------------------------------------------------

    /** An operand's value: {@code base} (an IR node of the view's frame, or a {@link Temp}) and a resolved member chain. */
    record Operand(Object base, List<Object> members) {
        boolean plain() {
            return members.isEmpty();
        }

        /** The same operand followed by {@code more}. */
        Operand then(List<Object> more) {
            if (more.isEmpty()) {
                return this;
            }
            List<Object> m = new ArrayList<>(members);
            m.addAll(more);
            return new Operand(base, List.copyOf(m));
        }
    }

    /**
     * One application of an op: the real invoke (the position of every event), the op's argument slots as operands (the
     * invoke's arguments at depth 0; the callback's operands for a re-dispatched target), and where its result goes
     * (null = the invoke's result node; a {@link Temp}; {@link #NO_RESULT}).
     */
    record View(LocalFlowGraph frame, Invoke inv, List<Operand> args, Object result, int depth) {
        ValueNode node() {
            return (ValueNode) inv.asNode();
        }
    }

    /** A member name that does not resolve in the image (an operand holding it refuses by name). */
    private static final Object UNRESOLVED = new Object() {
        @Override
        public String toString() {
            return "<unresolved>";
        }
    };

    /** A callback argument {@code _} (a primitive or an untracked value): matches no atom; resolved backward, refused. */
    private static final Operand UNTRACKED = new Operand("untracked", List.of());

    /**
     * The value the callback {@code binder} of {@code op} returns at {@code view} (the temp {@code $}), or the fresh object
     * a {@code fresh C -> $k} binder creates there.
     */
    record Temp(View view, JdkModels.Op op, Effect binder) {
    }

    /**
     * The synthetic sink: the operand {@code S} of {@code op} at {@code view}, a consumer the modelled JDK code hands to a
     * callback; its {@code accept(x)} is the op's store {@code store o m S}. Forward, an atom a callback passes to
     * {@code S.accept} escapes there; backward, "what S accepts" is resolved through the callbacks that receive S. Never an
     * atom: no JDK class has instances with this behaviour, so an IR-walked callee that receives it (a user Spliterator)
     * cannot dispatch on it, and its resolution there refuses by name ({@code sink-object}).
     */
    record SinkRef(View view, JdkModels.Op op) {
    }

    /**
     * The node of a load entry a model records at a call: the call's node plus the {@link Chain} the arriving atom
     * continues. The mark is part of the entry's identity, so each mark is its own entry and delivery. Not an IR node: the
     * per-node pools never separate it.
     */
    record ModelLoad(ValueNode node, Object mark) {
    }

    /** An atom that arrives here is (after the {@code rest} members) the operand {@code role} of {@code effect} in {@code view}. */
    record Chain(View view, JdkModels.Op op, Effect effect, int role, List<Object> rest) {
    }

    /** The node of a store entry a model records (a table store at the call; the view and effect keep two stores apart). */
    record ModelStore(View view, Effect effect) {
    }

    /** A stored value "the value of {@code operand}" (a member chain: its elements), resolved backward at {@code at}. */
    record OperandValue(Operand operand, ValueNode at) {
    }

    /** A fresh object's site: its view, op and effect (the result or a temp), its class, and the site vertex (the atom key's site). */
    record FreshSite(View view, JdkModels.Op op, Fresh effect, AnalysisType type, boolean exact, LocalFlowGraph.LocalVertex vertex) {
    }

    /** Why an unlisted target refuses by name. */
    enum RefusalRule {
        CLOSED,
        IMPLEMENTOR,
        /** An op of a lazy family whose callback sites do not resolve (never walked as IR). */
        UNAPPLIED
    }

    /** An unlisted target that refuses by name: the closed-class rule or the implementor rule. */
    record Refused(JdkModels.Family family, RefusalRule rule) {
    }

    /**
     * A callback's JDK-internal invoke, resolved in the child's IR: the site method's frame, the invoke at the site's bci,
     * and its call vertex. A usage the callback produces is recorded here (the site the parent parses, the enclosing
     * method the whitelists read, the DC absence contract's site), never at the modelled call.
     */
    record Site(LocalFlowGraph frame, Invoke inv, LocalFlowGraph.LocalVertex vertex) {
    }

    /** Operand roles: the effect's {@code a}, STORE's value, callback argument k = {@code ARG + k}. */
    private static final int ROLE_A = 0;
    private static final int ROLE_V = 1;
    private static final int ROLE_ARG = 2;

    /** A synthetic call link for a model callback (the DesugaredCall precedent): its parameters are the view's operands. */
    static final class ModelCall {
        final Invoke inv;
        final View view;
        final Callback effect;
        final JdkModels.Family family;
        final LocalFlowGraph.LocalVertex descriptor;

        ModelCall(View view, Callback effect, JdkModels.Family family, LocalFlowGraph.LocalVertex descriptor) {
            this.inv = view.inv();
            this.view = view;
            this.effect = effect;
            this.family = family;
            this.descriptor = descriptor;
        }

        JdkModels.Family family() {
            return family;
        }

        @Override
        public String toString() {
            return "model-callback[" + inv.bci() + " " + effect.cb() + "]";
        }
    }

    // ------------------------------------------------------------------
    // The table side: pure, memoised lookups
    // ------------------------------------------------------------------

    /** The reflection rule: the family is off when one of its abstracted fields is Unsafe-, reflection- or JNI-accessed. */
    private boolean isOff(JdkModels.Family f) {
        String why = familyOff.get(f);
        if (why == null) {
            // computed outside the map's own computation (a required family is looked up recursively); a pure function
            // of the closed world, so a racing duplicate stores the same value
            familyOff.putIfAbsent(f, offReason(f));
            why = familyOff.get(f);
        }
        return !why.isEmpty();
    }

    /** Why the family is off for the image ("" = on): a required family off, or a flagged abstracted field. */
    private String offReason(JdkModels.Family fam) {
        for (String r : fam.requires) {
            JdkModels.Family rf = JdkModels.family(r);
            if (rf == null || !rf.enabled || isOff(rf)) {
                return "requires:" + r;
            }
        }
        for (String id : fam.abstracted.keySet()) {
            if (!(named(id) instanceof AnalysisField af)) {
                if (!(named(id.substring(0, id.lastIndexOf('.'))) instanceof AnalysisType)) {
                    continue; // a class absent from the image has no field any code could access
                }
                return "missing:" + id;
            }
            boolean flagged;
            try {
                // JNI registration sets neither flag (JNIAccessFeature.addField), so the registry is read too
                flagged = af.isUnsafeAccessed() || af.getAccessedReason() != null || rt.jniRegistered(af);
            } catch (Throwable t) {
                flagged = true;
            }
            if (flagged) {
                return "reflective:" + id;
            }
        }
        return "";
    }

    private Object methodModel(ResolvedJavaMethod m) {
        return methods.computeIfAbsent(m, k -> {
            JdkModels.Op op = JdkModels.lookup(m);
            if (op != null) {
                if (isOff(op.family())) {
                    return NONE;
                }
                if (JdkModels.hidesStringReceiver(op, m.isStatic(), m.isConstructor(), m.getDeclaringClass().toJavaName(true))) {
                    count(op.family(), "unapplied-string-receiver"); // the terminal rule keeps a String receiver's usage
                    return NONE;
                }
                for (Effect e : op.effects()) {
                    if (e instanceof ClassCheck cc && !classCheckSitesResolve(cc)) {
                        // A class check's site method is not in the image: the model does not apply (the IR is walked)
                        count(op.family(), "unapplied-site:" + op.method());
                        return NONE;
                    }
                    if (e instanceof Callback cb && !sitesResolve(cb, op.family().lazy)) {
                        // A callback's internal site is not in the child's IR: the model does not apply and the IR is
                        // walked; a lazy family's op is refused by name instead (no IR fallback into the stream machinery)
                        count(op.family(), "unapplied-site:" + op.method());
                        return op.family().lazy ? new Refused(op.family(), RefusalRule.UNAPPLIED) : NONE;
                    }
                }
                return op;
            }
            JdkModels.Family f = JdkModels.closedFamilyOf(m);
            if (f != null && !isOff(f)) {
                return new Refused(f, RefusalRule.CLOSED);
            }
            f = implementorFamily(m);
            return f != null ? new Refused(f, RefusalRule.IMPLEMENTOR) : NONE;
        });
    }

    /**
     * The implementor rule ("the unknown receiver"): an unlisted method declared by a {@code java.*} class that implements
     * a method of an enabled family's interface is the family's to list: it refuses by name, never walks the IR, unless
     * its class is one of the family's templates. So a fan over an interface method is the user targets (walked), the
     * modelled JDK targets (one application per collapse key) and named refusals: nothing else.
     */
    private JdkModels.Family implementorFamily(ResolvedJavaMethod m) {
        String cls;
        try {
            cls = m.getDeclaringClass().toJavaName();
            if (!cls.startsWith("java.") || m.isStatic() || m.isConstructor() || JdkModels.mentioned(cls)) {
                return null; // a class some family takes responsibility for is that family's (listed, closed or a template)
            }
        } catch (Throwable t) {
            return null; // a name that cannot be derived is not a java.* class of a family (the closed rule fails closed)
        }
        String nd = m.getName() + m.getSignature().toMethodDescriptor();
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            if (!f.enabled || f.interfaces.isEmpty() || isOff(f)) {
                continue;
            }
            for (String iname : f.interfaces) {
                if (named(iname) instanceof AnalysisType it && it.isAssignableFrom(m.getDeclaringClass()) && declares(it, nd, new HashSet<>())) {
                    return f;
                }
            }
        }
        return null;
    }

    private static boolean declares(ResolvedJavaType t, String nameDesc, Set<ResolvedJavaType> seen) {
        if (t == null || !seen.add(t)) {
            return false;
        }
        for (ResolvedJavaMethod dm : t.getDeclaredMethods(false)) {
            if ((dm.getName() + dm.getSignature().toMethodDescriptor()).equals(nameDesc)) {
                return true;
            }
        }
        for (ResolvedJavaType i : t.getInterfaces()) {
            if (declares(i, nameDesc, seen)) {
                return true;
            }
        }
        return false;
    }

    /** The op of a resolved target (null: not modelled, its family off, or no family on). */
    JdkModels.Op op(ResolvedJavaMethod m) {
        return ON && m != null && methodModel(m) instanceof JdkModels.Op op ? op : null;
    }

    /** The family whose closed class (or interface) makes the unlisted target {@code m} refuse by name, never the IR. */
    JdkModels.Family closedUnlisted(ResolvedJavaMethod m) {
        return ON && m != null && methodModel(m) instanceof Refused r ? r.family() : null;
    }

    /** The named refusal of an unlisted target ({@code side}: fwd, bwd, callback, reflective). */
    void refuseUnlisted(ContainerTables.Refusable target, JdkModels.Family f, ResolvedJavaMethod m, String side) {
        RefusalRule rule = methodModel(m) instanceof Refused r ? r.rule() : RefusalRule.CLOSED;
        String why = switch (rule) {
            case CLOSED -> "";
            case IMPLEMENTOR -> "implementor/";
            case UNAPPLIED -> "unapplied/";
        };
        unmodelled(target, f, why + side + "/" + m.format("%H.%n(%p)"));
    }

    /** The enabled family that abstracts the field {@code member}, or null (memoised; F7-only images skip the lookup). */
    private JdkModels.Family abstracting(Object member) {
        if (!FIELDS || !(member instanceof AnalysisField af)) {
            return null;
        }
        return fields.computeIfAbsent(af, k -> {
            JdkModels.Family f = JdkModels.abstractingFamily(af);
            if (f == null) {
                // A record component field (F6's collector record) is the family's too: every IR access other than the
                // commit translation (which runs first) refuses by the field rule, not by the incidental reflection flag
                f = JdkModels.recordFamily(af);
            }
            return f != null && !isOff(f) ? f : NONE;
        }) instanceof JdkModels.Family f ? f : null;
    }

    /** Is {@code member} a representation field of an enabled family (the field rule's test)? */
    boolean abstracted(Object member) {
        return abstracting(member) != null;
    }

    /**
     * The field rule: when {@code member} is a field an enabled family's slots abstract, refuse {@code target} by name
     * and return true (the caller drops the event). Every IR event that names a member calls it.
     */
    boolean fieldRule(ContainerTables.Refusable target, Object member, String why) {
        JdkModels.Family f = abstracting(member);
        if (f != null) {
            unmodelled(target, f, why + ":" + ((AnalysisField) member).format("%H.%n")); // the census names the field
        }
        return f != null;
    }

    /** The commit translation / the heap fill: an abstracted array representation's slot, else null (counted as {@code why}). */
    JdkModels.Slot representationSlot(Object member, String why) {
        JdkModels.Family f = abstracting(member);
        if (f == null) {
            return null;
        }
        JdkModels.Slot s = JdkModels.representationSlot((AnalysisField) member);
        if (s != null) {
            count(f, why);
        }
        return s;
    }

    /** (an AnalysisField) -> the record slot an enabled, on family models it as, or NONE (memoised). */
    private final Map<Object, Object> recordSlots = new ConcurrentHashMap<>();

    /**
     * F6: the slot standing for the record component field {@code member} ({@link JdkModels.Family#recordSlots}), or
     * null. An inlined record constructor's commit stores its components there (a null initial value is skipped), so the
     * reflection-registered real field is never a table member.
     */
    JdkModels.Slot recordSlot(Object member) {
        if (!ON || !(member instanceof AnalysisField af)) {
            return null;
        }
        Object r = recordSlots.computeIfAbsent(af, k -> {
            String id;
            try {
                id = af.getDeclaringClass().toJavaName() + "." + af.getName();
            } catch (Throwable t) {
                return NONE;
            }
            for (JdkModels.Family f : JdkModels.FAMILIES) {
                String sl = f.enabled ? f.recordSlots.get(id) : null;
                if (sl != null && !isOff(f)) {
                    count(f, "record-slot");
                    return JdkModels.slot(sl);
                }
            }
            return NONE;
        });
        return r instanceof JdkModels.Slot sl ? sl : null;
    }

    /** The commit translation's stored value: the elements of the representation array's initial value {@code array}. */
    Object repElements(ValueNode array) {
        return new OperandValue(new Operand(array, List.of(RecursiveTracking.ARRAY_ELEMENT)), array);
    }

    /**
     * Every site of a callback resolves; in a lazy family (the op's family's flag), at least one (an unresolved site is
     * unreachable code).
     */
    private boolean sitesResolve(Callback e, boolean lazy) {
        boolean any = false;
        for (String s : e.sites()) {
            boolean r = siteOf(s) instanceof Site;
            if (!r && !lazy) {
                return false;
            }
            any |= r;
        }
        return any;
    }

    /** Every site method of a class check resolves to an analysis method (its usage site's enclosing method). */
    private boolean classCheckSitesResolve(ClassCheck e) {
        for (String s : e.sites()) {
            if (!(named(Effect.siteMethod(s)) instanceof AnalysisMethod)) {
                return false;
            }
        }
        return true;
    }

    /** A callback's internal site (memoised per site; a pure function of the child's frames). */
    private Object siteOf(String site) {
        return sites.computeIfAbsent(site, k -> {
            String sm = Effect.siteMethod(site);
            if (!(named(sm) instanceof AnalysisMethod m)) {
                return NONE;
            }
            LocalFlowGraph f = rt.bridge.frameOf(m);
            List<ValueNode> invs = f != null ? rt.invokesByBci(f, Effect.siteBci(site)) : List.of();
            if (invs.size() != 1 || !(invs.get(0) instanceof Invoke inv) || inv.callTarget() == null || inv.callTarget().targetMethod() == null) {
                return NONE;
            }
            return new Site(f, inv, rt.callVertexOf(f, inv));
        });
    }

    /**
     * The resolved sites of a callback whose invoke calls the callback's name and descriptor (null: one does not);
     * {@code lazy}: an unresolved site is skipped. The invoke's symbolic holder must be the callback's class or a subclass
     * (the typed-out rule and the subclass hook trust that only receivers of the callback's class receive the call), else
     * null (a refusal).
     */
    private List<Site> sitesOf(Callback e, AnalysisMethod cb, boolean lazy) {
        List<Site> out = new ArrayList<>(e.sites().size());
        for (String s : e.sites()) {
            if (!(siteOf(s) instanceof Site site)) {
                if (lazy) {
                    continue; // a lazy family's unreachable site
                }
                return null;
            }
            ResolvedJavaMethod t = site.inv().callTarget().targetMethod();
            if (!t.getName().equals(cb.getName()) || !t.getSignature().toMethodDescriptor().equals(cb.getSignature().toMethodDescriptor())) {
                return null; // the invoke at that bci is not the callback's call
            }
            if (!cb.getDeclaringClass().isAssignableFrom(t.getDeclaringClass())) {
                return null; // the invoke's holder is no subtype of the callback's class
            }
            out.add(site);
        }
        return out;
    }

    /** A model name resolved: "Class.field", "Class#name(desc)" (constructors too) or a class name; NONE if not. */
    private Object named(String id) {
        return names.computeIfAbsent(id, k -> {
            int h = id.indexOf('#');
            if (h < 0 && !id.contains(".") || id.startsWith("[")) {
                AnalysisType t = rt.jdkType(id);
                return t != null ? t : NONE;
            }
            if (h < 0) {
                AnalysisType whole = rt.jdkType(id);
                if (whole != null) {
                    return whole; // a class name (an interface of a family)
                }
            }
            int dot = h < 0 ? id.lastIndexOf('.') : h;
            AnalysisType t = rt.jdkType(id.substring(0, dot));
            Object r;
            if (h < 0) {
                r = rt.declaredField(t, id.substring(dot + 1));
            } else {
                String name = id.substring(h + 1, id.indexOf('('));
                String desc = id.substring(id.indexOf('('));
                r = RecursiveTracking.declaredMethod(t, name, desc);
                if (r == null && t != null && !name.equals("<init>")) {
                    r = inheritedMethod(t, name, desc, new HashSet<>()); // a callback named by its call site's class (UnaryOperator#apply)
                }
                if (r == null && name.equals("<init>") && t != null) {
                    for (ResolvedJavaMethod c : t.getDeclaredConstructors(false)) {
                        if (c.getSignature().toMethodDescriptor().equals(desc)) {
                            r = c;
                        }
                    }
                }
            }
            if (r instanceof ResolvedJavaMethod m) {
                r = rt.bridge.resolveMethod(m);
            }
            return r != null ? r : NONE;
        });
    }

    /** A method declared by a supertype of {@code t} (superclasses first, then the interfaces), or null. */
    private static ResolvedJavaMethod inheritedMethod(ResolvedJavaType t, String name, String desc, Set<ResolvedJavaType> seen) {
        if (t == null || !seen.add(t)) {
            return null;
        }
        if (t instanceof AnalysisType at) {
            ResolvedJavaMethod m = RecursiveTracking.declaredMethod(at, name, desc);
            if (m != null) {
                return m;
            }
        }
        ResolvedJavaMethod m = inheritedMethod(t.getSuperclass(), name, desc, seen);
        for (ResolvedJavaType i : t.getInterfaces()) {
            m = m != null ? m : inheritedMethod(i, name, desc, seen);
        }
        return m;
    }

    /** A model member: a slot, {@code []}, or a real field named "Class.field" (null = unresolvable: the caller refuses). */
    private Object member(String name) {
        if (name.equals("[]")) {
            return RecursiveTracking.ARRAY_ELEMENT;
        }
        JdkModels.Slot s = JdkModels.slot(name);
        return s != null ? s : named(name) instanceof AnalysisField f ? f : null;
    }

    private void count(JdkModels.Family f, String what) {
        RecursiveTracking.bump(by, f.id + "." + what);
    }

    void unmodelled(ContainerTables.Refusable target, JdkModels.Family f, String why) {
        count(f, "unmodelled:" + why);
        rt.refuseAny(target, RTrackRefusal.JDK_MODEL_UNMODELLED);
    }

    /**
     * The unknown-receiver rule: the fan size counted against the CHA cap, where modelled targets with one collapse key
     * count once. A pure function of the list.
     */
    int collapsedCount(List<DispatchResolution.ResolvedTarget> targets) {
        if (!ON || targets.size() <= RecursiveTracking.CHA_CAP) {
            return targets.size();
        }
        Set<String> keys = new HashSet<>();
        int n = 0;
        for (DispatchResolution.ResolvedTarget t : targets) {
            JdkModels.Op op = op(t.method());
            if (op == null || keys.add(op.key())) {
                n++;
            }
        }
        return n;
    }

    /** Collapse inside one crossing: the first target of a key applies the op; a later one is skipped (counted). */
    boolean firstOfKey(Set<String> applied, JdkModels.Op op) {
        if (applied.add(op.key())) {
            return true;
        }
        count(op.family(), "collapsed");
        return false;
    }

    // ------------------------------------------------------------------
    // Views and operands
    // ------------------------------------------------------------------

    /** The modelled call itself: its arguments as plain operands, its result the invoke's result node. */
    private static View identityView(LocalFlowGraph frame, Invoke inv) {
        var args = inv.callTarget().arguments();
        List<Operand> ops = new ArrayList<>(args.size());
        for (ValueNode a : args) {
            ops.add(new Operand(a, List.of()));
        }
        return new View(frame, inv, List.copyOf(ops), null, 0);
    }

    /** The operand {@code r} in {@code view} (null: no such slot, or a view without that value); members may hold null (unresolvable). */
    private Operand operand(View view, JdkModels.Op op, Ref r) {
        Operand base;
        if (r.slot() == Ref.NONE) {
            return UNTRACKED; // `_`: no tracked value (never an atom's position)
        } else if (r.slot() == Ref.SINK) {
            return new Operand(new SinkRef(view, op), List.of()); // the op's sink (a value record: one per view and op)
        } else if (Ref.isTemp(r.slot())) {
            Effect b = op.tempBinder(Ref.tempIndex(r.slot()));
            base = b == null ? null : new Operand(new Temp(view, op, b), List.of());
        } else if (r.slot() == Ref.RESULT) {
            base = view.result() == null ? new Operand(view.node(), List.of()) : view.result() instanceof Temp t ? new Operand(t, List.of()) : null;
        } else {
            base = r.slot() < view.args().size() ? view.args().get(r.slot()) : null;
        }
        if (base == null || r.members().isEmpty()) {
            return base;
        }
        List<Object> ms = new ArrayList<>(r.members().size());
        for (String m : r.members()) {
            Object mo = member(m);
            ms.add(mo != null ? mo : UNRESOLVED);
        }
        return base.then(ms);
    }

    /** The operand's value as a table store's value: the node itself, or an {@link OperandValue}. */
    private static Object storedValue(View view, Operand o) {
        return o.plain() && o.base() instanceof ValueNode vn ? vn : new OperandValue(o, view.node());
    }

    // ------------------------------------------------------------------
    // Forward: the model at a call crossing
    // ------------------------------------------------------------------

    /** The walked atom's context at a model application (the IR slot entry needs the real target and the pushed path). */
    private record Fwd(RAtom atom, CallPath path, MethodContext mctx, CallPath pushed, AnalysisMethod target) {
    }

    /**
     * The forward application at a modelled target (the atom is argument node {@code n} of the call). Every slot that
     * holds the atom must be named by an effect; an unnamed slot refuses by name (a table gap is never silent).
     */
    void invokeUsage(RAtom atom, LocalFlowGraph frame, ValueNode n, MethodCallTargetNode ct, Invoke inv, AnalysisMethod target,
                    JdkModels.Op op, CallPath path, MethodContext mctx, CallPath pushed, int depth) {
        JdkModels.Family fam = op.family();
        count(fam, "fwd");
        if (RecursiveTracking.DUMP && RecursiveTracking.focused(String.valueOf(atom.key))) {
            System.out.println("[rtrack-dump] MODEL atom=" + atom.key + " at " + rt.frameName(frame) + "@" + inv.bci() + " op=" + op.method() + " " + op.effects());
        }
        apply(new Fwd(atom, path, mctx, pushed, target), identityView(frame, inv), op, new Operand(n, List.of()));
        var args = ct.arguments();
        for (int s = 0; s < args.size(); s++) {
            if (args.get(s) == n && !namesSlot(op, s)) {
                unmodelled(atom.table, fam, "slot" + s + ":" + op.method());
            }
        }
    }

    private static boolean namesSlot(JdkModels.Op op, int s) {
        for (Effect e : op.effects()) {
            if (JdkModels.namesSlot(e, s)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The atom is at position {@code p} of {@code view}: every effect operand that starts with {@code p} is reached,
     * directly or through a chain of model loads (the rest of the members are loaded from its table). Returns whether any
     * operand matched.
     */
    private boolean apply(Fwd fw, View view, JdkModels.Op op, Operand p) {
        boolean any = false;
        for (Effect e : op.effects()) {
            switch (e) {
                case Alias a -> any |= at(fw, view, op, e, ROLE_A, a.a(), p);
                case Ir ir -> any |= at(fw, view, op, e, ROLE_A, ir.a(), p);
                case Unmodelled u -> any |= at(fw, view, op, e, ROLE_A, u.a(), p);
                case ClassCheck cc -> any |= at(fw, view, op, e, ROLE_A, cc.a(), p);
                case Store st -> {
                    if (!ownedAtBirth(op, st.a())) {
                        any |= at(fw, view, op, e, ROLE_A, st.a(), p);
                    }
                    any |= at(fw, view, op, e, ROLE_V, st.v(), p);
                }
                case Callback c -> {
                    any |= at(fw, view, op, e, ROLE_A, c.a(), p);
                    for (int k = 0; k < c.cbArgs().size(); k++) {
                        any |= at(fw, view, op, e, ROLE_ARG + k, c.cbArgs().get(k), p);
                    }
                }
                case Observe o -> any |= o.a().slot() < view.args().size() && p.equals(view.args().get(o.a().slot()));
                case Fresh f -> {
                }
            }
        }
        return any;
    }

    /**
     * Is {@code r} rooted at an {@code ir} slot of {@code op}? Such a slot is wholly the IR's: an atom there enters the
     * real callee and no other effect applies to it (F6: a sink's receiver, whose re-dispatch callbacks are for the string
     * argument).
     */
    private static boolean irRooted(JdkModels.Op op, Effect e, Ref r) {
        if (e instanceof Ir || r.slot() < 0) {
            return false;
        }
        for (Effect x : op.effects()) {
            if (x instanceof Ir ir && ir.a().slot() == r.slot()) {
                return true;
            }
        }
        return false;
    }

    private boolean at(Fwd fw, View view, JdkModels.Op op, Effect e, int role, Ref r, Operand p) {
        return !irRooted(op, e, r) && at(fw, view, op, e, role, operand(view, op, r), p);
    }

    /** The store's owner is a fresh object of the op ({@code R} or a fresh temp): the store is an initial store, made at its birth. */
    private static boolean ownedAtBirth(JdkModels.Op op, Ref owner) {
        return owner.slot() == Ref.RESULT || Ref.isTemp(owner.slot()) && op.tempBinder(Ref.tempIndex(owner.slot())) instanceof Fresh;
    }

    private boolean at(Fwd fw, View view, JdkModels.Op op, Effect e, int role, Operand o, Operand p) {
        if (o == null || !o.base().equals(p.base()) || o.members().size() < p.members().size() || !o.members().subList(0, p.members().size()).equals(p.members())) {
            return false;
        }
        List<Object> rest = o.members().subList(p.members().size(), o.members().size());
        if (rest.contains(UNRESOLVED)) {
            unmodelled(fw.atom().table, op.family(), "member");
        } else if (rest.isEmpty()) {
            direct(fw, view, op, e, role);
        } else {
            chainLoads.incrementAndGet();
            rt.recordLoad(fw.atom(), view.frame(), new ModelLoad(view.node(), new Chain(view, op, e, role, List.copyOf(rest.subList(1, rest.size())))), rest.get(0), fw.path(), fw.mctx());
        }
        return true;
    }

    /** The atom IS operand {@code role} of effect {@code e}. */
    private void direct(Fwd fw, View view, JdkModels.Op op, Effect e, int role) {
        RAtom atom = fw.atom();
        JdkModels.Family fam = op.family();
        switch (e) {
            case Alias a -> continueAtResult(fw, view, fam);
            case Store st -> {
                Object m = member(st.member());
                if (m == null) {
                    unmodelled(atom.table, fam, "member");
                } else if (role == ROLE_A) {
                    Operand v = operand(view, op, st.v());
                    if (v == null || v.members().contains(UNRESOLVED)) {
                        unmodelled(atom.table, fam, "member");
                    } else {
                        rt.recordStore(atom, view.frame(), new ModelStore(view, e), storedValue(view, v), m, fw.path(), fw.mctx());
                    }
                } else {
                    if (atom.kind == AtomKind.STRING) {
                        atom.strEscapes.incrementAndGet(); // a store of the string (as escape(): the candidate line's counter)
                    }
                    escapeInto(fw, view, operand(view, op, st.a()), m, fam);
                }
            }
            case Callback c -> callback(fw, view, op, c, role);
            case Ir ir -> {
                if (view.depth() == 0 && fw.target() != null) {
                    enterParameter(atom, view.frame(), view.inv(), fw.target(), ir.a().slot(), fw.pushed(), fw.mctx(), "fwd-model");
                } else {
                    unmodelled(atom.table, fam, "redispatch-ir:" + op.method());
                }
            }
            case Unmodelled u -> unmodelled(atom.table, fam, "op:" + op.method());
            case ClassCheck cc -> classCheck(fw, view, op, cc);
            case Observe o -> {
            }
            case Fresh f -> {
            }
        }
    }

    /**
     * The atom is the operand of a class check: a string atom records the CLASS_CHECK usage at each site (the detached
     * {@code Object.getClass} site, as the IR walk's GetClass usage: no whitelist admits it); any other atom is observed.
     */
    private void classCheck(Fwd fw, View view, JdkModels.Op op, ClassCheck e) {
        RAtom atom = fw.atom();
        count(op.family(), "classcheck");
        if (atom.kind != AtomKind.STRING) {
            return;
        }
        Operand o = operand(view, op, e.a());
        ValueNode observed = o != null && o.plain() && o.base() instanceof ValueNode vn ? vn : null;
        for (String s : e.sites()) {
            if (!(named(Effect.siteMethod(s)) instanceof AnalysisMethod sm)) {
                unmodelled(atom.table, op.family(), "classcheck-site:" + s); // never silent (classCheckSitesResolve admitted the op)
                continue;
            }
            if (op.family().repInsensitiveClassChecks.contains(s)) {
                // String map keys: a class check that only orders a tree bin (the family declares the site):
                // no usage; the bin's results do not depend on the order (Family.repInsensitiveClassChecks)
                count(op.family(), "classcheck-repinsensitive");
                continue;
            }
            rt.strClassChecks.incrementAndGet();
            rt.strUsage(atom, view.frame(), view.node(), observed, rt.strSites.classCheckSiteAt(sm, Effect.siteBci(s), "getClass"), UsageRole.RECEIVER, -1);
        }
    }

    /** The atom is the view's result: the walk continues at the invoke's result, or at the temp's readers. */
    private void continueAtResult(Fwd fw, View view, JdkModels.Family fam) {
        Object r = view.result();
        if (r == null) {
            rt.enqueueWalk(fw.atom(), view.frame(), view.node(), fw.path(), fw.mctx());
        } else if (r instanceof Temp t) {
            apply(fw, t.view(), t.op(), new Operand(t, List.of()));
        } else {
            // a callback result the calling JDK code drops (no `->`: the premise JUnit proves the JDK code does not use
            // it): nothing flows on, for a re-dispatched model and an IR-walked target alike
            count(fam, "dropped-result");
        }
    }

    /** The atom escapes into {@code owner.member} (a plain node: the ordinary escape; a chain or a temp: its interned sink). */
    private void escapeInto(Fwd fw, View view, Operand owner, Object member, JdkModels.Family fam) {
        RAtom atom = fw.atom();
        RecursiveTracking.markStored(atom); // a model store of the string (also when the owner does not resolve)
        if (owner == null || owner.members().contains(UNRESOLVED)) {
            unmodelled(atom.table, fam, "member");
        } else if (owner.plain() && owner.base() instanceof ValueNode vn) {
            rt.escapeInto(atom, view.frame(), view.node(), vn, member, fw.path(), fw.mctx());
        } else {
            rt.closedField.escapeIntoKey(atom, view.frame(), view.node(), owner, s -> backwardOperand(view.frame(), owner, view.node(), fw.mctx(), fw.path(), s), member, fw.path(), fw.mctx());
        }
    }

    /** Enters callee {@code m} at parameter {@code slot} (slot 0 of an instance method: the receiver entry); false = no IR (refused or dead). */
    private boolean enterParameter(RAtom atom, LocalFlowGraph frame, Invoke inv, AnalysisMethod m, int slot, CallPath pushed, MethodContext mctx, String side) {
        LocalFlowGraph calleeFrame = rt.bridge.frameOf(m);
        StructuredGraph g = calleeFrame != null ? rt.graphOf(calleeFrame) : null;
        if (calleeFrame == null && rt.dropDeadTarget(m, side)) {
            return false;
        }
        if (calleeFrame == null || g == null) {
            rt.missingIr(side + "-callee", m);
            rt.refuse(atom.table, RTrackRefusal.MISSING_IR);
            return false;
        }
        if (slot == 0 && !m.isStatic()) {
            rt.enterReceiver(atom, calleeFrame, g, pushed, rt.enter(mctx, frame, inv, m, true, atom));
            return true;
        }
        ParameterNode param = g.getParameter(slot);
        if (param != null) {
            rt.enqueueWalk(atom, calleeFrame, param, pushed, rt.enter(mctx, frame, inv, m, false, atom));
        }
        return true;
    }

    /** An atom arriving at a model load entry {@code l} (see {@link ModelLoad}); false = not a model load. */
    boolean loadArrival(RAtom atom, LoadEntry l, MethodContext lm) {
        if (!ON || !(l.node() instanceof ModelLoad ml) || !(ml.mark() instanceof Chain c)) {
            return false;
        }
        Fwd fw = new Fwd(atom, l.path(), lm, null, null);
        if (c.rest().isEmpty()) {
            direct(fw, c.view(), c.op(), c.effect(), c.role());
        } else {
            rt.recordLoad(atom, l.frame(), new ModelLoad(ml.node(), new Chain(c.view(), c.op(), c.effect(), c.role(), List.copyOf(c.rest().subList(1, c.rest().size())))), c.rest().get(0), l.path(),
                            lm);
        }
        return true;
    }

    /** The declared type a callback's targets are resolved over: the receiver node's stamp, a field's type, or the callback's class. */
    private static AnalysisType receiverType(Operand recv, AnalysisMethod cb) {
        AnalysisType t = null;
        if (recv.plain() && recv.base() instanceof ValueNode vn && StampTool.typeOrNull(vn.stamp(NodeView.DEFAULT)) instanceof AnalysisType at) {
            t = at;
        } else if (!recv.plain() && recv.members().get(recv.members().size() - 1) instanceof AnalysisField f && f.getType() instanceof AnalysisType ft) {
            t = ft;
        }
        return t != null && cb.getDeclaringClass().isAssignableFrom(t) ? t : cb.getDeclaringClass();
    }

    /**
     * A model callback {@code a.cb(args)} at the modelled call, the atom being operand {@code role}: a desugared call whose
     * targets are the deterministic CHA of the callback over the receiver's declared type (for an element receiver a
     * field's type or the callback's class), with the block filter and the exact-receiver narrowing when the atom is the
     * receiver, collapsed against the CHA cap. Each target goes through the shared per-target rules
     * ({@code RecursiveTracking.targetCheck}): a modelled target applies its own model on the callback's operands
     * (re-dispatch); a thread-local operation or an unlisted closed-class or implementor method refuses by name; a monitor
     * operation's object slot is observed; a String atom at a terminal target is the terminal usage; anything else enters
     * the target's IR along a {@link ModelCall} link.
     * <p>
     * A string atom's usages are recorded at the callback's JDK-internal invokes (the effect's {@link Site}s): the
     * Phase-A adapter's RECEIVER / PARAMETER usages when an invoke has a Phase-A site, else the terminal usage at the
     * internal invoke's target site. The arm filter stays the caller's.
     */
    private void callback(Fwd fw, View view, JdkModels.Op op, Callback e, int role) {
        RAtom atom = fw.atom();
        JdkModels.Family fam = op.family();
        Object cbm = named(e.cb());
        List<Site> ss = cbm instanceof AnalysisMethod cb0 ? sitesOf(e, cb0, op.family().lazy) : null;
        Operand recv = operand(view, op, e.a());
        if (!(cbm instanceof AnalysisMethod cb) || ss == null || recv == null || recv.members().contains(UNRESOLVED)) {
            unmodelled(atom.table, fam, "callback:" + e.cb());
            return;
        }
        List<Operand> cargs = new ArrayList<>();
        cargs.add(recv);
        for (Ref r : e.cbArgs()) {
            Operand o = operand(view, op, r);
            if (o == null || o.members().contains(UNRESOLVED)) {
                unmodelled(atom.table, fam, "callback-arg:" + e.cb());
                return;
            }
            cargs.add(o);
        }
        boolean atRecv = role == ROLE_A;
        int argK = atRecv ? -1 : role - ROLE_ARG;
        boolean staticCb = cb.isStatic(); // a static callback: `a` is its parameter 0, the arguments 1.. (or `_`)
        if (atRecv && !staticCb) {
            AnalysisType ex = rt.atomExactTypeOf(atom.key);
            if (ex != null && !canReceive(ex, cb)) {
                // The JDK makes this virtual call only on receivers of the callback's class (a LinkedHashMap's
                // eviction hook inside HashMap.put): an atom of another exact class never receives it (no flow, no refusal)
                count(fam, "callback-typed-out");
                return;
            }
        }
        ValueNode invNode = view.node();
        ValueNode observed = cargs.get(atRecv ? 0 : argK + 1).plain() && cargs.get(atRecv ? 0 : argK + 1).base() instanceof ValueNode vn ? vn : null;
        boolean str = atom.kind == AtomKind.STRING;
        boolean anyPhaseA = false;
        boolean allPhaseA = !ss.isEmpty(); // every internal site has a SUG vertex (the equals matrix sees them all)
        // ... and every one is a vertex the REDIRECT rule marks (EqualsMatrixHeuristic.redirectableArgSite)
        boolean allEqSites = allPhaseA;
        boolean allCmpSites = allPhaseA;
        if (str) {
            for (Site site : ss) {
                SugVertex phaseA = rt.strSites.phaseACallSite(site.frame(), site.inv());
                if (phaseA == null) {
                    allPhaseA = false;
                    allEqSites = false;
                    allCmpSites = false;
                    continue;
                }
                anyPhaseA = true;
                allEqSites &= EqualsMatrixHeuristic.redirectableArgSite(phaseA, false);
                allCmpSites &= EqualsMatrixHeuristic.redirectableArgSite(phaseA, true);
                // the adapter's usages at the internal invoke (RECEIVER at its receiver, PARAMETER at its argument k + 1)
                boolean strict = SugNameTables.isStrictClassCheckName(phaseA.getMethodName(), phaseA.getDeclaringClass());
                rt.strPhaseAUsages.incrementAndGet();
                if (staticCb) {
                    // A static call's arguments are its parameters 0.. (the adapter's PARAMETER usage with that slot)
                    int slot = atRecv ? 0 : argK + 1;
                    rt.strUsage(atom, view.frame(), invNode, observed, phaseA, strict ? UsageRole.RECEIVER : UsageRole.PARAMETER, strict ? -1 : slot);
                } else if (atRecv) {
                    // A tracked accumulator as the receiver: its own method (RecursiveTracking.accDispatchOwner)
                    rt.strUsage(atom, view.frame(), invNode, observed, phaseA, UsageRole.RECEIVER, -1,
                                    rt.accDispatchOwner(atom, phaseA, site.inv().callTarget().targetMethod()));
                } else {
                    rt.strUsage(atom, view.frame(), invNode, observed, phaseA, strict ? UsageRole.RECEIVER : UsageRole.PARAMETER, strict ? -1 : argK + 1);
                }
            }
        }
        if (recv.base() instanceof SinkRef sr) {
            sinkAccept(fw, sr, e, role); // a call ON the sink (its accept), after the usages at the internal sites
            return;
        }
        View cv = new View(view.frame(), view.inv(), List.copyOf(cargs), cvResult(view, op, e), view.depth() + 1); // the shared helper
        List<DispatchResolution.ResolvedTarget> targets = staticCb ? staticTarget(cb) : rt.chaTargets(cb, receiverType(recv, cb), atRecv ? rt.atomSiteBlock(atom) : null);
        count(fam, "callback");
        ModelCall mc = modelCall(cv, e, fam, cb);
        CallPath pushed = CallPath.push(view.frame(), mc, fw.mctx(), fw.path());
        Set<String> applied = ConcurrentHashMap.newKeySet();
        Set<Object> started = ConcurrentHashMap.newKeySet();
        CbCall c = new CbCall(fw, cv, e, fam, cargs, ss, atRecv, argK, observed, anyPhaseA, str && allPhaseA, str && allEqSites, str && allCmpSites, pushed, applied, started);
        if (!atRecv && !staticCb && str && !e.sites().isEmpty() && fam.sameClassCallbacks.containsAll(e.sites())) {
            AnalysisType st = rt.jdkType("java.lang.String");
            if (st != null && cb.getDeclaringClass().isAssignableFrom(st)) {
                // A same-class callback (Family.sameClassCallbacks): the receiver is of the string argument's own
                // class, so the targets are the callback's resolution over the String cone (the atom's block)
                count(fam, "callback-sameclass");
                callbackTargets(c, rt.chaTargets(cb, st, rt.atomSiteBlock(atom)));
                return;
            }
        }
        if (!atRecv && (!(recv.plain() && recv.base() instanceof ValueNode) || hookOnSubtype(recv, cb)) && targets.size() > 1) {
            // The atom is an argument of a callback whose receiver is an element / field value (a wrapper's delegate):
            // the targets follow the receiver's atoms, never a CHA fan; a refused receiver refuses the atom
            perReceiverAtom("mcb-fwd", view, recv, fw.mctx(), fw.path(), List.of("mcbf", atom.key, cv, e, role), cb, targets, sel -> callbackTargets(c, sel), atom.table);
            return;
        }
        if (!atRecv && !staticCb && fanRefusal(targets) != null) {
            // A plain receiver whose CHA fan refuses anyway: select per receiver through the typed sink (a final-typed
            // value, e.g. a String, stops the backward walk at once)
            count(fam, "callback-plain-typed");
            perReceiverAtom("mcb-fwd", view, recv, fw.mctx(), fw.path(), List.of("mcbf-p", atom.key, cv, e, role), cb, targets, sel -> callbackTargets(c, sel), atom.table);
            return;
        }
        if (atRecv && targets.size() > 1) {
            List<DispatchResolution.ResolvedTarget> exact = rt.exactReceiverTargetsOf(atom, cb, targets);
            if (exact != null) {
                rt.exactRecvNarrowed.incrementAndGet();
                targets = exact;
            }
        }
        callbackTargets(c, targets);
    }

    /** The one target of a static callback (the method itself: no dispatch, no receiver). */
    private List<DispatchResolution.ResolvedTarget> staticTarget(AnalysisMethod cb) {
        return List.of(new DispatchResolution.ResolvedTarget(cb, rt.bridge.frameOf(cb), null, true, cb.getDeclaringClass() != null ? cb.getDeclaringClass().toJavaName(true) : ""));
    }

    /**
     * A callback on a plain receiver whose static type is no subtype of the callback's class (a subclass hook:
     * {@code LinkedHashMap.removeEldestEntry} inside {@code HashMap.put}): a CHA fan over the callback's class would hand
     * the atom to every override although most receivers are no instance of that class, so the targets follow the
     * receiver's atoms instead ({@link #perReceiverAtom}).
     */
    private static boolean hookOnSubtype(Operand recv, AnalysisMethod cb) {
        return recv.plain() && recv.base() instanceof ValueNode vn && StampTool.typeOrNull(vn.stamp(NodeView.DEFAULT)) instanceof AnalysisType at &&
                        !canReceive(at, cb);
    }

    /** The subtype test of the typed-out rule and the subclass hook: can a receiver of type {@code t} receive {@code cb}? */
    private static boolean canReceive(AnalysisType t, AnalysisMethod cb) {
        return cb.getDeclaringClass().isAssignableFrom(t);
    }

    /**
     * The atom is argument k of a callback on the sink {@code sr}: {@code accept(x)} puts x where the sink's store says (x
     * escapes into the store's owner, in the sink's own view); any other call on a sink, or the atom as its receiver,
     * refuses by name.
     */
    private void sinkAccept(Fwd fw, SinkRef sr, Callback e, int role) {
        RAtom atom = fw.atom();
        Store target = sr.op().sinkStore();
        JdkModels.Family fam = sr.op().family();
        Object m = target == null ? null : member(target.member());
        if (role < ROLE_ARG || !isAccept(e) || m == null) {
            unmodelled(atom.table, fam, "sink-callback:" + e.cb());
            return;
        }
        count(fam, "sink-accept");
        if (atom.kind == AtomKind.STRING) {
            atom.strEscapes.incrementAndGet(); // a store of the string (as the store effect's escape)
        }
        escapeInto(fw, sr.view(), operand(sr.view(), sr.op(), target.a()), m, fam);
    }

    private static boolean passesSink(List<Operand> cargs) {
        for (Operand o : cargs) {
            if (o.base() instanceof SinkRef) {
                return true;
            }
        }
        return false;
    }

    /** A sink's one operation: {@code accept(Object)} with one argument (a Consumer's; the stream Sink's reference accept). */
    private static boolean isAccept(Callback e) {
        return e.cbArgs().size() == 1 && e.cb().endsWith("#accept(Ljava/lang/Object;)V");
    }

    /** One forward model callback in progress (the per-target loop may run once per receiver atom: its sets dedupe). */
    private record CbCall(Fwd fw, View cv, Callback e, JdkModels.Family fam, List<Operand> cargs, List<Site> sites, boolean atRecv, int argK, ValueNode observed,
                    boolean anyPhaseA, boolean allPhaseA, boolean allEqSites, boolean allCmpSites, CallPath pushed, Set<String> applied, Set<Object> started) {
    }

    /**
     * The receiver-atom selector, forward and backward: the targets a receiver of exact type {@code exact} dispatches to
     * among {@code fan}; a receiver of unknown type (a String, an inexact fresh object, a non-exact birth) or a type the
     * rule doubts ({@code dispatch} = null) selects the whole fan, never nothing. Pure; pinned by a unit test.
     */
    static <T, R> List<T> receiverSelection(R exact, Function<R, List<T>> dispatch, List<T> fan) {
        List<T> sel = exact == null ? null : dispatch.apply(exact);
        return sel != null ? sel : fan;
    }

    /**
     * Runs {@code leaf} once per atom of the receiver operand {@code recv} with the targets that atom selects
     * ({@link #receiverSelection}); a refused receiver refuses {@code onRefusal} (no fan). Shared by {@code mcb-fwd},
     * {@code mcb-recv} and {@code mcb-sink}.
     */
    private void perReceiverAtom(String kind, View view, Operand recv, MethodContext mctx, CallPath path, List<Object> listenerKey, AnalysisMethod cb,
                    List<DispatchResolution.ResolvedTarget> fan, java.util.function.Consumer<List<DispatchResolution.ResolvedTarget>> leaf, ContainerTables.Refusable onRefusal) {
        // Typed receiver: a type-only sink of its own root; see RecursiveTracking.TypedRecvKey
        Object rootKey = new RecursiveTracking.TypedRecvKey(recv);
        rt.attachOperandSink(kind, view.frame(), rootKey, sk -> backwardOperand(view.frame(), recv, view.node(), mctx, path, sk), mctx, path, listenerKey,
                        key -> {
                            if (key instanceof RecursiveTracking.TypeToken tt) {
                                // a receiver known only by its final stamp type: the callback's CHA over that type
                                if (!cb.getDeclaringClass().isAssignableFrom(tt.type())) {
                                    RecursiveTracking.bump(by, kind + "-typed-out");
                                    return;
                                }
                                RecursiveTracking.bump(by, kind + "-typetoken");
                                leaf.accept(rt.chaTargets(cb, tt.type(), null));
                                return;
                            }
                            ForwardFixpoint.Block sb = rt.stringAtomBlockOf(key);
                            AnalysisType st = sb != null ? rt.jdkType("java.lang.String") : null;
                            if (st != null && cb.getDeclaringClass().isAssignableFrom(st)) {
                                // a string atom receiver: its class is in the String cone (the same-class rule)
                                RecursiveTracking.bump(by, kind + "-stringrecv");
                                leaf.accept(rt.chaTargets(cb, st, sb));
                                return;
                            }
                            AnalysisType ex = rt.atomExactTypeOf(key);
                            if (ex != null && !canReceive(ex, cb)) {
                                RecursiveTracking.bump(by, kind + "-typed-out"); // a receiver of another exact class receives no call
                                return;
                            }
                            leaf.accept(receiverSelection(ex, (AnalysisType t) -> DispatchResolution.receiverDispatchTargets(List.of(t), cb, fan), fan));
                        },
                        r -> rt.refuseAny(onRefusal, r), onRefusal);
    }

    /** The cap rule of a callback fan: NO_TARGET / CHA_FAN_CAP (a collapsed fan counts each family operation once), or null. */
    private RTrackRefusal fanRefusal(List<DispatchResolution.ResolvedTarget> targets) {
        return StringAtoms.desugaredTargetRefusal(targets.size() > RecursiveTracking.CHA_CAP ? collapsedCount(targets) : targets.size(), RecursiveTracking.CHA_CAP);
    }

    /**
     * The shared per-target rule of a model callback, forward and backward: a thread-local operation or an unlisted
     * closed-class / implementor method refuses {@code target} by name (null); otherwise the target's check.
     */
    private RecursiveTracking.TargetCheck callbackRule(AnalysisMethod m, ContainerTables.Refusable target, String side) {
        RecursiveTracking.TargetCheck tc = rt.targetCheck(m);
        switch (tc.rule()) {
            case THREAD_LOCAL -> {
                rt.threadLocal.tlUnmodelled(target, "model-callback-tl-op");
                return null;
            }
            case CLOSED -> {
                refuseUnlisted(target, tc.closed(), m, side);
                return null;
            }
            default -> {
                return tc;
            }
        }
    }

    /** The per-target rules of a forward model callback over {@code targets} (the collapsed fan is capped). */
    private void callbackTargets(CbCall c, List<DispatchResolution.ResolvedTarget> targets) {
        Fwd fw = c.fw();
        RAtom atom = fw.atom();
        View cv = c.cv();
        JdkModels.Family fam = c.fam();
        RTrackRefusal targetRefusal = fanRefusal(targets);
        if (targetRefusal != null) {
            rt.refuse(atom.table, targetRefusal);
            return;
        }
        boolean str = atom.kind == AtomKind.STRING;
        ValueNode invNode = cv.node();
        for (DispatchResolution.ResolvedTarget t : targets) {
            AnalysisMethod m = t.method();
            if (!c.started().add(m)) {
                continue;
            }
            if (!c.atRecv() && str && mirrorCallbackArgument(c, m)) {
                continue; // builder-append mirror: terminal at every (mirrorable) internal site, or refused; never entered
            }
            RecursiveTracking.TargetCheck tc = callbackRule(m, atom.table, "callback");
            if (tc == null) {
                continue;
            }
            if (tc.rule() == RecursiveTracking.TargetRule.MODEL && !(c.atRecv() && StringAtoms.isTerminalTarget(m))) {
                // forward re-dispatch: the target's own model on the callback's operands; never for the receiver of a
                // terminal target (the terminal rule for a String receiver, the IR for any other, as at the invoke crossing)
                if (firstOfKey(c.applied(), tc.op())) {
                    if (overDepth(cv.depth())) {
                        unmodelled(atom.table, fam, "redispatch-depth:" + tc.op().method());
                    } else {
                        count(fam, "redispatch");
                        if (!apply(new Fwd(atom, fw.path(), fw.mctx(), null, null), cv, tc.op(), c.cargs().get(c.atRecv() ? 0 : c.argK() + 1))) {
                            unmodelled(atom.table, tc.op().family(), "redispatch-slot:" + tc.op().method());
                        }
                    }
                }
                continue;
            }
            // the forward IR leaf
            if (passesSink(c.cargs())) {
                // The callback hands the sink to an IR-walked callee (a user Spliterator / Iterator): the sink has no atom
                // there, so what it accepts is unknown; the atom (the traversed object) refuses by name
                unmodelled(atom.table, fam, "sink-ir:" + m.format("%H.%n(%p)"));
                continue;
            }
            boolean monitorOp = tc.rule() == RecursiveTracking.TargetRule.MONITOR;
            boolean terminal = c.atRecv() && str && StringAtoms.isTerminalTarget(m);
            if (terminal) {
                rt.strTerminals.incrementAndGet();
                if (!c.anyPhaseA()) {
                    for (Site site : c.sites()) {
                        SugVertex ts = rt.strSites.targetSite(site.frame(), site.vertex(), m);
                        rt.strUsage(atom, cv.frame(), invNode, c.observed(), ts, UsageRole.RECEIVER, -1, rt.accDispatchOwner(atom, ts, site.inv().callTarget().targetMethod())); // accumulator dispatch
                                                                                                                                                                                 // owner
                    }
                }
                rt.cmpBridgeReceiver(atom, cv.frame(), invNode, c.observed(), m); // the bridge's internal site
                if (c.e().bind() != JdkModels.BIND_NONE && StringAtoms.continuesAtResult(m)) {
                    rt.strListContinuations.incrementAndGet();
                    continueAtResult(fw, cv, fam);
                }
                continue;
            }
            StringAtoms.EqArgRow eqRow = c.atRecv() ? StringAtoms.EqArgRow.NONE
                            : StringAtoms.equalsArgRow(str, c.argK() + 1, StringAtoms.isStringEquals(m), c.allEqSites());
            if (!c.atRecv() && c.allPhaseA() && (eqRow == StringAtoms.EqArgRow.NO_SITE || !c.allCmpSites() && StringAtoms.compareToArgRow(str, c.argK() + 1,
                            StringAtoms.isStringCompareToString(m), StringAtoms.isStringCompareToBridge(m), true) == StringAtoms.CmpArgRow.TERMINAL)) {
                rt.argSiteNotRedirectable.incrementAndGet(); // an internal Phase-A vertex the REDIRECT rule would not mark
            }
            if (c.atRecv()) {
                if (!(monitorOp && MonitorPrimitive.OBJECT_SLOT == 0)) {
                    enterParameter(atom, cv.frame(), cv.inv(), m, 0, c.pushed(), fw.mctx(), "fwd-callback");
                }
            } else if (monitorOp && MonitorPrimitive.OBJECT_SLOT == c.argK() + 1) {
                rt.monitorObservations.incrementAndGet(); // a monitor operation's object slot is observed
            } else if (eqRow == StringAtoms.EqArgRow.TERMINAL) {
                rt.eqArgTerminals.incrementAndGet(); // the PARAMETER usage at every internal site (recorded above)
            } else if (eqRow == StringAtoms.EqArgRow.NO_SITE) {
                rt.eqArgNoSite.incrementAndGet(); // an internal site without a SUG vertex could not be REDIRECTed
                rt.refuse(atom.table, RTrackRefusal.EQUALS_ARG_NO_SITE);
            } else if (rt.cmpArgument(atom, cv.frame(), invNode, c.observed(), m, str, c.argK() + 1, c.allCmpSites())) {
                // Site-keyed (as the equals argument): every internal site has a Phase-A vertex (the
                // adapter's usages recorded above), or the bridge's internal site, or refused; never entered
            } else {
                enterParameter(atom, cv.frame(), cv.inv(), m, c.argK() + 1, c.pushed(), fw.mctx(), "fwd-callback");
            }
        }
    }

    /**
     * The builder-append mirror ({@link StringAtoms#mirrorArgRow}) at a forward callback whose target {@code m} is a
     * builder entry point and whose argument {@code argK} is the entry's string slot: TERMINAL when every internal site has
     * a mirrorable Phase-A vertex ({@link AppendMirror#mirrorSite}), each site recorded for its MIRROR line; otherwise
     * NO_SITE (refused {@code MIRROR_ARG_NO_SITE}). True when the target is consumed.
     */
    private boolean mirrorCallbackArgument(CbCall c, AnalysisMethod m) {
        int entrySlot = AppendMirror.stringSlot(m);
        if (!AppendMirror.on() || entrySlot < 0 || c.argK() + 1 != entrySlot) {
            return false;
        }
        List<SugVertex> vs = new ArrayList<>();
        boolean all = c.allPhaseA();
        for (Site site : c.sites()) {
            if (!all) {
                break;
            }
            SugVertex v = AppendMirror.mirrorSite(rt.strSites.phaseACallSite(site.frame(), site.inv()), site.inv());
            all = v != null;
            vs.add(v);
        }
        switch (StringAtoms.mirrorArgRow(true, true, entrySlot, entrySlot, all)) {
            case TERMINAL:
                for (int i = 0; i < vs.size(); i++) {
                    AppendMirror.recordTerminal(vs.get(i), c.sites().get(i).inv().callTarget().targetMethod());
                }
                return true;
            case NO_SITE:
                AppendMirror.recordNoSite(m);
                rt.refuse(c.fw().atom().table, RTrackRefusal.MIRROR_ARG_NO_SITE);
                return true;
            default:
                return false;
        }
    }

    private ModelCall modelCall(View cv, Callback e, JdkModels.Family fam, AnalysisMethod cb) {
        return modelCalls.computeIfAbsent(List.of(cv, e, fam.id), k -> {
            LocalFlowGraph.LocalVertex d = new LocalFlowGraph.LocalVertex(cv.frame(), -1, LocalFlowGraph.VertexKind.INVOKE_CALLSITE);
            d.bci = StringAnalysisChildInlining.pointsToBci(cv.inv());
            d.calleeMethod = cb;
            d.label = "model-callback";
            return new ModelCall(cv, e, fam, d);
        });
    }

    /** A return arriving along {@code p}: a model callback's result goes where the callback binds it (true), or not a model link (false). */
    boolean returnArrival(RAtom atom, CallPath p) {
        if (p == null || !(p.call instanceof ModelCall mc)) {
            return false;
        }
        MethodContext mctx = RecursiveTracking.restored(p.callerMctx);
        // A callback without `->` whose IR-walked target returns a reference drops the value, as a re-dispatched model's
        // ("dropped-result"): the premise JUnit reports every tracked use of a callback's result as an undeclared effect.
        continueAtResult(new Fwd(atom, p.next, mctx, null, null), mc.view, mc.family());
        return true;
    }

    // ------------------------------------------------------------------
    // Fresh: an object the model creates, born at the call with its real JDK class
    // ------------------------------------------------------------------

    /** Mints the fresh object {@code fe} of the op at {@code view} into {@code sink} (the call's result, or the temp it binds). */
    private void mintFresh(View view, JdkModels.Op op, Fresh fe, MethodContext mctx, CallPath path, Sink sink) {
        FreshSite fs = freshSite(view, op, fe);
        if (fs == null) {
            unmodelled(sink, op.family(), "fresh-class:" + fe.fresh());
            return;
        }
        count(op.family(), "fresh");
        rt.contextsAndMint(view.frame(), view.node(), mctx, path, sink, fs.vertex());
    }

    // ------------------------------------------------------------------
    // The fresh container of an element-source call (the ELEM seed)
    // ------------------------------------------------------------------

    /** The element-source ops: a fresh stream head (F4) / a fresh String[] (counted under F1); no other effect. */
    private static final Map<ElementSources.Kind, JdkModels.Op> ELEMENT_OPS = Map.of(
                    ElementSources.Kind.STREAM, JdkModels.parse(JdkModels.F4, "c97.elem#stream() : fresh java.util.stream.ReferencePipeline$Head"),
                    ElementSources.Kind.ARRAY, JdkModels.parse(JdkModels.F1, "c97.elem#array() : fresh [Ljava.lang.String;"));

    /** A fresh site's initial element store: {@code member := } the ELEM seed's string atom. */
    record ElementStore(Object member, Object atomKey, LocalFlowGraph.LocalVertex site) {
    }

    private final Map<LocalFlowGraph.LocalVertex, ElementStore> elementStores = new ConcurrentHashMap<>();

    /** The container member that holds the elements of a {@code kind} row: the stream head's {@code <elem>}, an array's {@code []}. */
    Object elementMember(ElementSources.Kind kind) {
        return kind == null ? null : kind == ElementSources.Kind.STREAM ? JdkModels.slot("<elem>") : RecursiveTracking.ARRAY_ELEMENT;
    }

    /** Whether a {@code kind} row can be placed: fresh minting needs the engine on; a stream needs F4 active for the image. */
    boolean elementSourceActive(ElementSources.Kind kind) {
        if (!ON || kind == null) {
            return false;
        }
        return kind != ElementSources.Kind.STREAM || JdkModels.F4.enabled && !isOff(JdkModels.F4);
    }

    /**
     * Mints the fresh container of an element-source call {@code inv} into {@code sink}; its birth ({@link #freshBirth})
     * records the initial store {@code member := strAtom} and starts its walk at the call's result.
     */
    void mintElementSource(LocalFlowGraph frame, Invoke inv, ElementSources.Kind kind, RAtom strAtom, Sink sink) {
        JdkModels.Op op = ELEMENT_OPS.get(kind);
        View view = identityView(frame, inv);
        FreshSite fs = freshSite(view, op, op.fresh());
        if (fs == null) {
            unmodelled(sink, op.family(), "fresh-class:" + op.fresh().fresh());
            return;
        }
        elementStores.putIfAbsent(fs.vertex(), new ElementStore(elementMember(kind), strAtom.key, fs.vertex()));
        count(op.family(), "elem-fresh");
        rt.contextsAndMint(view.frame(), view.node(), MethodContext.UNKNOWN, null, sink, fs.vertex());
    }

    /** The fresh site of {@code fe} at {@code view} (one per view, op and effect), or null when its class does not resolve. */
    private FreshSite freshSite(View view, JdkModels.Op op, Fresh fe) {
        if (!(named(fe.fresh()) instanceof AnalysisType t)) {
            return null;
        }
        return freshSites.computeIfAbsent(List.of(view, op.method(), fe), k -> {
            LocalFlowGraph.LocalVertex v = new LocalFlowGraph.LocalVertex(view.frame(), -1, LocalFlowGraph.VertexKind.INTERNAL);
            v.label = t.isArray() ? "new-array" : "new-instance";
            v.irNode = view.node();
            v.declaredType = fe.exact() ? t : null; // an inexact class: no identity type (block TOP, no exact narrowing)
            FreshSite s = new FreshSite(view, op, fe, t, fe.exact(), v);
            freshByVertex.put(v, s);
            return s;
        });
    }

    /** The exact class of a fresh atom (null: not fresh, or inexact). */
    AnalysisType freshExactType(RAtom atom) {
        FreshSite fs = ON && atom.key.site instanceof LocalFlowGraph.LocalVertex v ? freshByVertex.get(v) : null;
        return fs != null && fs.exact() ? fs.type() : null;
    }

    /** Is the atom fresh (its birth is a model call, not an allocation)? */
    boolean isFresh(RAtom atom) {
        return ON && atom.key.site instanceof LocalFlowGraph.LocalVertex v && freshByVertex.containsKey(v);
    }

    /** The owner slot of fresh {@code fe}'s initial stores: {@code R}, or the temp it binds. */
    private static int freshOwner(Fresh fe) {
        return fe.bind() == JdkModels.BIND_RESULT ? Ref.RESULT : Ref.TEMP - (fe.bind() - JdkModels.BIND_TEMP);
    }

    /**
     * A fresh atom's birth under {@code mctx}: its initial stores (the op's {@code store R ...} / {@code store $k ...}
     * effects) and the start of its walk: a result at the view's result, and the op's own effects that read it (a
     * callback's receiver or argument, a stored value). False: not a fresh atom.
     */
    boolean freshBirth(RAtom atom, MethodContext mctx) {
        FreshSite fs = ON && atom.key.site instanceof LocalFlowGraph.LocalVertex v ? freshByVertex.get(v) : null;
        if (fs == null) {
            return false;
        }
        View view = fs.view();
        JdkModels.Op op = fs.op();
        int owner = freshOwner(fs.effect());
        for (Effect e : op.effects()) {
            if (!(e instanceof Store st) || st.a().slot() != owner) {
                continue;
            }
            Object m = member(st.member());
            Operand v = operand(view, op, st.v());
            if (m == null || !st.a().members().isEmpty() || v == null || v.members().contains(UNRESOLVED)) {
                unmodelled(atom.table, op.family(), "fresh-store:" + op.method());
                continue;
            }
            rt.recordStore(atom, view.frame(), new ModelStore(view, e), storedValue(view, v), m, null, mctx);
        }
        ElementStore es = elementStores.get(fs.vertex());
        if (es != null) {
            rt.recordStore(atom, view.frame(), es, new RecursiveTracking.ElementValue(es.atomKey()), es.member(), null, mctx); // the ELEM seed's initial store
            if (es.member() == RecursiveTracking.ARRAY_ELEMENT) {
                rt.elementContainer(es.atomKey(), atom); // the array's own heap escape marks its pieces stored
            }
        }
        Fwd fw = new Fwd(atom, null, mctx, null, null);
        if (owner == Ref.RESULT) {
            if (view.result() instanceof Temp t) {
                apply(fw, t.view(), t.op(), new Operand(t, List.of()));
            } else {
                rt.enqueueWalk(atom, view.frame(), view.node(), null, mctx);
            }
        }
        Operand self = operand(view, op, Ref.of(owner));
        if (self != null) {
            apply(fw, view, op, self); // R or the FRESH temp as a callback's operand or a stored value of its own op
        }
        return true;
    }

    // ------------------------------------------------------------------
    // Backward: the model at an invoke's result, a callback's parameter, a stored operand
    // ------------------------------------------------------------------

    /**
     * The backward application at a modelled target (the invoke's result). Returns false when the op's result is the
     * real callee's ({@code result ir}): the caller walks the IR.
     */
    boolean invokeResult(LocalFlowGraph frame, Invoke inv, JdkModels.Op op, MethodContext mctx, CallPath path, Sink sink) {
        count(op.family(), "bwd");
        if (op.resultIr()) {
            return false;
        }
        resultInto(identityView(frame, inv), op, mctx, path, sink);
        return true;
    }

    /** The result of {@code op} applied at {@code view}, resolved into {@code sink} (the op has no {@code result ir}). */
    private void resultInto(View view, JdkModels.Op op, MethodContext mctx, CallPath path, Sink sink) {
        JdkModels.Family fam = op.family();
        if (!op.hasResultEffect()) {
            unmodelled(sink, fam, "result:" + op.method());
            return;
        }
        for (Effect e : op.effects()) {
            switch (e) {
                case Alias a -> backwardOperand(view.frame(), operand(view, op, a.a()), view.node(), mctx, path, sink);
                case Fresh f -> {
                    if (f.bind() == JdkModels.BIND_RESULT) {
                        mintFresh(view, op, f, mctx, path, sink);
                    }
                }
                case Callback c -> {
                    if (c.bind() == JdkModels.BIND_RESULT) {
                        callbackResult(new Temp(view, op, c), mctx, path, sink);
                    }
                }
                case Store st -> {
                }
                case Observe o -> {
                }
                case Ir ir -> {
                }
                case Unmodelled u -> {
                }
                case ClassCheck cc -> {
                }
            }
        }
    }

    /**
     * The operand's atoms into {@code sink}: a plain node is the ordinary backward case; a member chain is the load case
     * over the chain (at the model call); a temp is the callback's result (or its fresh object); the sink itself has no
     * atom and refuses by name.
     */
    void backwardOperand(LocalFlowGraph frame, Operand o, ValueNode at, MethodContext mctx, CallPath path, Sink sink) {
        if (o == null || o.members().contains(UNRESOLVED)) {
            rt.refuse(sink, RTrackRefusal.JDK_MODEL_UNMODELLED);
            return;
        }
        if (o.plain()) {
            if (o.base() instanceof ValueNode vn) {
                rt.backward(frame, vn, mctx, path, sink);
            } else if (o.base() instanceof Temp t && t.binder() instanceof Fresh fe) {
                mintFresh(t.view(), t.op(), fe, mctx, path, sink);
            } else if (o.base() instanceof Temp t) {
                callbackResult(t, mctx, path, sink);
            } else if (o.base() instanceof SinkRef sr) {
                unmodelled(sink, sr.op().family(), "sink-object:" + sr.op().method());
            } else {
                rt.refuse(sink, RTrackRefusal.UNRESOLVED_VALUE); // `_` (no tracked value) resolved: never silent
            }
            return;
        }
        List<Object> rest = List.copyOf(o.members().subList(1, o.members().size()));
        if (o.base() instanceof ValueNode vn) {
            rt.loadCase(frame, at, vn, o.members().get(0), rest, sink, mctx, path);
        } else {
            Operand base = new Operand(o.base(), List.of());
            rt.loadCaseKey(frame, at, base, s -> backwardOperand(frame, base, at, mctx, path, s), o.members().get(0), rest, sink, mctx, path);
        }
    }

    /** A stored {@link OperandValue} resumed (the load case's continuation); false: not a model value. */
    boolean resumeStored(Object value, LocalFlowGraph frame, MethodContext mctx, CallPath path, Sink sink) {
        if (!(value instanceof OperandValue ov)) {
            return false;
        }
        if (ov.operand().plain() && ov.operand().base() instanceof SinkRef sr) {
            sinkValues(sr, new Operand(sr, List.of()), sr.view(), sr.op(), mctx, path, sink); // what the sink accepts
        } else {
            backwardOperand(frame, ov.operand(), ov.at(), mctx, path, sink);
        }
        return true;
    }

    /** Where a callback's result goes in its view (forward and backward build the same view): the op's result, its temp, or nowhere. */
    private static Object cvResult(View view, JdkModels.Op op, Callback e) {
        return e.bind() == JdkModels.BIND_RESULT ? view.result() : e.bind() >= JdkModels.BIND_TEMP ? new Temp(view, op, e) : NO_RESULT;
    }

    /** One target of a backward callback (the view, the link, the target, the pushed path, the per-call dedup sets). */
    private interface BwdLeaf {
        void target(View cv, ModelCall mc, AnalysisMethod m, CallPath pushed, Set<Object> started, Set<String> applied);
    }

    /**
     * A backward callback {@code e} of {@code op} at {@code view}: its view, its link, and its targets, selected by the
     * receiver's atoms ({@link #perReceiverAtom}: an atom of unknown type takes the whole collapsed CHA fan or its refusal
     * over the cap; a refused receiver refuses {@code sink}); each target is handed to {@code leaf}.
     */
    private void backwardCallback(View view, JdkModels.Op op, Callback e, String kind, List<Object> listenerKey, MethodContext mctx, CallPath path, Sink sink, BwdLeaf leaf) {
        JdkModels.Family fam = op.family();
        if (!(named(e.cb()) instanceof AnalysisMethod cb) || sitesOf(e, cb, op.family().lazy) == null || overDepth(view.depth() + 1)) {
            unmodelled(sink, fam, "callback-result:" + e.cb());
            return;
        }
        List<Operand> cargs = new ArrayList<>();
        cargs.add(operand(view, op, e.a()));
        for (Ref r : e.cbArgs()) {
            cargs.add(operand(view, op, r));
        }
        if (cargs.stream().anyMatch(o -> o == null || o.members().contains(UNRESOLVED))) {
            unmodelled(sink, fam, "callback-result:" + e.cb());
            return;
        }
        count(fam, "callback-bwd");
        // the callback's view as forward builds it: a fresh object minted here is the same site as forward's
        View cv = new View(view.frame(), view.inv(), List.copyOf(cargs), cvResult(view, op, e), view.depth() + 1);
        List<DispatchResolution.ResolvedTarget> all = cb.isStatic() ? staticTarget(cb) : rt.chaTargets(cb, receiverType(cargs.get(0), cb), null);
        if (all.isEmpty()) {
            rt.refuse(sink, RTrackRefusal.NO_TARGET);
            return;
        }
        Set<Object> started = ConcurrentHashMap.newKeySet();
        Set<String> applied = ConcurrentHashMap.newKeySet();
        ModelCall mc = modelCall(cv, e, fam, cb);
        CallPath pushed = CallPath.pushBackward(view.frame(), mc, mctx, path);
        if (all.size() == 1) {
            leaf.target(cv, mc, all.get(0).method(), pushed, started, applied);
            return;
        }
        perReceiverAtom(kind, view, cargs.get(0), mctx, path, listenerKey, cb, all, sel -> {
            RTrackRefusal over = fanRefusal(sel);
            if (over != null) {
                rt.refuse(sink, over);
                return;
            }
            for (DispatchResolution.ResolvedTarget x : sel) {
                leaf.target(cv, mc, x.method(), pushed, started, applied);
            }
        }, sink); // a refused receiver refuses the result, no fan
    }

    /** The result of a callback (the temp {@code t}: the callback {@code binder} at its view) into {@code sink}. */
    private void callbackResult(Temp t, MethodContext mctx, CallPath path, Sink sink) {
        backwardCallback(t.view(), t.op(), (Callback) t.binder(), "mcb-recv", List.of("mcb", sink, t), mctx, path, sink,
                        (cv, mc, m, pushed, started, applied) -> callbackTarget(cv, mc, m, mctx, path, pushed, sink, started, applied));
    }

    /**
     * One target of a backward callback (started once per target): a model is its own result on the callback's operands
     * (re-dispatch), anything else the target's IR returns along the link.
     */
    private void callbackTarget(View cv, ModelCall mc, AnalysisMethod m, MethodContext mctx, CallPath path, CallPath pushed, Sink sink, Set<Object> started, Set<String> applied) {
        if (!started.add(m)) {
            return;
        }
        RecursiveTracking.TargetCheck tc = callbackRule(m, sink, "callback-bwd");
        if (tc == null) {
            return;
        }
        if (tc.rule() == RecursiveTracking.TargetRule.MODEL && !tc.op().resultIr()) {
            if (firstOfKey(applied, tc.op())) {
                count(mc.family(), "redispatch-bwd");
                resultInto(cv, tc.op(), mctx, path, sink);
            }
            return;
        }
        LocalFlowGraph calleeFrame = rt.bridge.frameOf(m);
        StructuredGraph g = calleeFrame != null ? rt.graphOf(calleeFrame) : null;
        if (calleeFrame == null && rt.dropDeadTarget(m, "bwd-callback")) {
            return;
        }
        if (g == null) {
            rt.missingIr("bwd-callback-callee", m);
            rt.refuse(sink, RTrackRefusal.MISSING_IR);
            return;
        }
        MethodContext calleeMctx = m.isStatic() ? MethodContext.staticCtx(new ContainerAtoms.ContextElement(rt.bridge.methodOf(cv.frame()), StringAnalysisChildInlining.pointsToBci(cv.inv())), mctx)
                        : MethodContext.UNKNOWN;
        for (ReturnNode ret : g.getNodes(ReturnNode.TYPE)) {
            if (ret.result() != null) {
                rt.backward(calleeFrame, ret.result(), calleeMctx, pushed, sink);
            }
        }
    }

    /**
     * The values the sink {@code s} accepts, into {@code sink}: a callback on the sink ({@code s.accept(x)}) gives x; a
     * callback that passes the sink on (to a spliterator, an iterator, a stream) gives what its targets' models accept
     * (per receiver atom); an IR-walked target (a user Spliterator) refuses by name: the sink has no atom its code could
     * call.
     */
    private void sinkValues(SinkRef sr, Operand s, View view, JdkModels.Op op, MethodContext mctx, CallPath path, Sink sink) {
        for (Effect e : op.effects()) {
            if (!(e instanceof Callback c)) {
                continue;
            }
            if (s.equals(operand(view, op, c.a()))) {
                if (!isAccept(c)) {
                    unmodelled(sink, op.family(), "sink-callback:" + c.cb());
                    continue;
                }
                count(sr.op().family(), "sink-bwd");
                backwardOperand(view.frame(), operand(view, op, c.cbArgs().get(0)), view.node(), mctx, path, sink);
                continue;
            }
            boolean passes = false;
            for (Ref r : c.cbArgs()) {
                passes |= s.equals(operand(view, op, r));
            }
            if (passes) {
                backwardCallback(view, op, c, "mcb-sink", List.of("mcbs", sink, view, c), mctx, path, sink,
                                (cv, mc, m, pushed, started, applied) -> sinkTarget(sr, s, cv, mc, m, mctx, path, sink, started, applied));
            }
        }
    }

    /** One target of a callback that passes the sink on: its model's accepted values (re-dispatch), or a named refusal. */
    private void sinkTarget(SinkRef sr, Operand s, View cv, ModelCall mc, AnalysisMethod m, MethodContext mctx, CallPath path, Sink sink, Set<Object> started, Set<String> applied) {
        if (!started.add(m)) {
            return;
        }
        RecursiveTracking.TargetCheck tc = callbackRule(m, sink, "sink");
        if (tc == null) {
            return;
        }
        if (tc.rule() == RecursiveTracking.TargetRule.MODEL) {
            if (firstOfKey(applied, tc.op())) {
                count(mc.family(), "redispatch-sink");
                sinkValues(sr, s, cv, tc.op(), mctx, path, sink);
            }
            return;
        }
        unmodelled(sink, sr.op().family(), "sink-ir:" + m.format("%H.%n(%p)"));
    }

    /**
     * A callback's parameter {@code pidx} resolved backward along a {@link ModelCall} link (true): the callback's operand
     * (a node of the modelled call, an element of a container argument, a temp); false = not a model link.
     */
    boolean parameterCase(CallPath path, int pidx, Sink sink) {
        if (!(path.call instanceof ModelCall mc)) {
            return false;
        }
        Operand o = pidx < mc.view.args().size() ? mc.view.args().get(pidx) : null;
        if (o == null) {
            rt.refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
        } else {
            backwardOperand(path.callerFrame, o, (ValueNode) mc.inv.asNode(), RecursiveTracking.restored(path.callerMctx), path.next, sink);
        }
        return true;
    }

    // ------------------------------------------------------------------
    // The image heap (the fill of an array representation from the snapshot)
    // ------------------------------------------------------------------

    /**
     * The image-heap fill (one hook in {@code buildTimeStores}): a heap container's abstracted array representation is not
     * a member; each element of its snapshot is a build-time store of the slot (the reverse heap index lists the container
     * as the element's holder under the slot). A pending value refuses by name; a node or link representation
     * (LinkedList) is the ordinary build-time store (the container refuses by the field rule and the value inherits it), so
     * a heap container's slot is never silently empty. False: {@code f} is no abstracted field.
     */
    boolean heapFill(RAtom holder, AnalysisField f, Object v) {
        if (!abstracted(f)) {
            return false;
        }
        if (v == null || v instanceof jdk.vm.ci.meta.JavaConstant jc && jc.isNull()) {
            return true;
        }
        if (!(v instanceof jdk.vm.ci.meta.JavaConstant)) {
            rt.heapSnapshotPending.incrementAndGet();
            rt.refuse(holder.table, RTrackRefusal.HEAP_SNAPSHOT_PENDING);
            return true;
        }
        JdkModels.Slot slot = representationSlot(f, "heap-fill");
        if (slot == null || !(v instanceof ImageHeapObjectArray arr)) {
            // A node or link representation (LinkedList's nodes, a view's `-@` link) is the ordinary build-time store: it
            // refuses the container by the field rule and records the value's holder, so the value (and every node and
            // item behind it) inherits the refusal at its build-time escape. A bare field rule would drop that inheritance.
            rt.appendBuildTimeStore(holder.table, holder.key, f, v, -1);
            return true;
        }
        for (int i = 0; i < arr.getLength(); i++) {
            Object e;
            try {
                e = arr.getElement(i);
            } catch (Throwable t) {
                e = RecursiveTracking.PENDING;
            }
            rt.appendBuildTimeStore(holder.table, holder.key, slot, e, i);
        }
        return true;
    }

    /** The slot an abstracted array field's snapshot elements fill (the reverse heap index), or null. */
    JdkModels.Slot heapSlot(Object member) {
        return abstracting(member) != null ? JdkModels.representationSlot((AnalysisField) member) : null;
    }

    /**
     * A heap constant's slot is its snapshot's (true): its class has an array representation field of an enabled family
     * mapping to that slot (filled from the snapshot, or the container refused at its build-time stores). False: no such
     * field, so the slot would be silently empty (the load refuses by name).
     */
    boolean heapSlotsFilled(com.oracle.graal.pointsto.heap.ImageHeapConstant c, JdkModels.Slot slot) {
        if (c == null || c.getType() == null) {
            return false;
        }
        return heapFilled.computeIfAbsent(List.of(c.getType(), slot), k -> {
            for (var rf : c.getType().getInstanceFields(true)) {
                if (rf instanceof AnalysisField af && abstracting(af) != null && JdkModels.representationSlot(af) == slot) {
                    return true;
                }
            }
            return false;
        });
    }

    /** The census field (printed only when a family is on). */
    String census() {
        StringBuilder sb = new StringBuilder(" jdkmodel{on=").append(JdkModels.enabledIds());
        Map<String, String> off = new TreeMap<>();
        familyOff.forEach((f, why) -> {
            if (!why.isEmpty()) {
                off.put(f.id, why);
            }
        });
        sb.append(" off=").append(off).append(" chains=").append(chainLoads.get()).append(" fresh=").append(freshSites.size());
        Map<String, Long> kinds = new TreeMap<>();
        Map<String, Counter> unmod = new TreeMap<>();
        by.forEach((k, c) -> {
            int colon = k.indexOf(':');
            kinds.merge(colon < 0 ? k : k.substring(0, colon), c.get(), Long::sum);
            if (colon >= 0) {
                unmod.put(k, c);
            }
        });
        sb.append(" kinds=").append(kinds).append(" depth=").append(new TreeMap<>(depths)).append(" unmodelled=").append(RecursiveTracking.top(unmod)).append('}');
        return sb.toString();
    }
}
