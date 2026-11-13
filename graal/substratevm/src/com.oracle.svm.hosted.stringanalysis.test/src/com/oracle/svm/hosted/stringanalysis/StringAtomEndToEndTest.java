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

import java.lang.annotation.Annotation;
import java.lang.reflect.AnnotatedElement;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.graalvm.collections.EconomicMap;
import org.graalvm.nativeimage.impl.AnnotationExtractor;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.graal.pointsto.api.HostVM;
import com.oracle.graal.pointsto.heap.ImageHeapConstant;
import com.oracle.graal.pointsto.infrastructure.SubstitutionProcessor;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisFactory;
import com.oracle.graal.pointsto.typestate.DefaultAnalysisPolicy;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.NodeSourcePosition;
import jdk.graal.compiler.java.GraphBuilderPhase;
import jdk.graal.compiler.nodes.BeginNode;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.InvokeNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration;
import jdk.graal.compiler.nodes.graphbuilderconf.IntrinsicContext;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.graal.compiler.phases.OptimisticOptimizations;
import jdk.graal.compiler.word.WordCastNode;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * End-to-end pins of the one string engine. Each case drives a STRING atom
 * ({@link RecursiveTracking#mintString}) over a small synthetic IR (frames = {@link LocalFlowGraph}s over hand-built
 * {@link StructuredGraph}s of a JVMCI-backed analysis universe, a fixture {@link RecursiveTracking.Bridge} and a fixture
 * {@link StringAtoms.Sites}), drains the engine to quiescence, and reads the result through the verdict layer's
 * interface: {@link ForwardFixpoint#emit} and its {@code strackAggregates} (the names → reasons, the usages-suppressed
 * token, the RESOURCE_LIMIT mark, the EVALUATION_GUARD global refusal) onto the candidate's {@link SugVertex}. The row-level JUnits
 * pin the classifiers; these pin the plumbing from the rows to the candidate. The eight cases:
 * <ol>
 * <li>an R2 (raw memory) use: UNSAFE_ACCESS, the candidate is incomplete (usages suppressed);</li>
 * <li>a caller-less exit: NO_CALLER_EXIT;</li>
 * <li>a raw {@code String.value} read is a field usage, and a String-declared receiver call is a terminal whose body is
 * not entered;</li>
 * <li>the walk budget: WALK_BUDGET, the candidate is resource-limited;</li>
 * <li>a return continuation reaches the caller's post-call usage;</li>
 * <li>an argument position is a PARAMETER usage with its index;</li>
 * <li>an unresolved call is a named refusal;</li>
 * <li>a guard trip refuses every atom with EVALUATION_GUARD.</li>
 * </ol>
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.memory.address",
                "jdk.graal.compiler/jdk.graal.compiler.word", "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo", "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory", "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc", "jdk.graal.compiler/jdk.graal.compiler.graph.spi",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.memory", "jdk.graal.compiler/jdk.graal.compiler.lir.gen",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators", "jdk.graal.compiler/jdk.graal.compiler.nodes.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.graphbuilderconf", "jdk.graal.compiler/jdk.graal.compiler.java",
                "jdk.graal.compiler/jdk.graal.compiler.phases", "jdk.graal.compiler/jdk.graal.compiler.replacements.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.virtual", "jdk.graal.compiler/jdk.graal.compiler.nodes.util",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.type", "jdk.graal.compiler/jdk.graal.compiler.core.common",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.cfg",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.gc", "jdk.graal.compiler/jdk.graal.compiler.nodes.loop",
                "jdk.internal.vm.ci/jdk.vm.ci.common", "org.graalvm.nativeimage/org.graalvm.nativeimage.impl"})
public class StringAtomEndToEndTest {

    /** The fixture program's methods (their bodies are the hand-built graphs; only their signatures are read). */
    @SuppressWarnings("unused")
    static final class Program {
        static String seed(String s) {
            return s;
        }

        static void two(Object o, String s) {
        }

        static String callee(String s) {
            return s;
        }

        static int caller(String s) {
            return callee(s).length();
        }

        // fixtures: the arm-liveness continuation stop, and the receiver-aware dispatch's two engine sources
        static void use(Object o) {
        }

        interface Sink {
            void take(String s);
        }

        static final class SinkA implements Sink {
            @Override
            public void take(String s) {
            }
        }

        static final class SinkB implements Sink {
            @Override
            public void take(String s) {
            }
        }

        static final class SinkC implements Sink {
            @Override
            public void take(String s) {
            }
        }

        static void feed(Sink k, String s) {
            k.take(s);
        }

        static void opaque(String s) {
        }

        /** An instance method whose receiver slot is resolved by the owner shortcut. */
        static final class Owned {
            Object self() {
                return this;
            }
        }

        interface Factory {
            Object make();
        }

        static final class FactoryA implements Factory {
            @Override
            public Object make() {
                return null;
            }
        }

        static final class FactoryB implements Factory {
            @Override
            public Object make() {
                return unknown();
            }
        }

        static final class Holder {
            String value;
        }

        /** A static string field (the static-store escape route). */
        static String last;

        static Object unknown() {
            return null;
        }

        static void build(String s) {
        }

        /** A static frame whose IR is one allocation (the static visited-key pin). */
        static Object fresh() {
            return new Holder();
        }
    }

    /** The minimal JVMCI-backed analysis universe (the ArmFeasibilityTest shape) plus method/field lookups. */
    private static final class Universe {
        final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
        final AnalysisUniverse universe;

        Universe() {
            AnnotationExtractor annotations = new AnnotationExtractor() {
                @Override
                public boolean hasAnnotation(AnnotatedElement element, Class<? extends Annotation> annotationType) {
                    return element.isAnnotationPresent(annotationType);
                }

                @Override
                public <T extends Annotation> T extractAnnotation(AnnotatedElement element, Class<T> annotationType, boolean declaredOnly) {
                    return declaredOnly ? element.getDeclaredAnnotation(annotationType) : element.getAnnotation(annotationType);
                }

                @Override
                @SuppressWarnings("unchecked")
                public Class<? extends Annotation>[] getAnnotationTypes(AnnotatedElement element) {
                    return Arrays.stream(element.getAnnotations()).map(Annotation::annotationType).toArray(Class[]::new);
                }
            };
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), StringAtomEndToEndTest.class.getClassLoader()) {
                @Override
                public void onTypeReachable(com.oracle.graal.pointsto.BigBang bb, AnalysisType type) {
                    // no-op
                }

                @Override
                public boolean isInitialized(AnalysisType type) {
                    return true;
                }

                @Override
                public GraphBuilderPhase.Instance createGraphBuilderPhase(com.oracle.graal.pointsto.meta.HostedProviders providers,
                                GraphBuilderConfiguration config, OptimisticOptimizations optimizations, IntrinsicContext intrinsicContext) {
                    return null;
                }

                @Override
                public Comparator<? super ResolvedJavaType> getTypeComparator() {
                    return null;
                }
            };
            this.universe = new AnalysisUniverse(host, JavaKind.Object, new DefaultAnalysisPolicy(new OptionValues(EconomicMap.create())),
                            SubstitutionProcessor.IDENTITY, metaAccess, new PointsToAnalysisFactory(), annotations);
            type(Object.class);
            type(Cloneable.class); // the universe's own bootstrap order (AnalysisType's constructor reads Cloneable)
            type(java.io.Serializable.class);
            type(String.class);
            /*
             * Every fixture type exists before the no-op analysis stand-in is installed (as in ChaAbstractRootLoopTest): a
             * type created later would register itself with the stand-in and fail loudly.
             */
            for (Class<?> c : new Class<?>[]{void.class, int.class, long.class, boolean.class, Number.class, CharSequence.class, Program.class,
                            Program.Sink.class, Program.SinkA.class, Program.SinkB.class, Program.SinkC.class, Program.Factory.class,
                            Program.FactoryA.class, Program.FactoryB.class, Program.Holder.class, byte[].class, Thread.class, ThreadLocal.class,
                            InheritableThreadLocal.class, Program.Owned.class}) {
                type(c);
            }
            // the engine's own lazy lookups (RecursiveTracking.tlTypes and the thread-local erasure fields)
            for (String n : new String[]{"jdk.internal.misc.TerminatingThreadLocal", "java.lang.ThreadLocal$ThreadLocalMap", "java.lang.ThreadLocal$ThreadLocalMap$Entry"}) {
                try {
                    type(Class.forName(n, false, Object.class.getClassLoader()));
                } catch (ClassNotFoundException e) {
                    throw new AssertionError(e);
                }
            }
            universe.setBigBang((com.oracle.graal.pointsto.BigBang) java.lang.reflect.Proxy.newProxyInstance(com.oracle.graal.pointsto.BigBang.class.getClassLoader(),
                            new Class<?>[]{com.oracle.graal.pointsto.BigBang.class}, (proxy, m, args) -> noOp(proxy, m, args)));
        }

        private static Object noOp(Object proxy, java.lang.reflect.Method m, Object[] args) {
            switch (m.getName()) {
                case "equals":
                    return proxy == args[0];
                case "hashCode":
                    return System.identityHashCode(proxy);
                case "toString":
                    return "StringAtomEndToEndTest.NoOpBigBang";
                default:
                    break;
            }
            Class<?> r = m.getReturnType();
            if (r == boolean.class) {
                return false;
            } else if (r == long.class) {
                return 0L;
            } else if (r == float.class) {
                return 0f;
            } else if (r == double.class) {
                return 0d;
            } else if (r == short.class) {
                return (short) 0;
            } else if (r == byte.class) {
                return (byte) 0;
            } else if (r == char.class) {
                return (char) 0;
            } else if (r == int.class) {
                return 0;
            }
            return null;
        }

        AnalysisType type(Class<?> c) {
            return universe.lookup((ResolvedJavaType) metaAccess.lookupJavaType(c));
        }

        AnalysisMethod method(Class<?> c, String name, Class<?>... params) {
            try {
                return universe.lookup(metaAccess.lookupJavaMethod(c.getDeclaredMethod(name, params)));
            } catch (NoSuchMethodException e) {
                throw new AssertionError(e);
            }
        }

        AnalysisField field(Class<?> c, String name) {
            for (ResolvedJavaField f : metaAccess.lookupJavaType(c).getInstanceFields(false)) {
                if (f.getName().equals(name)) {
                    return universe.lookup(f);
                }
            }
            throw new AssertionError("no " + c.getName() + "." + name);
        }

        AnalysisField staticField(Class<?> c, String name) {
            for (ResolvedJavaField f : metaAccess.lookupJavaType(c).getStaticFields()) {
                if (f.getName().equals(name)) {
                    return universe.lookup(f);
                }
            }
            throw new AssertionError("no static " + c.getName() + "." + name);
        }
    }

    /**
     * One fixture world: the frames (method → graph), the caller lists, the call targets and the Phase-A call sites the
     * bridge and the sites answer with, the engine, and the candidate SUG graph.
     */
    private static final class World {
        final Universe u = new Universe();
        final Map<AnalysisMethod, LocalFlowGraph> frames = new HashMap<>();
        final Map<LocalFlowGraph, List<ForwardFixpoint.CallerSite>> callers = new HashMap<>();
        /** Call targets by declared callee; a callee absent here resolves to itself; an empty list = no target. */
        final Map<AnalysisMethod, List<AnalysisMethod>> targets = new HashMap<>();
        final Map<Invoke, SugVertex> phaseASites = new HashMap<>();
        final Map<List<Object>, SugVertex> sites = new HashMap<>();
        final StringUtilizationGraph sug = new StringUtilizationGraph();
        /** The STRING atoms' block (TOP = the table proves nothing) and the points-to receiver facts by callee. */
        ForwardFixpoint.Block stringBlock = ForwardFixpoint.Block.TOP;
        final Map<AnalysisMethod, List<AnalysisType>> pointsTo = new HashMap<>();
        final Map<List<Object>, List<LocalFlowGraph.TypeGuard>[]> armMemo = new HashMap<>();
        final RecursiveTracking engine;
        private int nextSite = 900_000_000;

        World() {
            this.engine = new RecursiveTracking(new FixtureBridge(), null);
            engine.strackSites(new FixtureSites());
        }

        LocalFlowGraph frame(AnalysisMethod m) {
            OptionValues options = new OptionValues(EconomicMap.create());
            DebugContext debug = new DebugContext.Builder(options).build();
            StructuredGraph g = new StructuredGraph.Builder(options, debug).name(m.getName()).build();
            g.setStart(g.add(new StartNode()));
            LocalFlowGraph f = new LocalFlowGraph(m);
            f.irGraph = g;
            frames.put(m, f);
            return f;
        }

        static StructuredGraph graph(LocalFlowGraph f) {
            return (StructuredGraph) f.irGraph;
        }

        ParameterNode param(LocalFlowGraph f, int index, Class<?> type) {
            return graph(f).addWithoutUnique(new ParameterNode(index, StampPair.createSingle(StampFactory.object(TypeReference.createWithoutAssumptions(u.type(type))))));
        }

        InvokeNode invoke(LocalFlowGraph f, InvokeKind kind, AnalysisMethod target, int bci, ValueNode... args) {
            StampPair ret = StampPair.createSingle(target.getSignature().getReturnKind() == JavaKind.Object
                            ? StampFactory.object(TypeReference.createWithoutAssumptions(u.type(Object.class)))
                            : StampFactory.forKind(target.getSignature().getReturnKind()));
            MethodCallTargetNode ct = graph(f).addWithoutUnique(new MethodCallTargetNode(kind, target, args, ret, null));
            return graph(f).addWithoutUnique(new InvokeNode(ct, bci));
        }

        /** The candidate: a user-code substring site (the String View seed shape) whose atom is born at {@code births}. */
        SugVertex seed(LocalFlowGraph f, String location, ValueNode... births) {
            SugVertex v = sug.newVertex();
            v.setNodeType(SugNodeType.STRING_METHOD_CALL);
            v.setDeclaringClass("java.lang.String");
            v.setMethodName("substring");
            v.setMethodSignature("int");
            v.setSourceLocation(location);
            v.setEnclosingMethod(f.getMethod());
            engine.mintString(new StringAtoms.StringSeed(v, "SV", f, List.of(births), null));
            return v;
        }

        /** Drain to quiescence (the serial solve loop of ForwardFixpoint.solve) and emit through the verdict layer. */
        void solveAndEmit() throws ReflectiveOperationException {
            do {
                engine.drain();
            } while (engine.hasWork() || engine.roundBoundary());
            emit();
        }

        void emit() throws ReflectiveOperationException {
            ForwardFixpoint ff = new ForwardFixpoint(sug, Map.of(), Map.of(), null, null);
            java.lang.reflect.Field rt = ForwardFixpoint.class.getDeclaredField("rtrack");
            rt.setAccessible(true);
            rt.set(ff, engine);
            ff.emit();
        }

        RecursiveTracking.RAtom atom(SugVertex v) {
            for (RecursiveTracking.RAtom a : engine.stringAtoms.values()) {
                if (a.seed.vertex == v) {
                    return a;
                }
            }
            throw new AssertionError("no atom for " + v);
        }

        List<RTrackRefusal> refusals(SugVertex v) {
            return atom(v).table.refusalsSnapshot();
        }

        /** The candidate's emitted usage tags as (site label, role, index) strings. */
        List<String> usages(SugVertex v) {
            List<String> out = new ArrayList<>();
            List<UsageTag> tags = sug.getUsageTags();
            v.getUsageTags().stream().forEach(i -> {
                UsageTag t = tags.get(i);
                out.add(t.usageSite().getLabel() + ":" + t.role() + ":" + t.paramIndex());
            });
            return out;
        }

        SugVertex site(List<Object> key, String label) {
            return sites.computeIfAbsent(key, k -> {
                SugVertex s = new SugVertex(nextSite++);
                s.setLabel(label);
                s.setSourceLocation(label);
                s.setNodeType(SugNodeType.STRING_METHOD_CALL);
                return s;
            });
        }

        /** The fixture bridge: the frames and caller lists above; no image heap, no roots, no statics. */
        private final class FixtureBridge implements RecursiveTracking.Bridge {
            @Override
            public List<DispatchResolution.ResolvedTarget> resolveCrossing(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call, boolean receiverPosition,
                            ForwardFixpoint.Block siteBlock) {
                AnalysisMethod callee = call.calleeMethod;
                List<DispatchResolution.ResolvedTarget> out = new ArrayList<>();
                for (AnalysisMethod t : targets.getOrDefault(callee, callee != null ? List.of(callee) : List.of())) {
                    out.add(new DispatchResolution.ResolvedTarget(t, frames.get(t), null, t.isStatic(), t.getDeclaringClass().toJavaName(true)));
                }
                return out;
            }

            @Override
            public AnalysisMethod methodOf(LocalFlowGraph frame) {
                return frame.getMethod();
            }

            @Override
            public List<ForwardFixpoint.CallerSite> callersOf(LocalFlowGraph frame) {
                return callers.get(frame);
            }

            @Override
            public boolean isWorldTop(LocalFlowGraph frame) {
                return false;
            }

            @Override
            public StructuredGraph decodeIrGraph(AnalysisMethod method) {
                LocalFlowGraph f = frames.get(method);
                return f != null ? graph(f) : null;
            }

            @Override
            public AnalysisField resolveField(ResolvedJavaField field) {
                return field instanceof AnalysisField af ? af : u.universe.lookup(field);
            }

            @Override
            public AnalysisMethod resolveMethod(ResolvedJavaMethod method) {
                return method instanceof AnalysisMethod am ? am : u.universe.lookup(method);
            }

            @Override
            public ForwardFixpoint.Block siteBlockOf(LocalFlowGraph frame, LocalFlowGraph.LocalVertex site) {
                return ForwardFixpoint.Block.TOP;
            }

            @Override
            public ForwardFixpoint.Block widenedBlockOf(AnalysisType exactType) {
                return null;
            }

            @Override
            public LocalFlowGraph frameOf(AnalysisMethod method) {
                return frames.get(method);
            }

            @Override
            public Map<AnalysisType, Set<ImageHeapConstant>> heapObjects() {
                return Map.of();
            }

            @Override
            public boolean classInitSimulated(AnalysisType type) {
                return false;
            }

            @Override
            public JavaConstant simulatedStaticValue(AnalysisField f) {
                return null;
            }

            @Override
            public Iterable<AnalysisMethod> universeMethods() {
                return new ArrayList<>(frames.keySet());
            }

            @Override
            public Iterable<AnalysisField> staticFields() {
                return List.of();
            }

            @Override
            public Iterable<AnalysisField> universeFields() {
                return List.of();
            }

            @Override
            public Set<AnalysisType> argStampOfUnregistered(Invoke inv) {
                return null;
            }

            @Override
            public AnalysisType lookupJavaType(Class<?> c) {
                return u.type(c);
            }

            @Override
            public AnalysisMethod resolveMethodSubstituted(ResolvedJavaMethod method) {
                return resolveMethod(method);
            }

            @Override
            public List<AnalysisMethod> foreignCallTargets() {
                return List.of();
            }

            @Override
            public List<AnalysisType> pointsToReceiverTypes(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call, java.util.function.Consumer<String> why) {
                List<AnalysisType> types = pointsTo.get(call.calleeMethod);
                if (types == null) {
                    why.accept("noInvokeFlow");
                }
                return types;
            }
        }

        /** The fixture usage sites: detached SUG vertices keyed like ForwardFixpoint.StrackSites', labelled for the asserts. */
        private final class FixtureSites implements StringAtoms.Sites {
            @Override
            public SugVertex phaseACallSite(LocalFlowGraph frame, Invoke inv) {
                return phaseASites.get(inv);
            }

            @Override
            public SugVertex concatSite(LocalFlowGraph frame, Invoke inv) {
                return site(List.of("concat", frame, inv.bci()), "concat@" + inv.bci());
            }

            @Override
            public SugVertex targetSite(LocalFlowGraph frame, LocalFlowGraph.LocalVertex call, AnalysisMethod target) {
                return site(List.of("target", frame, call.bci, target), target.getName() + "@" + frame.getMethod().getName() + ":" + call.bci);
            }

            @Override
            public SugVertex fieldSite(LocalFlowGraph frame, LoadFieldNode lfn) {
                String usage = SugNameTables.rawStringFieldUsageName(lfn.field().getName());
                return site(List.of("field", frame, lfn), (usage != null ? usage : lfn.field().getName()) + "@" + frame.getMethod().getName());
            }

            @Override
            public SugVertex classCheckSite(LocalFlowGraph frame, ValueNode node, String label) {
                return site(List.of("classcheck", frame, node), label);
            }

            @Override
            public boolean armDead(LocalFlowGraph frame, jdk.graal.compiler.graph.Node anchor, ValueNode observed, ForwardFixpoint.Block block) {
                return armFeasibility(frame, anchor, observed, block) != 0;
            }

            @Override
            public int armFeasibility(LocalFlowGraph frame, jdk.graal.compiler.graph.Node anchor, ValueNode observed, ForwardFixpoint.Block block) {
                return ForwardFixpoint.armFeasibility(frame, anchor, observed, block, armMemo); // the production table (no guards: 0)
            }

            @Override
            public boolean strictExactInstanceOf(LocalFlowGraph frame, InstanceOfNode ion) {
                return true;
            }

            @Override
            public StringAtoms.Concat concatAt(LocalFlowGraph frame, Invoke inv) {
                return StringAtoms.Concat.NONE;
            }

            @Override
            public long[] concatUnreadable() {
                return new long[]{0, 0, 0, 0};
            }

            @Override
            public ForwardFixpoint.Block stringBlock() {
                return stringBlock;
            }

            @Override
            public AnalysisMethod objectToString() {
                return null;
            }
        }
    }

    private static void assertRefusedCandidate(World w, SugVertex v, RTrackRefusal expected) {
        Assert.assertTrue(expected + " expected, got " + w.refusals(v), w.refusals(v).contains(expected));
        Assert.assertEquals("the canonical refusal token", ForwardFixpoint.D2_ALL_TOKEN, v.getBudgetRefusal());
        Assert.assertTrue("a refused candidate is incomplete", v.isIncompleteTrace());
        Assert.assertTrue("the emitted usage list is suppressed", w.usages(v).isEmpty());
        Assert.assertTrue("the candidate is an emitted atom", v.isEmittedAtom());
    }

    /** Case 1: an R2 use ({@code Word.objectToUntrackedPointer(s)}) is UNSAFE_ACCESS; the candidate is incomplete (usages suppressed). */
    @Test
    public void r2UseIsUnsafeAccessAndTheCandidateIsIncomplete() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        World.graph(f).addWithoutUnique(WordCastNode.objectToUntrackedPointer(s, JavaKind.Long));
        SugVertex v = w.seed(f, "Program#seed@1", s);
        w.solveAndEmit();
        assertRefusedCandidate(w, v, RTrackRefusal.UNSAFE_ACCESS);
        Assert.assertFalse("UNSAFE_ACCESS is not a budget-class refusal", v.isResourceLimitedTrace());
    }

    /** Case 2: a return with an empty path out of a frame no analysed call reaches is NO_CALLER_EXIT. */
    @Test
    public void callerLessExitIsNoCallerExit() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        World.graph(f).addWithoutUnique(new ReturnNode(s));
        SugVertex v = w.seed(f, "Program#seed@1", s);
        w.solveAndEmit();
        assertRefusedCandidate(w, v, RTrackRefusal.NO_CALLER_EXIT);
    }

    /**
     * Case 3: a raw {@code String.value} read of the walked string is a field usage (RECEIVER), and a call into a
     * String-declared resolved target at the receiver slot is a TERMINAL usage: its body (which reads {@code value} of
     * its own receiver) is not entered, so no usage is recorded there.
     */
    @Test
    public void rawValueReadIsAFieldUsageAndAStringReceiverCallIsATerminal() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        World.graph(f).addWithoutUnique(LoadFieldNode.create(null, s, w.u.field(String.class, "value")));
        AnalysisMethod length = w.u.method(String.class, "length");
        w.invoke(f, InvokeKind.Virtual, length, 7, s);
        // the terminal's body: it reads its own receiver's value (a field usage if the body were walked)
        LocalFlowGraph body = w.frame(length);
        World.graph(body).addWithoutUnique(LoadFieldNode.create(null, w.param(body, 0, String.class), w.u.field(String.class, "value")));
        SugVertex v = w.seed(f, "Program#seed@1", s);
        w.solveAndEmit();
        Assert.assertEquals("no refusal", List.of(), w.refusals(v));
        Assert.assertNull("no refusal token", v.getBudgetRefusal());
        Assert.assertFalse(v.isIncompleteTrace());
        List<String> us = w.usages(v);
        Assert.assertTrue("the raw read is a field usage: " + us, us.contains(SugNameTables.RAW_VALUE_USAGE + "@seed:RECEIVER:-1"));
        Assert.assertTrue("the String-declared receiver call is a terminal usage: " + us, us.contains("length@seed:7:RECEIVER:-1"));
        Assert.assertFalse("the terminal's body is not entered: " + us, us.contains(SugNameTables.RAW_VALUE_USAGE + "@length:RECEIVER:-1"));
        Assert.assertEquals(2, us.size());
    }

    /** Case 4: a walk past the WALK_BUDGET positions is WALK_BUDGET, a budget-class refusal: resource-limited. */
    @Test
    public void walkBudgetIsResourceLimited() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        ValueNode cur = s;
        for (int i = 0; i <= RecursiveTracking.WALK_BUDGET + 8; i++) {
            cur = World.graph(f).addWithoutUnique(new PiNode(cur, s.stamp(jdk.graal.compiler.nodes.NodeView.DEFAULT)));
        }
        SugVertex v = w.seed(f, "Program#seed@1", s);
        w.solveAndEmit();
        assertRefusedCandidate(w, v, RTrackRefusal.WALK_BUDGET);
        Assert.assertTrue("WALK_BUDGET is budget-class: RESOURCE_LIMIT", v.isResourceLimitedTrace());
    }

    /**
     * Case 5: the string returned by the callee continues at the caller's call result (the caller-list return rule of a
     * merged, path-free atom), where the post-call usage {@code .length()} is recorded at the caller's bci.
     */
    @Test
    public void returnContinuationReachesTheCallersPostCallUsage() throws Exception {
        World w = new World();
        AnalysisMethod calleeM = w.u.method(Program.class, "callee", String.class);
        LocalFlowGraph callee = w.frame(calleeM);
        ParameterNode s = w.param(callee, 0, String.class);
        World.graph(callee).addWithoutUnique(new ReturnNode(s));
        LocalFlowGraph caller = w.frame(w.u.method(Program.class, "caller", String.class));
        ParameterNode cs = w.param(caller, 0, String.class);
        InvokeNode call = w.invoke(caller, InvokeKind.Static, calleeM, 3, cs);
        w.invoke(caller, InvokeKind.Virtual, w.u.method(String.class, "length"), 9, call);
        LocalFlowGraph.LocalVertex callVertex = new LocalFlowGraph.LocalVertex(caller, 0, LocalFlowGraph.VertexKind.INVOKE_CALLSITE);
        callVertex.bci = 3;
        callVertex.calleeMethod = calleeM;
        callVertex.irNode = call;
        w.callers.put(callee, List.of(new ForwardFixpoint.CallerSite(caller.getMethod(), callVertex)));
        SugVertex v = w.seed(callee, "Program#callee@1", s);
        w.solveAndEmit();
        List<String> us = w.usages(v);
        Assert.assertEquals("no refusal: " + w.refusals(v), List.of(), w.refusals(v));
        Assert.assertEquals("the caller's post-call usage", List.of("length@caller:9:RECEIVER:-1"), us);
    }

    /** Case 6: the string at an argument slot of a call with a Phase-A usage site is a PARAMETER usage with its slot. */
    @Test
    public void argumentPositionIsAParameterUsageWithItsIndex() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        ParameterNode o = w.param(f, 1, Object.class);
        AnalysisMethod two = w.u.method(Program.class, "two", Object.class, String.class);
        InvokeNode call = w.invoke(f, InvokeKind.Static, two, 5, o, s);
        LocalFlowGraph body = w.frame(two);
        w.param(body, 0, Object.class);
        w.param(body, 1, String.class);
        w.phaseASites.put(call, w.site(List.of("phaseA", call), "two@5"));
        SugVertex v = w.seed(f, "Program#seed@1", s);
        w.solveAndEmit();
        Assert.assertEquals("no refusal: " + w.refusals(v), List.of(), w.refusals(v));
        Assert.assertEquals("the PARAMETER usage with the argument index", List.of("two@5:PARAMETER:1"), w.usages(v));
    }

    /** Case 7: a call with no resolvable target is the named refusal NO_TARGET (never a silent pass). */
    @Test
    public void unresolvedCallIsANamedRefusal() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        AnalysisMethod hash = w.u.method(String.class, "hashCode"); // (a final class: no universe-wide implementation scan)
        w.targets.put(hash, List.of());
        w.invoke(f, InvokeKind.Virtual, hash, 4, s);
        SugVertex v = w.seed(f, "Program#seed@1", s);
        w.solveAndEmit();
        assertRefusedCandidate(w, v, RTrackRefusal.NO_TARGET);
    }

    /** Case 8: a tripped EVALUATION_GUARD is a GLOBAL refusal — every atom takes EVALUATION_GUARD, even a clean one. */
    @Test
    public void guardTripRefusesEveryAtom() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        w.invoke(f, InvokeKind.Virtual, w.u.method(String.class, "length"), 7, s);
        SugVertex v1 = w.seed(f, "Program#seed@1", s);
        SugVertex v2 = w.seed(f, "Program#seed@2", s);
        do {
            w.engine.drain();
        } while (w.engine.hasWork() || w.engine.roundBoundary());
        Assert.assertEquals("clean before the trip", List.of(), w.refusals(v1));
        java.lang.reflect.Field g = RecursiveTracking.class.getDeclaredField("guardTripped");
        g.setAccessible(true);
        g.set(w.engine, true);
        w.emit();
        for (SugVertex v : List.of(v1, v2)) {
            Assert.assertEquals("refusal token", ForwardFixpoint.D2_ALL_TOKEN, v.getBudgetRefusal());
            Assert.assertTrue(v.isIncompleteTrace());
            Assert.assertTrue("EVALUATION_GUARD is budget-class: RESOURCE_LIMIT", v.isResourceLimitedTrace());
            Assert.assertTrue(w.usages(v).isEmpty());
        }
    }

    // ------------------------------------------------------------------
    // The arm-liveness continuation stop (built on the arm-feasibility table).
    // ------------------------------------------------------------------

    /** A trusted type reference, as the bytecode parser makes for instanceof/checkcast (an untrusted interface stamp is Object). */
    private static TypeReference ref(World w, Class<?> c) {
        return TypeReference.createTrustedWithoutAssumptions(w.u.type(c));
    }

    /**
     * {@code use(Object o)}: {@code if (o instanceof Number) o.longValue(); else if (o instanceof CharSequence)
     * o.length(); else o.longValue();} with the candidate String as {@code o}. The Number arm's Pi is dead by the never
     * direction (no String-cone member is a Number), the else arm's Pi by the vacuous direction (every member is a
     * CharSequence; that Pi even carries an unrelated Number stamp, which is never read): neither is walked, so neither
     * {@code longValue} (a call with no target, NO_TARGET) is reached. The CharSequence arm is a compatible
     * cast: its Pi continues, and the length() terminal is the one usage.
     */
    @Test
    public void aDeadArmsPiStopsTheWalkAndACompatibleCastContinues() throws Exception {
        World w = new World();
        w.stringBlock = ForwardFixpoint.Block.of(Set.of(w.u.type(String.class)));
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "use", Object.class));
        StructuredGraph g = World.graph(f);
        ParameterNode o = w.param(f, 0, Object.class);
        AnalysisMethod longValue = w.u.method(Number.class, "longValue");
        AnalysisMethod csLength = w.u.method(CharSequence.class, "length");
        w.targets.put(longValue, List.of()); // entering a Number arm = NO_TARGET
        w.targets.put(csLength, List.of(w.u.method(String.class, "length")));
        InstanceOfNode isNumber = (InstanceOfNode) g.addOrUnique(InstanceOfNode.create(ref(w, Number.class), o));
        BeginNode numberArm = g.add(new BeginNode());
        BeginNode notNumber = g.add(new BeginNode());
        g.start().setNext(g.add(new IfNode(isNumber, numberArm, notNumber, null)));
        PiNode asNumber = g.addWithoutUnique(new PiNode(o, StampFactory.objectNonNull(ref(w, Number.class)), numberArm));
        InvokeNode dead1 = w.invoke(f, InvokeKind.Virtual, longValue, 11, asNumber);
        numberArm.setNext(dead1);
        dead1.setNext(g.add(new ReturnNode(null)));
        InstanceOfNode isCs = (InstanceOfNode) g.addOrUnique(InstanceOfNode.create(ref(w, CharSequence.class), o));
        BeginNode csArm = g.add(new BeginNode());
        BeginNode notCs = g.add(new BeginNode());
        notNumber.setNext(g.add(new IfNode(isCs, csArm, notCs, null)));
        PiNode asCs = g.addWithoutUnique(new PiNode(o, StampFactory.objectNonNull(ref(w, CharSequence.class)), csArm));
        InvokeNode live = w.invoke(f, InvokeKind.Interface, csLength, 21, asCs);
        csArm.setNext(live);
        live.setNext(g.add(new ReturnNode(null)));
        PiNode elsePi = g.addWithoutUnique(new PiNode(o, StampFactory.objectNonNull(ref(w, Number.class)), notCs));
        InvokeNode dead2 = w.invoke(f, InvokeKind.Virtual, longValue, 31, elsePi);
        notCs.setNext(dead2);
        dead2.setNext(g.add(new ReturnNode(null)));
        LfgWalk.collectGuardsInto(f, g, t -> t instanceof AnalysisType at ? at : w.u.universe.lookup(t));
        SugVertex v = w.seed(f, "Program#use@1", o);
        w.solveAndEmit();
        Assert.assertEquals("no refusal: neither dead arm was walked", List.of(), w.refusals(v));
        Assert.assertEquals("the compatible arm continues to its usage", List.of("length@use:21:RECEIVER:-1"), w.usages(v));
        Assert.assertTrue("both dead arms' Pis stopped the walk: " + w.engine.census(), w.engine.census().contains(" armlive{piStops=2}"));
    }

    /** The same infeasible Pi without a type test confining it (no guard): nothing proves it dead, so the walk continues (NO_TARGET). */
    @Test
    public void aPiNoTypeTestConfinesContinuesWhateverItsStamp() throws Exception {
        World w = new World();
        w.stringBlock = ForwardFixpoint.Block.of(Set.of(w.u.type(String.class)));
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "use", Object.class));
        StructuredGraph g = World.graph(f);
        ParameterNode o = w.param(f, 0, Object.class);
        AnalysisMethod longValue = w.u.method(Number.class, "longValue");
        w.targets.put(longValue, List.of());
        PiNode unchecked = g.addWithoutUnique(new PiNode(o, StampFactory.objectNonNull(ref(w, Number.class))));
        InvokeNode call = w.invoke(f, InvokeKind.Virtual, longValue, 11, unchecked);
        g.start().setNext(call);
        call.setNext(g.add(new ReturnNode(null)));
        LfgWalk.collectGuardsInto(f, g, t -> t instanceof AnalysisType at ? at : w.u.universe.lookup(t));
        SugVertex v = w.seed(f, "Program#use@1", o);
        w.solveAndEmit();
        assertRefusedCandidate(w, v, RTrackRefusal.NO_TARGET);
        Assert.assertTrue(w.engine.census(), w.engine.census().contains(" armlive{piStops=0}"));
    }

    // ------------------------------------------------------------------
    // The receiver-aware dispatch rule's engine sources.
    // ------------------------------------------------------------------

    /** {@code feed(Sink k, String s) { k.take(s); }}: SinkA.take reads s.length(); SinkB.take passes s to a call with no target. */
    private static SugVertex feed(World w) {
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "feed", Program.Sink.class, String.class));
        ParameterNode k = w.param(f, 0, Program.Sink.class);
        ParameterNode s = w.param(f, 1, String.class);
        AnalysisMethod take = w.u.method(Program.Sink.class, "take", String.class);
        AnalysisMethod takeA = w.u.method(Program.SinkA.class, "take", String.class);
        AnalysisMethod takeB = w.u.method(Program.SinkB.class, "take", String.class);
        w.targets.put(take, List.of(takeA, takeB));
        w.invoke(f, InvokeKind.Interface, take, 4, k, s);
        LocalFlowGraph a = w.frame(takeA);
        w.param(a, 0, Program.SinkA.class);
        w.invoke(a, InvokeKind.Virtual, w.u.method(String.class, "length"), 2, w.param(a, 1, String.class));
        LocalFlowGraph b = w.frame(takeB);
        w.param(b, 0, Program.SinkB.class);
        AnalysisMethod opaque = w.u.method(Program.class, "opaque", String.class);
        w.targets.put(opaque, List.of());
        w.invoke(b, InvokeKind.Static, opaque, 2, w.param(b, 1, String.class));
        return w.seed(f, "Program#feed@1", s);
    }

    /** The points-to receiver state {SinkA} narrows the argument crossing to SinkA.take: SinkB.take (and its NO_TARGET) is never entered. */
    @Test
    public void argumentCrossingFollowsThePointsToReceiverState() throws Exception {
        World w = new World();
        SugVertex v = feed(w);
        w.pointsTo.put(w.u.method(Program.Sink.class, "take", String.class), List.of(w.u.type(Program.SinkA.class)));
        w.solveAndEmit();
        Assert.assertEquals("SinkB.take is not entered: " + w.refusals(v), List.of(), w.refusals(v));
        Assert.assertEquals(List.of("length@take:2:RECEIVER:-1"), w.usages(v));
        Assert.assertTrue(w.engine.census(), w.engine.census().contains(" recvPointsTo{arg=1/1 result=0/0 exact1=1 dropped=1 "));
    }

    /** No points-to fact (any bridge fallback): the committed fan, both targets entered (SinkB's NO_TARGET). */
    @Test
    public void argumentCrossingWithoutAPointsToFactKeepsTheFan() throws Exception {
        World w = new World();
        SugVertex v = feed(w);
        w.solveAndEmit();
        Assert.assertTrue(w.refusals(v).toString(), w.refusals(v).contains(RTrackRefusal.NO_TARGET));
        Assert.assertTrue(w.engine.census(), w.engine.census().contains(" recvPointsTo{arg=0/1 result=0/0 exact1=0 dropped=0 fromOverCap=0 fallbacks=[noInvokeFlow=1]}"));
    }

    /** One points-to invoke flow of the fixture: its source position (a BytecodePosition) and declared target. */
    private record Flow(NodeSourcePosition pos, AnalysisMethod target) {
    }

    private static Flow flow(AnalysisMethod method, int bci, AnalysisMethod target) {
        return new Flow(new NodeSourcePosition(null, method, bci), target);
    }

    private static String matchReason(List<Flow> flows, ResolvedJavaMethod method, int bci, AnalysisMethod callee, Flow[] out) {
        String[] why = {"matched"};
        out[0] = ForwardFixpoint.uniqueInvokeFlow(flows, Flow::pos, Flow::target, method, bci, callee, r -> why[0] = r);
        return why[0];
    }

    /**
     * The points-to invoke flow of a call is matched by method, bci and declared target. A (bci, target) match
     * in another method (an inlined-before-analysis position) is never taken, and an inlined IR invoke (no own method)
     * matches nothing: the fan is kept.
     */
    @Test
    public void pointsToInvokeFlowMatchComparesTheMethod() {
        World w = new World();
        AnalysisMethod ctx = w.u.method(Program.class, "feed", Program.Sink.class, String.class);
        AnalysisMethod other = w.u.method(String.class, "length"); // any method whose code covers bci 4
        AnalysisMethod take = w.u.method(Program.Sink.class, "take", String.class);
        Flow[] out = new Flow[1];
        Flow own = flow(ctx, 4, take);
        Flow elsewhere = flow(other, 4, take);
        Assert.assertEquals("matched", matchReason(List.of(own), ctx, 4, take, out));
        Assert.assertSame(own, out[0]);
        Assert.assertEquals("a (bci, target) match in another method is not this call's flow", "invokeFlowMethodMismatch",
                        matchReason(List.of(elsewhere), ctx, 4, take, out));
        Assert.assertNull(out[0]);
        Assert.assertEquals("matched", matchReason(List.of(elsewhere, own), ctx, 4, take, out));
        Assert.assertSame("the method disambiguates a repeated (bci, target)", own, out[0]);
        Assert.assertEquals("an inlined IR invoke (no own method) matches nothing", "invokeFlowMethodMismatch", matchReason(List.of(own), null, 4, take, out));
        Assert.assertEquals("noInvokeFlow", matchReason(List.of(own), ctx, 5, take, out));
        Assert.assertEquals("noInvokeFlow", matchReason(List.of(flow(ctx, 4, other)), ctx, 4, take, out));
        Assert.assertEquals("ambiguousInvokeFlow", matchReason(List.of(own, flow(ctx, 4, take)), ctx, 4, take, out));

        LocalFlowGraph f = w.frame(ctx);
        ParameterNode k = w.param(f, 0, Program.Sink.class);
        ParameterNode s = w.param(f, 1, String.class);
        InvokeNode plain = w.invoke(f, InvokeKind.Interface, take, 4, k, s);
        Assert.assertSame("no position, no state: the caller's method", ctx, ForwardFixpoint.invokeOwnMethod(plain, ctx));
        Assert.assertSame("a non-invoke node: the caller's method", ctx, ForwardFixpoint.invokeOwnMethod(k, ctx));
        plain.setNodeSourcePosition(new NodeSourcePosition(null, ctx, 4));
        Assert.assertSame("the invoke's own position", ctx, ForwardFixpoint.invokeOwnMethod(plain, ctx));
        InvokeNode inlined = w.invoke(f, InvokeKind.Interface, take, 4, k, s);
        inlined.setNodeSourcePosition(new NodeSourcePosition(new NodeSourcePosition(null, ctx, 2), other, 4));
        Assert.assertNull("an inlined-before-analysis invoke has no own method", ForwardFixpoint.invokeOwnMethod(inlined, ctx));
    }

    /** A receiver type whose resolution is outside the committed fan is a doubt: the fan is kept (never a smaller, wrong set). */
    @Test
    public void argumentCrossingWithAReceiverOutsideTheFanKeepsTheFan() throws Exception {
        World w = new World();
        SugVertex v = feed(w);
        w.pointsTo.put(w.u.method(Program.Sink.class, "take", String.class), List.of(w.u.type(Program.SinkA.class), w.u.type(Program.SinkC.class)));
        w.solveAndEmit();
        Assert.assertTrue(w.refusals(v).toString(), w.refusals(v).contains(RTrackRefusal.NO_TARGET));
        Assert.assertTrue(w.engine.census(), w.engine.census().contains("fallbacks=[typeOutsideFan=1]"));
    }

    /**
     * {@code build(String s) { Holder h = (Holder) new FactoryA().make(); h.value = s; }}: the store resolves its receiver
     * backward through an invoke result whose fan is {FactoryA.make (returns null), FactoryB.make (returns a call with no
     * target)}. The receiver sink of the call holds the FactoryA allocation, so only FactoryA.make is entered (no
     * refusal); a refused receiver takes the committed fan (NO_TARGET through FactoryB.make).
     */
    private static SugVertex buildWorld(World w, boolean refusedReceiver) {
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "build", String.class));
        StructuredGraph g = World.graph(f);
        ParameterNode s = w.param(f, 0, String.class);
        ValueNode receiver;
        if (refusedReceiver) {
            AnalysisMethod unknown = w.u.method(Program.class, "unknown");
            w.targets.put(unknown, List.of());
            receiver = w.invoke(f, InvokeKind.Static, unknown, 2);
        } else {
            receiver = g.add(new jdk.graal.compiler.nodes.java.NewInstanceNode(w.u.type(Program.FactoryA.class), true));
        }
        AnalysisMethod make = w.u.method(Program.Factory.class, "make");
        AnalysisMethod makeA = w.u.method(Program.FactoryA.class, "make");
        AnalysisMethod makeB = w.u.method(Program.FactoryB.class, "make");
        w.targets.put(make, List.of(makeA, makeB));
        InvokeNode h = w.invoke(f, InvokeKind.Interface, make, 6, receiver);
        g.addWithoutUnique(new jdk.graal.compiler.nodes.java.StoreFieldNode(h, w.u.field(Program.Holder.class, "value"), s));
        LocalFlowGraph a = w.frame(makeA);
        w.param(a, 0, Program.FactoryA.class);
        World.graph(a).addWithoutUnique(new ReturnNode(World.graph(a).addOrUnique(jdk.graal.compiler.nodes.ConstantNode.forConstant(JavaConstant.NULL_POINTER, null))));
        LocalFlowGraph b = w.frame(makeB);
        w.param(b, 0, Program.FactoryB.class);
        AnalysisMethod unknownB = w.u.method(Program.class, "unknown");
        w.targets.put(unknownB, List.of());
        World.graph(b).addWithoutUnique(new ReturnNode(w.invoke(b, InvokeKind.Static, unknownB, 1)));
        return w.seed(f, "Program#build@1", s);
    }

    @Test
    public void backwardResultFollowsTheReceiverSinksAtoms() throws Exception {
        World w = new World();
        SugVertex v = buildWorld(w, false);
        w.solveAndEmit();
        Assert.assertEquals("FactoryB.make is not entered: " + w.refusals(v), List.of(), w.refusals(v));
        Assert.assertTrue(w.engine.census(), w.engine.census().contains(" recvSink{cases=1 fellBack=0 narrowed=[0:0 1:1 2:0 3+:0]}"));
        Assert.assertTrue("the points-to source was asked at RESULT, apart from ARGUMENT (the memo split): " + w.engine.census(),
                        w.engine.census().contains(" recvPointsTo{arg=0/0 result=0/1 "));
    }

    @Test
    public void backwardResultWithARefusedReceiverTakesTheCommittedFan() throws Exception {
        World w = new World();
        SugVertex v = buildWorld(w, true);
        w.solveAndEmit();
        Assert.assertTrue(w.refusals(v).toString(), w.refusals(v).contains(RTrackRefusal.NO_TARGET));
        Assert.assertTrue(w.engine.census(), w.engine.census().contains(" recvSink{cases=1 fellBack=1 "));
    }

    /**
     * The backward visited key carries the method context. Two
     * resumes into one sink at the same (frame, node, path) under two OWNER contexts are two routes: the parameter
     * case's owner shortcut resolves {@code this} to each context's owner atom, so the sink holds both. A
     * (frame, node, path) key would drop the second resume as visited, with no refusal (only owner A arriving). The same
     * context twice is still deduplicated.
     */
    @Test
    public void twoOwnerContextsAtOnePositionAreBothProcessed() throws Exception {
        World w = new World();
        AnalysisMethod self = w.u.method(Program.Owned.class, "self");
        LocalFlowGraph f = w.frame(self);
        ParameterNode recv = w.param(f, 0, Program.Owned.class);
        java.lang.reflect.Method intern = RecursiveTracking.class.getDeclaredMethod("internKey", Object.class, ContainerAtoms.HeapContext.class);
        intern.setAccessible(true);
        Object siteA = new Object();
        Object siteB = new Object();
        RecursiveTracking.RAtomKey keyA = (RecursiveTracking.RAtomKey) intern.invoke(w.engine, siteA, ContainerAtoms.HeapContext.EMPTY);
        RecursiveTracking.RAtomKey keyB = (RecursiveTracking.RAtomKey) intern.invoke(w.engine, siteB, ContainerAtoms.HeapContext.EMPTY);
        for (RecursiveTracking.RAtomKey k : List.of(keyA, keyB)) {
            w.engine.atoms.put(k, w.engine.new RAtom(k, RecursiveTracking.AtomKind.ALLOCATION, null, null, ContextPolicy.MethodContext.UNKNOWN, null, null, false));
        }
        ContextPolicy.MethodContext ownerA = ContextPolicy.MethodContext.owner(siteA, ContainerAtoms.HeapContext.EMPTY);
        ContextPolicy.MethodContext ownerB = ContextPolicy.MethodContext.owner(siteB, ContainerAtoms.HeapContext.EMPTY);
        ContainerTables.Sink sink = new ContainerTables.Sink("vkey-root", RecursiveTracking.BACKWARD_BUDGET, RecursiveTracking.TRACK_DEPTH_CAP);
        w.engine.backward(f, recv, ownerA, null, sink);
        w.engine.backward(f, recv, ownerB, null, sink);
        w.engine.backward(f, recv, ownerA, null, sink); // the same (position, context) again: deduplicated
        Assert.assertEquals("both owner contexts are processed: " + sink.atomsSnapshot(), List.of(keyA, keyB), sink.atomsSnapshot());
        Assert.assertEquals("one visited key per (position, context)", 2, sink.visited.size());
        Assert.assertFalse("no refusal", sink.refused());
    }

    /**
     * The accessed-field rule at the escape itself. The escape listener, on a receiver atom X, checks the stored
     * member: a reflectively/Unsafe/JNI-accessed field refuses T(X), and the string inherits it, although X's own
     * forward walk never reached the store (here X has no walk at all, so {@code recordStore}'s check never ran).
     */
    @Test
    public void escapeIntoReflectiveFieldRefusesWithoutTheHolderWalk() throws Exception {
        World w = new World();
        AnalysisField field = w.u.field(Program.Holder.class, "value");
        java.lang.reflect.Field flag = AnalysisField.class.getDeclaredField("isUnsafeAccessed");
        flag.setAccessible(true);
        flag.set(field, "unsafe-accessed test field"); // the accessed-field flag (Unsafe-accessed), set without a points-to engine
        Assert.assertTrue(field.isUnsafeAccessed());
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "build", String.class));
        java.lang.reflect.Method intern = RecursiveTracking.class.getDeclaredMethod("internKey", Object.class, ContainerAtoms.HeapContext.class);
        intern.setAccessible(true);
        RecursiveTracking.RAtomKey strKey = (RecursiveTracking.RAtomKey) intern.invoke(w.engine, new Object(), ContainerAtoms.HeapContext.EMPTY);
        RecursiveTracking.RAtomKey xKey = (RecursiveTracking.RAtomKey) intern.invoke(w.engine, new Object(), ContainerAtoms.HeapContext.EMPTY);
        RecursiveTracking.RAtom str = w.engine.new RAtom(strKey, RecursiveTracking.AtomKind.ALLOCATION, null, null, ContextPolicy.MethodContext.UNKNOWN, null, null, false);
        RecursiveTracking.RAtom x = w.engine.new RAtom(xKey, RecursiveTracking.AtomKind.ALLOCATION, null, null, ContextPolicy.MethodContext.UNKNOWN, null, null, false);
        w.engine.atoms.put(strKey, str);
        w.engine.atoms.put(xKey, x);
        java.lang.reflect.Method esc = RecursiveTracking.class.getDeclaredMethod("escapeListener", RecursiveTracking.RAtom.class, LocalFlowGraph.class, Object.class,
                        Object.class, ContextPolicy.CallPath.class);
        esc.setAccessible(true);
        ContainerTables.Listener l = (ContainerTables.Listener) esc.invoke(w.engine, str, f, new Object(), field, null);
        l.onAtom().accept(xKey); // the receiver sink resolved X
        do {
            w.engine.drain(); // the inheritance is a deferred delivery
        } while (w.engine.hasWork() || w.engine.roundBoundary());
        Assert.assertTrue("T(X) refused: " + x.table.refusalsSnapshot(), x.table.refusalsSnapshot().contains(RTrackRefusal.REFLECTIVE_FIELD));
        Assert.assertTrue("the string inherits it: " + str.table.refusalsSnapshot(), str.table.refusalsSnapshot().contains(RTrackRefusal.REFLECTIVE_FIELD));
    }

    /**
     * The static part of the visited key. A static frame's allocation reached by {@code backward}
     * under STATIC(c1) and STATIC(c2) with a null path mints one atom per context ({@code mintStatic}: the heap context
     * is the static chain's), so the sink holds both. A (frame, node, path) key, or an owner-only key (every
     * STATIC context collapsed to null), would drop the second resume as visited, with no refusal.
     */
    @Test
    public void twoStaticContextsAtOnePositionAreBothProcessed() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "fresh"));
        ValueNode alloc = World.graph(f).add(new jdk.graal.compiler.nodes.java.NewInstanceNode(w.u.type(Program.Holder.class), true));
        AnalysisMethod caller = w.u.method(Program.class, "caller", String.class);
        ContextPolicy.MethodContext c1 = ContextPolicy.MethodContext.staticCtx(new ContainerAtoms.ContextElement(caller, 1), null);
        ContextPolicy.MethodContext c2 = ContextPolicy.MethodContext.staticCtx(new ContainerAtoms.ContextElement(caller, 2), null);
        ContainerTables.Sink sink = new ContainerTables.Sink("vkey-static-root", RecursiveTracking.BACKWARD_BUDGET, RecursiveTracking.TRACK_DEPTH_CAP);
        w.engine.backward(f, alloc, c1, null, sink);
        w.engine.backward(f, alloc, c2, null, sink);
        w.engine.backward(f, alloc, c1, null, sink); // the same (position, context) again: deduplicated
        List<Object> atoms = sink.atomsSnapshot();
        Assert.assertEquals("both static contexts mint their atom: " + atoms, 2, atoms.size());
        Assert.assertNotEquals("distinct heap contexts: " + atoms, ((RecursiveTracking.RAtomKey) atoms.get(0)).context,
                        ((RecursiveTracking.RAtomKey) atoms.get(1)).context);
        Assert.assertEquals("one visited key per (position, context)", 2, sink.visited.size());
        Assert.assertFalse("no refusal", sink.refused());
    }

    // ---- the real-IR compareTo / equals argument rows ----

    /** A Phase-A call vertex with the given shape (the REDIRECT rule reads type, name, declaring class and signature). */
    private static SugVertex callVertex(World w, Invoke inv, String name, String decl, String sig) {
        SugVertex v = w.site(List.of("phaseA", inv), name + "@" + inv.bci());
        v.setMethodName(name);
        v.setDeclaringClass(decl);
        v.setMethodSignature(sig);
        return v;
    }

    /**
     * The walked string as the argument of {@code plain.<m>(s)} (String-declared {@code compareTo(String)} or
     * {@code equals(Object)}) at bci 6 of a user frame, with the target's own frame present (it would be entered).
     */
    private static SugVertex argumentOf(World w, AnalysisMethod target, Class<?> argType, java.util.function.Function<Invoke, SugVertex> phaseA) throws Exception {
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        ParameterNode plain = w.param(f, 1, String.class);
        InvokeNode call = w.invoke(f, InvokeKind.Virtual, target, 6, plain, s);
        LocalFlowGraph body = w.frame(target);
        w.param(body, 0, String.class);
        w.param(body, 1, argType);
        SugVertex site = phaseA.apply(call);
        if (site != null) {
            w.phaseASites.put(call, site);
        }
        SugVertex v = w.seed(f, "Program#seed@1", s);
        w.solveAndEmit();
        return v;
    }

    /**
     * A String atom as the argument of {@code String.compareTo(String)} at an invoke without a Phase-A vertex
     * (the parent could not REDIRECT it) reaches the real-IR NO_SITE branch: {@code COMPARETO_ARG_NO_SITE}, the body is
     * not entered. (No shape reaches it: every user-code String invoke has a Phase-A vertex, and the
     * reflective crossing is cut earlier by {@code CHA_FAN_CAP}.)
     */
    @Test
    public void compareToArgumentWithoutAPhaseASiteIsNoSite() throws Exception {
        World w = new World();
        long before = w.engine.cmpArgNoSite.get();
        SugVertex v = argumentOf(w, w.u.method(String.class, "compareTo", String.class), String.class, inv -> null);
        assertRefusedCandidate(w, v, RTrackRefusal.COMPARETO_ARG_NO_SITE);
        Assert.assertEquals("one NO_SITE row", before + 1, w.engine.cmpArgNoSite.get());
    }

    /** The REDIRECTable compareTo(String) vertex: the PARAMETER usage at slot 1 there (TERMINAL), no refusal. */
    @Test
    public void compareToArgumentAtARedirectableSiteIsATerminalParameterUsage() throws Exception {
        World w = new World();
        SugVertex v = argumentOf(w, w.u.method(String.class, "compareTo", String.class), String.class,
                        inv -> callVertex(w, inv, "compareTo", "java.lang.String", "Ljava/lang/String;"));
        Assert.assertEquals("no refusal: " + w.refusals(v), List.of(), w.refusals(v));
        Assert.assertEquals(List.of("compareTo@6:PARAMETER:1"), w.usages(v));
        Assert.assertEquals(0, w.engine.argSiteNotRedirectable.get());
    }

    /**
     * A Phase-A vertex at the call that the REDIRECT rule would not mark (here: the bridge-shaped
     * {@code compareTo(Ljava/lang/Object;)} signature) is no site: refused, counted in {@code argSiteNotRedir}.
     */
    @Test
    public void compareToArgumentAtANonRedirectableVertexIsNoSite() throws Exception {
        World w = new World();
        SugVertex v = argumentOf(w, w.u.method(String.class, "compareTo", String.class), String.class,
                        inv -> callVertex(w, inv, "compareTo", "java.lang.String", "Ljava/lang/Object;"));
        assertRefusedCandidate(w, v, RTrackRefusal.COMPARETO_ARG_NO_SITE);
        Assert.assertEquals(1, w.engine.argSiteNotRedirectable.get());
    }

    /** The same for equals: the REDIRECTable equals(Object) vertex is TERMINAL, another is no site. */
    @Test
    public void equalsArgumentNeedsARedirectableVertex() throws Exception {
        World ok = new World();
        SugVertex v = argumentOf(ok, ok.u.method(String.class, "equals", Object.class), Object.class,
                        inv -> callVertex(ok, inv, "equals", "java.lang.String", "Ljava/lang/Object;"));
        Assert.assertEquals("no refusal: " + ok.refusals(v), List.of(), ok.refusals(v));
        Assert.assertEquals(List.of("equals@6:PARAMETER:1"), ok.usages(v));
        World bad = new World();
        SugVertex u = argumentOf(bad, bad.u.method(String.class, "equals", Object.class), Object.class,
                        inv -> callVertex(bad, inv, "equals", "java.lang.String", "(Ljava/lang/Object;)")); // the Objects.equals shape
        assertRefusedCandidate(bad, u, RTrackRefusal.EQUALS_ARG_NO_SITE);
        Assert.assertEquals(1, bad.engine.argSiteNotRedirectable.get());
    }

    // ---- the stack-confinement flag (RAtom.strStored -> SugVertex.isStored) end to end ----

    /** A string that is only read (a terminal usage) is not stored: the vertex stays unmarked. */
    @Test
    public void aReadOnlyStringIsNotStored() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        w.invoke(f, InvokeKind.Virtual, w.u.method(String.class, "length"), 7, s);
        SugVertex v = w.seed(f, "Program#seed@1", s);
        w.solveAndEmit();
        Assert.assertFalse(w.atom(v).strStored);
        Assert.assertFalse(v.isStored());
    }

    /** A static-field store of the string (escape -> escapeIntoStatic) marks the vertex stored. */
    @Test
    public void aStaticStoreMarksTheStringStored() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        World.graph(f).addWithoutUnique(new StoreFieldNode(null, w.u.staticField(Program.class, "last"), s));
        SugVertex v = w.seed(f, "Program#seed@1", s);
        w.solveAndEmit();
        Assert.assertTrue(w.atom(v).strStored);
        Assert.assertTrue(v.isStored());
    }

    /** An instance-field store of the string (escape -> escapeInto) marks the vertex stored, whatever the holder resolves to. */
    @Test
    public void anInstanceFieldStoreMarksTheStringStored() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "two", Object.class, String.class));
        ParameterNode holder = w.param(f, 0, Program.Holder.class);
        ParameterNode s = w.param(f, 1, String.class);
        World.graph(f).addWithoutUnique(new StoreFieldNode(holder, w.u.field(Program.Holder.class, "value"), s));
        SugVertex v = w.seed(f, "Program#two@1", s);
        w.solveAndEmit();
        Assert.assertTrue(w.atom(v).strStored);
        Assert.assertTrue(v.isStored());
    }

    /**
     * The routes whose early returns precede any walk still mark the atom: a VM thread-local store with an
     * unresolvable identity (vmtlEscape refuses and returns) and the static helper itself (STRING atoms only, monotone).
     */
    @Test
    public void earlyReturningRoutesStillMarkTheString() throws Exception {
        World w = new World();
        LocalFlowGraph f = w.frame(w.u.method(Program.class, "seed", String.class));
        ParameterNode s = w.param(f, 0, String.class);
        SugVertex v = w.seed(f, "Program#seed@1", s);
        w.solveAndEmit();
        RecursiveTracking.RAtom a = w.atom(v);
        Assert.assertFalse(a.strStored);
        java.lang.reflect.Method vmtl = ThreadLocalModel.class.getDeclaredMethod("vmtlEscape", RecursiveTracking.RAtom.class, Object.class);
        vmtl.setAccessible(true);
        vmtl.invoke(w.engine.threadLocal, a, null);
        Assert.assertTrue("vmtlEscape marks before its identity check", a.strStored);
        RecursiveTracking.markStored(a);
        Assert.assertTrue("monotone", a.strStored);
        java.lang.reflect.Method intern = RecursiveTracking.class.getDeclaredMethod("internKey", Object.class, ContainerAtoms.HeapContext.class);
        intern.setAccessible(true);
        RecursiveTracking.RAtomKey k = (RecursiveTracking.RAtomKey) intern.invoke(w.engine, new Object(), ContainerAtoms.HeapContext.EMPTY);
        RecursiveTracking.RAtom container = w.engine.new RAtom(k, RecursiveTracking.AtomKind.ALLOCATION, null, null, ContextPolicy.MethodContext.UNKNOWN, null, null, false);
        RecursiveTracking.markStored(container);
        Assert.assertFalse("a container atom carries no confinement flag", container.strStored);
    }

    /**
     * {@code AccumulatorHeuristic.applyTwoPass} reads the emitted mark. Three admitted extractions
     * (hand-built vertices; the engine -> {@code SugVertex.markStored} path is pinned by the rows above) of one
     * only-growing accumulator each, every one read only through {@code String.length()} (W_view): an unmarked one is
     * {@code ACCUMULATOR_VIEW_SHARED}; a marked one ({@code markStored}, as the emit sets it) is plain
     * {@code ACCUMULATOR_VIEW}; an unmarked one whose other usage is a leak-marked terminal outside W_view at the
     * PARAMETER role (which the String View check skips), reached through an internal call, is plain too (the graph walk
     * of {@code leakMarkedOutsideWhitelist}, with a cycle the visited set ends).
     */
    @Test
    public void applyTwoPassEmitsSharedOnlyForAnUnstoredExtraction() throws Exception {
        World w = new World();
        SugVertex length = w.sug.newVertex();
        length.setNodeType(SugNodeType.STRING_METHOD_CALL);
        length.setDeclaringClass("java.lang.String");
        length.setMethodName("length");
        length.setMethodSignature("");
        Assert.assertTrue(StringViewWhitelist.isWhitelistedUsage("length", "java.lang.String", ""));
        SugVertex read = w.sug.newVertex();
        read.setNodeType(SugNodeType.STRING_METHOD_CALL);
        read.setSourceLocation("Program#read@3");
        SugVertex stored = w.sug.newVertex();
        stored.setNodeType(SugNodeType.STRING_METHOD_CALL);
        stored.setSourceLocation("Program#stored@3");
        stored.markStored();
        // the hand-built third extraction: x -> <init> (an internal call, followed) -> String.replaceAll(regex, x) as PARAMETER
        SugVertex leaky = w.sug.newVertex();
        leaky.setNodeType(SugNodeType.STRING_METHOD_CALL);
        leaky.setSourceLocation("Program#leaky@3");
        SugVertex init = w.sug.newVertex();
        init.setNodeType(SugNodeType.JDK_LIBRARY_CALL);
        init.setDeclaringClass("app.Wrapper");
        init.setMethodName("<init>");
        init.setMethodSignature("Ljava/lang/String;");
        SugVertex replaceAll = w.sug.newVertex();
        replaceAll.setNodeType(SugNodeType.STRING_METHOD_CALL);
        replaceAll.setDeclaringClass("java.lang.String");
        replaceAll.setMethodName("replaceAll");
        replaceAll.setMethodSignature("Ljava/lang/String;,Ljava/lang/String;");
        Assert.assertTrue("the fixture's terminal is leak-marked and outside W_view",
                        AccumulatorHeuristic.isLeakMarkedOutsideWhitelist("java.lang.String", "replaceAll", "Ljava/lang/String;,Ljava/lang/String;"));
        List<UsageTag> tags = new ArrayList<>(w.sug.getUsageTags() == null ? List.of() : w.sug.getUsageTags());
        int iLen = tags.size();
        tags.add(new UsageTag(length, UsageRole.RECEIVER, 0));
        int iInit = tags.size();
        tags.add(new UsageTag(init, UsageRole.PARAMETER, 1));
        int iRepl = tags.size();
        tags.add(new UsageTag(replaceAll, UsageRole.PARAMETER, 2));
        w.sug.setUsageTags(tags);
        w.sug.setUsageSourceBuilt();
        for (SugVertex x : List.of(read, stored)) {
            java.util.BitSet rt = new java.util.BitSet();
            rt.set(iLen);
            x.setUsageTags(rt);
        }
        java.util.BitSet lt = new java.util.BitSet();
        lt.set(iLen);
        lt.set(iInit);
        leaky.setUsageTags(lt);
        java.util.BitSet it = new java.util.BitSet();
        it.set(iRepl);
        it.set(iInit); // a cycle through the internal call: the visited set ends it
        init.setUsageTags(it);
        Assert.assertEquals("java.lang.String.replaceAll(Ljava/lang/String;,Ljava/lang/String;)",
                        AccumulatorHeuristic.leakMarkedOutsideWhitelist(w.sug, leaky, new java.util.HashSet<>()));
        Assert.assertNull(AccumulatorHeuristic.leakMarkedOutsideWhitelist(w.sug, read, new java.util.HashSet<>()));

        AnalysisType accType = w.u.type(Program.Holder.class);
        Map<SugVertex, String> want = new java.util.LinkedHashMap<>();
        want.put(read, AccumulatorHeuristic.accVariant(false));
        want.put(stored, "ACCUMULATOR_VIEW");
        want.put(leaky, "ACCUMULATOR_VIEW");
        for (SugVertex x : want.keySet()) {
            SugVertex acc = w.sug.newVertex();
            acc.setNodeType(SugNodeType.NEW_ACCUMULATOR);
            acc.markEmittedAtom();
            acc.setEnclosingClassName("app.Main");
            acc.setSourceLocation("app.Main#acc@" + acc.getId());
            acc.setJavaType(accType); // a type of this test universe (the variant does not depend on the class)
            w.sug.accExtractionReceivers().put(x, Set.of(acc));
        }
        AccumulatorHeuristic h = new AccumulatorHeuristic(true);
        List<InstrumentationDecision> ds = h.apply(w.sug);
        Map<SugVertex, String> got = new java.util.LinkedHashMap<>();
        for (InstrumentationDecision d : ds) {
            Assert.assertEquals(OptimizationType.STRING_VIEW, d.getType());
            Assert.assertEquals(accType.toJavaName(true), d.getAccumulatorClass());
            got.put(d.getCandidate(), d.getVariant());
        }
        Assert.assertEquals("rejections " + h.getRejections(), want, got);
        Assert.assertEquals("the read-only extraction is shared", "ACCUMULATOR_VIEW_SHARED", got.get(read));
    }
}
