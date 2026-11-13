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

import java.io.IOException;
import java.io.InputStream;
import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.ParsingReason;
import com.oracle.svm.core.util.UserError;
import com.oracle.svm.hosted.stringanalysis.OffStringFinalBindingPlugin.Decision;
import com.oracle.svm.hosted.stringanalysis.OffStringFinalBindingPlugin.Receiver;

import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration.Plugins;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugins;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The OFF parse-time String binding. Pins: (1) the
 * registration predicate: the binding applies only with the knob on, no string-analysis mode, fork/child role or profile, a
 * closed type world, no layered build and no runtime class loading; (2) the knob default is on; (3) the registration
 * helper registers only for the analysis parse and only when the predicate holds, and the feature registers only
 * through it, with appliesToThisBuild; (3b) every branch of the per-invoke binding decision; (4) the afterAnalysis soundness check names every instantiated strict subtype of String and fails the build
 * (UserError), and is silent otherwise; (5) the plugin leaves already-bound (Special/Static) invokes alone.
 */
public class OffStringFinalBindingTest {

    /** appliesTo with every argument at its "applies" value except the named overrides. */
    private static boolean applies(String off) {
        return OffStringFinalBindingPlugin.appliesTo(!off.equals("knob"), off.equals("sa"), off.equals("fork"), off.equals("childOnly"), off.equals("modeOnly"),
                        off.equals("profileOption") ? "/tmp/p.txt" : null, off.equals("profileLoaded"), !off.equals("openWorld"), off.equals("layered"),
                        off.equals("runtimeClassLoading"));
    }

    @Test
    public void appliesOnlyWithoutAnyStringAnalysisModeOrProfileInAClosedNonLayeredWorld() {
        Assert.assertTrue(applies(""));
        for (String off : new String[]{"knob", "sa", "fork", "childOnly", "modeOnly", "profileOption", "profileLoaded", "openWorld", "layered", "runtimeClassLoading"}) {
            Assert.assertFalse(off, applies(off));
        }
    }

    /** The registration helper the feature calls: analysis parse only, and only when the predicate holds. */
    @Test
    public void registrationIsGuardedByReasonAndPredicate() {
        boolean saved = OffStringFinalBindingPlugin.registered;
        try {
            for (ParsingReason reason : ParsingReason.values()) {
                for (boolean applies : new boolean[]{false, true}) {
                    OffStringFinalBindingPlugin.registered = false;
                    Plugins plugins = new Plugins(new InvocationPlugins());
                    NodePlugin earlier = new NodePlugin() {
                    };
                    plugins.appendNodePlugin(earlier);
                    int[] asked = {0};
                    boolean r = OffStringFinalBindingPlugin.registerIfApplies(reason, () -> {
                        asked[0]++;
                        return applies;
                    }, plugins);
                    boolean expect = reason == ParsingReason.PointsToAnalysis && applies;
                    String what = reason + " applies=" + applies;
                    NodePlugin[] now = plugins.getNodePlugins();
                    Assert.assertEquals(what, expect, r);
                    Assert.assertEquals(what, expect, OffStringFinalBindingPlugin.registered);
                    Assert.assertEquals(what, expect ? 2 : 1, now.length);
                    Assert.assertSame("prepended: " + what, expect ? now[1] : now[0], earlier);
                    if (expect) {
                        Assert.assertTrue(what, now[0] instanceof OffStringFinalBindingPlugin);
                    }
                    Assert.assertEquals("the predicate is evaluated for the analysis parse only: " + what, reason == ParsingReason.PointsToAnalysis ? 1 : 0, asked[0]);
                }
            }
        } finally {
            OffStringFinalBindingPlugin.registered = saved;
        }
    }

    @Test
    public void knobDefaultIsOn() {
        Assert.assertNull("the test JVM must not set the knob", System.getProperty("svm.stringanalysis.off.stringfinal"));
        Assert.assertTrue(OffStringFinalBindingPlugin.ENABLED);
    }

    /**
     * The feature creates no plugin itself: its only use of the plugin class in registerGraphBuilderPlugins is one
     * registerIfApplies call (whose guard registrationIsGuardedByReasonAndPredicate pins) with appliesToThisBuild as
     * the predicate; the plugin is instantiated only inside registerIfApplies.
     */
    @Test
    public void featureRegistersOnlyThroughTheGuardedHelper() throws IOException {
        String feature = "com/oracle/svm/hosted/stringanalysis/StringAnalysisFeature";
        String plugin = "com/oracle/svm/hosted/stringanalysis/OffStringFinalBindingPlugin";
        int helperCalls = 0;
        int zeroAdmitCalls = 0;
        boolean predicateRef = false;
        boolean zeroAdmitPredicateRef = false;
        for (MethodModel m : ClassFile.of().parse(classBytes(feature)).methods()) {
            for (CodeElement e : m.code().map(c -> c.elementList()).orElse(List.of())) {
                Assert.assertFalse("the feature must not create the plugin itself", e instanceof NewObjectInstruction n && n.className().asInternalName().equals(plugin));
                if (e instanceof InvokeInstruction i && i.owner().asInternalName().equals(plugin) && i.name().equalsString("registerIfApplies")) {
                    helperCalls++;
                    Assert.assertEquals("registerGraphBuilderPlugins", m.methodName().stringValue());
                }
                if (e instanceof InvokeInstruction i && i.owner().asInternalName().equals(plugin) && i.name().equalsString("registerZeroAdmitIfApplies")) {
                    zeroAdmitCalls++; // the zero-admit registration, guarded the same way
                    Assert.assertEquals("registerGraphBuilderPlugins", m.methodName().stringValue());
                }
                if (e instanceof InvokeDynamicInstruction indy && m.methodName().equalsString("registerGraphBuilderPlugins")) {
                    for (java.lang.constant.ConstantDesc arg : indy.bootstrapArgs()) {
                        if (arg instanceof java.lang.constant.DirectMethodHandleDesc mh && mh.methodName().equals("appliesToThisBuild") &&
                                        mh.owner().descriptorString().equals("L" + plugin + ";")) {
                            predicateRef = true;
                        }
                        if (arg instanceof java.lang.constant.DirectMethodHandleDesc mh && mh.methodName().equals("appliesToZeroAdmitThisBuild") &&
                                        mh.owner().descriptorString().equals("L" + plugin + ";")) {
                            zeroAdmitPredicateRef = true;
                        }
                    }
                }
            }
        }
        Assert.assertEquals("exactly one registration site", 1, helperCalls);
        Assert.assertTrue("the predicate passed is appliesToThisBuild", predicateRef);
        Assert.assertEquals("exactly one zero-admit registration site", 1, zeroAdmitCalls);
        Assert.assertTrue("the zero-admit predicate passed is appliesToZeroAdmitThisBuild", zeroAdmitPredicateRef);
        /* inside the plugin class, only the two guarded helpers create an instance */
        int creations = 0;
        for (MethodModel m : ClassFile.of().parse(classBytes(plugin)).methods()) {
            for (CodeElement e : m.code().map(c -> c.elementList()).orElse(List.of())) {
                if (e instanceof NewObjectInstruction n && n.className().asInternalName().equals(plugin)) {
                    creations++;
                    Assert.assertTrue(m.methodName().stringValue(), m.methodName().equalsString("registerIfApplies") || m.methodName().equalsString("registerZeroAdmitIfApplies"));
                }
            }
        }
        Assert.assertEquals(2, creations);
    }

    private static byte[] classBytes(String internalName) throws IOException {
        try (InputStream in = OffStringFinalBindingTest.class.getResourceAsStream("/" + internalName + ".class")) {
            Assert.assertNotNull(internalName, in);
            return in.readAllBytes();
        }
    }

    /** decide: every branch, in the order the plugin checks them. */
    @Test
    public void bindingDecisionBranches() {
        Receiver str = Receiver.STRING;
        Receiver other = Receiver.OTHER;
        Receiver sub = Receiver.STRICT_SUBTYPE;
        InvokeKind v = InvokeKind.Virtual;
        /* the bindable baselines */
        Assert.assertEquals(Decision.BIND_R1, decide(v, true, other, true, false, false, false, true));
        Assert.assertEquals(Decision.BIND_R1, decide(v, true, str, true, false, false, false, true));
        Assert.assertEquals(Decision.BIND_R2, decide(InvokeKind.Interface, false, str, true, false, false, false, true));
        Assert.assertEquals(Decision.BIND_R2, decide(v, false, str, true, false, false, false, true));
        /* not indirect / no receiver */
        for (InvokeKind k : new InvokeKind[]{InvokeKind.Special, InvokeKind.Static, null}) {
            Assert.assertEquals(Decision.NOT_INDIRECT, decide(k, true, str, true, false, false, false, true));
        }
        Assert.assertEquals(Decision.NOT_INDIRECT, OffStringFinalBindingPlugin.decide(v, 0, true, str, true, false, false, false, () -> true));
        /* neither R1 nor R2 */
        Assert.assertEquals(Decision.NOT_STRING, decide(v, false, other, true, false, false, false, true));
        Assert.assertEquals(Decision.NOT_STRING, decide(v, false, sub, true, false, false, false, true));
        /* a rep receiver on a String-declared target */
        Assert.assertEquals(Decision.SKIP_REP_RECEIVER, decide(v, true, sub, true, false, false, false, true));
        /* not the bytecode parser / an intrinsic */
        Assert.assertEquals(Decision.SKIP_NOT_PARSER, decide(v, true, str, false, false, false, false, true));
        Assert.assertEquals(Decision.SKIP_NOT_PARSER, decide(v, false, str, true, true, false, false, true));
        /* a null-constant receiver */
        Assert.assertEquals(Decision.SKIP_NULL_CONSTANT, decide(v, true, str, true, false, true, false, true));
        /* an interface caller (the correctness-critical skip) */
        Assert.assertEquals(Decision.SKIP_INTERFACE_CALLER, decide(v, true, other, true, false, false, true, true));
        Assert.assertEquals(Decision.SKIP_INTERFACE_CALLER, decide(InvokeKind.Interface, false, str, true, false, false, true, true));
        /* unresolved / abstract target */
        Assert.assertEquals(Decision.SKIP_UNRESOLVED, decide(v, true, str, true, false, false, false, false));
        /* only the bind/skip-unresolved outcomes resolve the target; only BIND_* binds */
        for (Decision d : Decision.values()) {
            Assert.assertEquals(d.name(), d == Decision.BIND_R1 || d == Decision.BIND_R2, d.binds());
        }
        int[] resolved = {0};
        OffStringFinalBindingPlugin.decide(v, 1, true, str, true, false, false, true, () -> {
            resolved[0]++;
            return true;
        });
        OffStringFinalBindingPlugin.decide(v, 1, true, sub, true, false, false, false, () -> {
            resolved[0]++;
            return true;
        });
        Assert.assertEquals("the target is not resolved for a skipped invoke", 0, resolved[0]);
    }

    private static Decision decide(InvokeKind kind, boolean declaredByString, Receiver receiver, boolean bytecodeParser, boolean parsingIntrinsic, boolean nullConstant,
                    boolean callerIsInterface, boolean targetConcrete) {
        return OffStringFinalBindingPlugin.decide(kind, 1, declaredByString, receiver, bytecodeParser, parsingIntrinsic, nullConstant, callerIsInterface, () -> targetConcrete);
    }

    /** A proxy ResolvedJavaType: a name, a String-subtype flag; answers equals/hashCode/toJavaName/isAssignableFrom. */
    private static ResolvedJavaType type(String name, Set<String> stringSubtypes) {
        return (ResolvedJavaType) Proxy.newProxyInstance(OffStringFinalBindingTest.class.getClassLoader(), new Class<?>[]{ResolvedJavaType.class}, (proxy, method, args) -> {
            switch (method.getName()) {
                case "equals":
                    return proxy == args[0];
                case "hashCode":
                    return System.identityHashCode(proxy);
                case "toJavaName":
                case "toString":
                    return name;
                case "isAssignableFrom":
                    /* only the String proxy is asked: is args[0] String or a subtype of it */
                    Assert.assertEquals("java.lang.String", name);
                    String other = ((ResolvedJavaType) args[0]).toJavaName();
                    return other.equals(name) || stringSubtypes.contains(other);
                default:
                    throw new AssertionError("unexpected call " + method.getName());
            }
        });
    }

    @Test
    public void soundnessCheckFailsOnAnInstantiatedStringSubtype() {
        Set<String> subs = Set.of("p.Rep", "p.DeadRep");
        ResolvedJavaType string = type("java.lang.String", subs);
        ResolvedJavaType rep = type("p.Rep", subs);
        ResolvedJavaType deadRep = type("p.DeadRep", subs);
        ResolvedJavaType other = type("p.Other", subs);
        Set<String> instantiated = Set.of("java.lang.String", "p.Rep", "p.Other");
        List<ResolvedJavaType> all = List.of(string, rep, deadRep, other);
        Assert.assertEquals(List.of("p.Rep"), OffStringFinalBindingPlugin.instantiatedStringSubtypes(all, string, t -> instantiated.contains(t.toJavaName())));
        try {
            OffStringFinalBindingPlugin.checkNoInstantiatedStringSubtype(all, string, t -> instantiated.contains(t.toJavaName()));
            Assert.fail("the build must fail");
        } catch (UserError.UserException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("p.Rep") && e.getMessage().contains("svm.stringanalysis.off.stringfinal=0"));
        }
        /* String itself and non-instantiated subtypes are fine */
        OffStringFinalBindingPlugin.checkNoInstantiatedStringSubtype(all, string, t -> !subs.contains(t.toJavaName()));
    }

    @Test
    public void boundInvokesAreLeftAlone() {
        for (InvokeKind k : new InvokeKind[]{InvokeKind.Special, InvokeKind.Static, null}) {
            List<String> touched = new ArrayList<>();
            GraphBuilderContext b = (GraphBuilderContext) Proxy.newProxyInstance(OffStringFinalBindingTest.class.getClassLoader(), new Class<?>[]{GraphBuilderContext.class},
                            (proxy, method, args) -> {
                                switch (method.getName()) {
                                    case "getInvokeKind":
                                        return k;
                                    case "equals":
                                        return proxy == args[0];
                                    case "hashCode":
                                        return System.identityHashCode(proxy);
                                    default:
                                        touched.add(method.getName());
                                        throw new AssertionError("touched " + method.getName());
                                }
                            });
            ResolvedJavaMethod m = (ResolvedJavaMethod) Proxy.newProxyInstance(OffStringFinalBindingTest.class.getClassLoader(), new Class<?>[]{ResolvedJavaMethod.class},
                            (proxy, method, args) -> {
                                throw new AssertionError("touched the method: " + method.getName());
                            });
            Assert.assertFalse(new OffStringFinalBindingPlugin(false).handleInvoke(b, m, new ValueNode[1]));
            Assert.assertTrue(touched.toString(), touched.isEmpty());
        }
    }
}
