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

import java.io.DataInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.annotation.Annotation;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.FixedWithNextNode;
import jdk.graal.compiler.nodes.InvokeNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.AddNode;
import jdk.graal.compiler.nodes.calc.SubNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Guards for the unit-range proof (an instance final has no rule of its own), the SBS-only orchestrator filter, the
 * rep-allocation hook calls in {@code SimulateClassInitializerGraphDecoder} and the SB-pool premise ({@code POOL} is
 * not {@code @Stable}).
 */
public class UnitRangeAndPoolGuardsTest {

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    @SuppressWarnings("unused") private int mutablePos;
    @SuppressWarnings("unused") private volatile int volatilePos;
    @SuppressWarnings("unused") private final int finalPos = 3;
    @SuppressWarnings("unused") private static int staticMutablePos;
    @SuppressWarnings("unused") private static final int STATIC_FINAL_POS = Integer.getInteger("c95.r1.unused", 4);

    private ResolvedJavaField field(String name) throws NoSuchFieldException {
        return metaAccess.lookupJavaField(UnitRangeAndPoolGuardsTest.class.getDeclaredField(name));
    }

    private static ValueNode receiver(int index) {
        return new ParameterNode(index, StampPair.createSingle(StampFactory.object()));
    }

    private static ValueNode load(ValueNode object, ResolvedJavaField f) {
        return LoadFieldNode.create(null, object, f);
    }

    private static ValueNode plusOne(ValueNode x) {
        return new AddNode(x, ConstantNode.forInt(1));
    }

    // ---- the unit-range proof -----------------------------------------------------------------------------------

    @Test
    public void sameNodeIsAUnitRange() {
        ValueNode i = new ParameterNode(1, StampPair.createSingle(StampFactory.forInteger(32)));
        Assert.assertTrue(StringAnalysisCapturePlugin.isUnitRange(i, plusOne(i), false));
        Assert.assertTrue(StringAnalysisCapturePlugin.isUnitRange(i, new AddNode(ConstantNode.forInt(1), i), false));
        Assert.assertTrue(StringAnalysisCapturePlugin.isUnitRange(new SubNode(i, ConstantNode.forInt(1)), i, false));
        Assert.assertTrue("node identity holds in an initializer too", StringAnalysisCapturePlugin.isUnitRange(i, plusOne(i), true));
    }

    @Test
    public void twoUnchainedLoadsOfAMutableFieldAreNotOneValue() throws Exception {
        ValueNode thiz = receiver(0);
        ResolvedJavaField pos = field("mutablePos");
        // two loads with no proven kill-free chain between them (here: unattached) are two values
        Assert.assertFalse(StringAnalysisCapturePlugin.isUnitRange(load(thiz, pos), plusOne(load(thiz, pos)), false));
        Assert.assertFalse(StringAnalysisCapturePlugin.isUnitRange(new SubNode(load(thiz, pos), ConstantNode.forInt(1)), load(thiz, pos), false));
        ResolvedJavaField spos = field("staticMutablePos");
        Assert.assertFalse(StringAnalysisCapturePlugin.isUnitRange(load(null, spos), plusOne(load(null, spos)), false));
        // the same load node used twice is one value
        ValueNode once = load(thiz, pos);
        Assert.assertTrue(StringAnalysisCapturePlugin.isUnitRange(once, plusOne(once), false));
    }

    @Test
    public void twoUnchainedLoadsOfAStaticFinalAreOneValueOutsideInitializersButAnInstanceFinalIsNot() throws Exception {
        ValueNode thiz = receiver(0);
        ResolvedJavaField fin = field("finalPos");
        // An instance final has no rule of its own (Field.set/Unsafe/readObject can write it)
        Assert.assertFalse("instance final, unchained", StringAnalysisCapturePlugin.isUnitRange(load(thiz, fin), plusOne(load(thiz, fin)), false));
        Assert.assertFalse("different receivers", StringAnalysisCapturePlugin.isUnitRange(load(thiz, fin), plusOne(load(receiver(1), fin)), false));
        Assert.assertFalse(StringAnalysisCapturePlugin.isUnitRange(load(thiz, fin), plusOne(load(thiz, fin)), true));
        ResolvedJavaField sfin = field("STATIC_FINAL_POS");
        Assert.assertTrue(StringAnalysisCapturePlugin.isUnitRange(load(null, sfin), plusOne(load(null, sfin)), false));
        Assert.assertFalse("in an initializer a final field may be assigned between the loads",
                        StringAnalysisCapturePlugin.isUnitRange(load(null, sfin), plusOne(load(null, sfin)), true));
    }

    /** A static invoke of {@link #sideEffect()} (a memory kill of any location). */
    private InvokeNode invoke(StructuredGraph g) throws NoSuchMethodException {
        ResolvedJavaMethod m = metaAccess.lookupJavaMethod(UnitRangeAndPoolGuardsTest.class.getDeclaredMethod("sideEffect"));
        MethodCallTargetNode target = g.add(new MethodCallTargetNode(InvokeKind.Static, m, new ValueNode[0], StampPair.createSingle(StampFactory.forVoid()), null));
        return g.add(new InvokeNode(target, 0));
    }

    @SuppressWarnings("unused")
    private static void sideEffect() {
    }

    @Test
    public void anInvokeBetweenTwoLoadsOfAnInstanceFinalMakesThemTwoValues() throws Exception {
        // int p = this.f; in.defaultReadObject(); s.substring(p, this.f + 1): the invoke may write f
        StructuredGraph g = graph();
        ValueNode thiz = g.addOrUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull())));
        ResolvedJavaField fin = field("finalPos");
        ValueNode[] r = chain(g, thiz, fin, invoke(g));
        Assert.assertFalse("instance final, invoke between the loads", StringAnalysisCapturePlugin.isUnitRange(r[0], r[1], false));
        // without the invoke, rule 2 (no kill on a straight chain) still makes them one read
        StructuredGraph g2 = graph();
        ValueNode thiz2 = g2.addOrUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull())));
        ValueNode[] r2 = chain(g2, thiz2, fin);
        Assert.assertTrue("instance final, adjacent loads", StringAnalysisCapturePlugin.isUnitRange(r2[0], r2[1], false));
        // a static final keeps rule 3 across an invoke (outside an initializer only)
        StructuredGraph g3 = graph();
        ValueNode[] r3 = chain(g3, null, field("STATIC_FINAL_POS"), invoke(g3));
        Assert.assertTrue("static final, invoke between the loads", StringAnalysisCapturePlugin.isUnitRange(r3[0], r3[1], false));
        StructuredGraph g4 = graph();
        ValueNode[] r4 = chain(g4, null, field("STATIC_FINAL_POS"), invoke(g4));
        Assert.assertFalse("static final, invoke between the loads, in an initializer", StringAnalysisCapturePlugin.isUnitRange(r4[0], r4[1], true));
    }

    private static StructuredGraph graph() {
        OptionValues options = new OptionValues(EconomicMap.create());
        return new StructuredGraph.Builder(options, new DebugContext.Builder(options).build()).name("UnitRangeAndPoolGuardsTest").build();
    }

    /** {@code [load1, middle..., load2]} chained after the graph's start node; returns {start, end} value pair. */
    private ValueNode[] chain(StructuredGraph g, ValueNode thiz, ResolvedJavaField f, FixedWithNextNode... middle) {
        LoadFieldNode l1 = g.add(LoadFieldNode.create(null, thiz, f));
        LoadFieldNode l2 = g.add(LoadFieldNode.create(null, thiz, f));
        FixedWithNextNode last = g.start();
        last.setNext(l1);
        last = l1;
        for (FixedWithNextNode m : middle) {
            last.setNext(m);
            last = m;
        }
        last.setNext(l2);
        return new ValueNode[]{l1, g.addOrUnique(new AddNode(l2, g.addOrUnique(ConstantNode.forInt(1))))};
    }

    @Test
    public void twoLoadsOfAMutableFieldWithNoKillBetweenAreOneRead() throws Exception {
        StructuredGraph g = graph();
        ValueNode thiz = g.addOrUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull())));
        ValueNode[] r = chain(g, thiz, field("mutablePos"));
        Assert.assertTrue("s.substring(index, index + 1): adjacent loads, the JSON-parser pattern", StringAnalysisCapturePlugin.isUnitRange(r[0], r[1], false));
        Assert.assertTrue("also inside an initializer (no write between them)", StringAnalysisCapturePlugin.isUnitRange(r[0], r[1], true));
    }

    @Test
    public void aStoreBetweenTwoLoadsMakesThemTwoValues() throws Exception {
        StructuredGraph g = graph();
        ValueNode thiz = g.addOrUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull())));
        ResolvedJavaField pos = field("mutablePos");
        // s.substring(pos++, pos + 1): load, store pos+1, load
        StoreFieldNode store = g.add(new StoreFieldNode(thiz, pos, g.addOrUnique(ConstantNode.forInt(7))));
        ValueNode[] r = chain(g, thiz, pos, store);
        Assert.assertFalse(StringAnalysisCapturePlugin.isUnitRange(r[0], r[1], false));
        // a volatile read in between is a synchronization action (a kill of any location)
        StructuredGraph g2 = graph();
        ValueNode thiz2 = g2.addOrUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull())));
        LoadFieldNode vol = g2.add(LoadFieldNode.create(null, thiz2, field("volatilePos")));
        ValueNode[] r2 = chain(g2, thiz2, pos, vol);
        Assert.assertFalse(StringAnalysisCapturePlugin.isUnitRange(r2[0], r2[1], false));
        // two loads of a volatile field are never one read
        StructuredGraph g3 = graph();
        ValueNode thiz3 = g3.addOrUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull())));
        ValueNode[] r3 = chain(g3, thiz3, field("volatilePos"));
        Assert.assertFalse(StringAnalysisCapturePlugin.isUnitRange(r3[0], r3[1], false));
    }

    // ---- the mode filter ---------------------------------------------------------------------------------------

    @Test
    public void singleByteOnlyKeepsOnlySingleByteDecisions() {
        List<InstrumentationDecision> sb = new ArrayList<>();
        List<InstrumentationDecision> sv = new ArrayList<>();
        List<InstrumentationDecision> lc = new ArrayList<>();
        List<InstrumentationDecision> acc = new ArrayList<>();
        StringAnalysisFeature.OrchestratorInputs all = StringAnalysisFeature.orchestratorInputs(false, false, false, sb, sv, lc, acc);
        Assert.assertSame(sb, all.sb());
        Assert.assertSame(sv, all.sv());
        Assert.assertSame(lc, all.lc());
        Assert.assertSame(acc, all.acc());

        StringAnalysisFeature.OrchestratorInputs sbs = StringAnalysisFeature.orchestratorInputs(false, false, true, sb, sv, lc, acc);
        Assert.assertSame(sb, sbs.sb());
        Assert.assertNotSame("SBS must drop the StringView decisions", sv, sbs.sv());
        Assert.assertNotSame("SBS must drop the LazyConcat decisions", lc, sbs.lc());
        Assert.assertNotSame("SBS must drop the accumulator decisions", acc, sbs.acc());
        Assert.assertTrue(sbs.sv().isEmpty() && sbs.lc().isEmpty() && sbs.acc().isEmpty());

        StringAnalysisFeature.OrchestratorInputs svo = StringAnalysisFeature.orchestratorInputs(true, false, false, sb, sv, lc, acc);
        Assert.assertTrue(svo.sb().isEmpty() && svo.lc().isEmpty());
        Assert.assertSame(sv, svo.sv());
        Assert.assertSame(acc, svo.acc());

        StringAnalysisFeature.OrchestratorInputs lco = StringAnalysisFeature.orchestratorInputs(false, true, false, sb, sv, lc, acc);
        Assert.assertTrue(lco.sb().isEmpty() && lco.sv().isEmpty() && lco.acc().isEmpty());
        Assert.assertSame(lc, lco.lc());
    }

    /** The StringJoiner extraction (an accumulator LAZY_CONCAT INTERLEAVED) counts as LS: LC-only keeps it. */
    @Test
    public void lazyConcatOnlyKeepsTheJoinerExtraction() {
        List<InstrumentationDecision> none = new ArrayList<>();
        InstrumentationDecision view = new InstrumentationDecision(new SugVertex(1), OptimizationType.STRING_VIEW, "ACCUMULATOR_VIEW", "java.lang.StringBuilder");
        InstrumentationDecision joiner = new InstrumentationDecision(new SugVertex(2), OptimizationType.LAZY_CONCAT, LazyConcatMint.INTERLEAVED, AccumulatorWhitelist.JOINER);
        List<InstrumentationDecision> acc = List.of(view, joiner);
        Assert.assertSame(acc, StringAnalysisFeature.orchestratorInputs(false, false, false, none, none, none, acc).acc());
        Assert.assertSame(acc, StringAnalysisFeature.orchestratorInputs(true, false, false, none, none, none, acc).acc());
        Assert.assertEquals(List.of(joiner), StringAnalysisFeature.orchestratorInputs(false, true, false, none, none, none, acc).acc());
        Assert.assertTrue(StringAnalysisFeature.orchestratorInputs(false, false, true, none, none, none, acc).acc().isEmpty());
    }

    // ---- the rep-allocation hook calls -------------------------------------------------------------------------

    /**
     * Every point where the class-initializer simulation turns an allocation into an image-heap object calls the
     * rep-allocation hook. Counted on the bytecode of the class file (read as a resource: loading the decoder class
     * would need the compiler's non-exported packages), so removing a call fails here; the method names are the stock
     * decoder's (an upstream rename fails loudly, and the list must then be re-audited).
     */
    @Test
    public void everySimulatedAllocationPointCallsTheRepHook() throws Exception {
        Map<String, Integer> expected = new TreeMap<>(Map.of(
                        "handleNewInstanceNode", 1,
                        "createNewArray", 1,
                        "createNewMultiArray", 1,
                        "handleObjectClone", 2,
                        "handleVirtualInstance", 1,
                        "handleVirtualArray", 1));
        Map<String, Integer> found = invokeCountsPerMethod("com/oracle/svm/hosted/classinitialization/SimulateClassInitializerGraphDecoder.class", "abortIfRepAllocation");
        Assert.assertEquals(expected, found);
        // 7 call sites (the innermost NewMultiArray dimension goes through createNewArray)
        Assert.assertEquals(7, found.values().stream().mapToInt(Integer::intValue).sum());
    }

    /** Per method of a class file: the number of invoke instructions whose callee is named {@code calleeName}. */
    private static Map<String, Integer> invokeCountsPerMethod(String resource, String calleeName) throws IOException {
        Map<String, Integer> out = new TreeMap<>();
        try (InputStream raw = UnitRangeAndPoolGuardsTest.class.getClassLoader().getResourceAsStream(resource)) {
            Assert.assertNotNull(resource, raw);
            DataInputStream in = new DataInputStream(raw);
            Assert.assertEquals(0xCAFEBABE, in.readInt());
            in.readUnsignedShort();
            in.readUnsignedShort();
            int n = in.readUnsignedShort();
            String[] utf8 = new String[n];
            int[] memberNameAndType = new int[n];
            int[] ntName = new int[n];
            for (int i = 1; i < n; i++) {
                int tag = in.readUnsignedByte();
                switch (tag) {
                    case 1 -> utf8[i] = in.readUTF();
                    case 7, 8, 16, 19, 20 -> in.readUnsignedShort();
                    case 3, 4 -> in.readInt();
                    case 5, 6 -> {
                        in.readLong();
                        i++;
                    }
                    case 9, 10, 11 -> {
                        in.readUnsignedShort();
                        memberNameAndType[i] = in.readUnsignedShort();
                    }
                    case 12 -> {
                        ntName[i] = in.readUnsignedShort();
                        in.readUnsignedShort();
                    }
                    case 15 -> {
                        in.readUnsignedByte();
                        in.readUnsignedShort();
                    }
                    case 17, 18 -> {
                        in.readUnsignedShort();
                        in.readUnsignedShort();
                    }
                    default -> throw new AssertionError("unknown constant pool tag " + tag);
                }
            }
            in.readUnsignedShort(); // access
            in.readUnsignedShort(); // this
            in.readUnsignedShort(); // super
            int interfaces = in.readUnsignedShort();
            for (int i = 0; i < interfaces; i++) {
                in.readUnsignedShort();
            }
            int fields = in.readUnsignedShort();
            for (int i = 0; i < fields; i++) {
                in.readUnsignedShort();
                in.readUnsignedShort();
                in.readUnsignedShort();
                skipAttributes(in);
            }
            int methods = in.readUnsignedShort();
            for (int i = 0; i < methods; i++) {
                in.readUnsignedShort();
                String name = utf8[in.readUnsignedShort()];
                in.readUnsignedShort();
                int attrs = in.readUnsignedShort();
                for (int a = 0; a < attrs; a++) {
                    String attr = utf8[in.readUnsignedShort()];
                    int len = in.readInt();
                    byte[] body = in.readNBytes(len);
                    if (!attr.equals("Code")) {
                        continue;
                    }
                    DataInputStream code = new DataInputStream(new java.io.ByteArrayInputStream(body));
                    code.readUnsignedShort();
                    code.readUnsignedShort();
                    byte[] bc = code.readNBytes(code.readInt());
                    BytecodeStream s = new BytecodeStream(bc);
                    int calls = 0;
                    while (s.currentBC() != Bytecodes.END) {
                        int op = s.currentBC();
                        if (op == Bytecodes.INVOKEVIRTUAL || op == Bytecodes.INVOKESPECIAL || op == Bytecodes.INVOKESTATIC || op == Bytecodes.INVOKEINTERFACE) {
                            if (calleeName.equals(utf8[ntName[memberNameAndType[s.readCPI()]]])) {
                                calls++;
                            }
                        }
                        s.next();
                    }
                    if (calls > 0) {
                        out.merge(name, calls, Integer::sum);
                    }
                }
            }
        }
        return out;
    }

    private static void skipAttributes(DataInputStream in) throws IOException {
        int attrs = in.readUnsignedShort();
        for (int a = 0; a < attrs; a++) {
            in.readUnsignedShort();
            in.readNBytes(in.readInt());
        }
    }

    // ---- the SB-pool route premise ------------------------------------------------------------------------------

    /**
     * A pooled SingleByteString cannot reach the image heap from a simulated class initializer because {@code POOL} is
     * not {@code @Stable}: its element load stays residual and the simulation aborts. If this fails, re-audit that
     * argument (the image-heap check for rep objects still fails the build closed).
     */
    @Test
    public void singleBytePoolIsNotStable() throws Exception {
        Field pool = SingleByteString.class.getDeclaredField("POOL");
        for (Annotation a : pool.getDeclaredAnnotations()) {
            Assert.assertFalse(a.annotationType().getName(), a.annotationType().getSimpleName().equals("Stable"));
        }
    }
}
