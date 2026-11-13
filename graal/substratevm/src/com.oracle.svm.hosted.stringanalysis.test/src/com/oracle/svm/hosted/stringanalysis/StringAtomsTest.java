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

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.calc.IsNullNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.LoadIndexedNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.java.StoreIndexedNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * STRING atom pins: the use classification rows (field usage, CLASS_CHECK usage, the refused store/array roles, the
 * invoke rows, the shared rows), the hand-list continuation, the terminal predicate and the {@code String.concat} test,
 * the indy concat shape test (operands by position, the constant appendix last), the knob defaults, and the
 * unrecognised-concat refusal name.
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
                "jdk.graal.compiler/jdk.graal.compiler.replacements.nodes"})
public class StringAtomsTest {

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    /** A holder with an Object field (the store/load rows on a non-String object). */
    static final class Holder {
        Object o;

        static String id(String s) {
            return s;
        }

        void keep(Object x) {
            o = x;
        }
    }

    private static StructuredGraph graph() {
        OptionValues options = new OptionValues(EconomicMap.create());
        DebugContext debug = new DebugContext.Builder(options).build();
        StructuredGraph graph = new StructuredGraph.Builder(options, debug).name("StringAtomsTest").build();
        graph.setStart(graph.add(new StartNode()));
        return graph;
    }

    private ParameterNode param(StructuredGraph graph, int index, Class<?> type) {
        ResolvedJavaType t = metaAccess.lookupJavaType(type);
        return graph.addWithoutUnique(new ParameterNode(index, StampPair.createSingle(StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(t)))));
    }

    private ResolvedJavaField field(Class<?> c, String name) {
        for (ResolvedJavaField f : metaAccess.lookupJavaType(c).getInstanceFields(false)) {
            if (f.getName().equals(name)) {
                return f;
            }
        }
        throw new AssertionError("no " + c.getName() + "." + name);
    }

    private ResolvedJavaMethod method(Class<?> c, String name, Class<?>... params) throws NoSuchMethodException {
        return metaAccess.lookupJavaMethod(c.getDeclaredMethod(name, params));
    }

    /** A LoadField on the walked string is a field usage (STOP); on another object it is a shared row. */
    @Test
    public void loadFieldIsAFieldUsage() {
        StructuredGraph g = graph();
        ParameterNode s = param(g, 0, String.class);
        ParameterNode h = param(g, 1, Holder.class);
        LoadFieldNode value = g.addWithoutUnique(LoadFieldNode.create(null, s, field(String.class, "value")));
        LoadFieldNode other = g.addWithoutUnique(LoadFieldNode.create(null, h, field(Holder.class, "o")));
        Assert.assertEquals(StringAtoms.Row.FIELD_USAGE, StringAtoms.rowOf(value, s, false));
        Assert.assertEquals("the loaded value of another object is not this string", StringAtoms.Row.SHARED, StringAtoms.rowOf(other, s, false));
    }

    /** The string as the OBJECT of a store / the ARRAY of a store or load is refused; as the stored VALUE it escapes. */
    @Test
    public void storeRolesAndArrayRoles() {
        StructuredGraph g = graph();
        ParameterNode s = param(g, 0, String.class);
        ParameterNode h = param(g, 1, Holder.class);
        ParameterNode arr = param(g, 2, Object[].class);
        ConstantNode zero = ConstantNode.forInt(0, g);
        StoreFieldNode storeValue = g.addWithoutUnique(new StoreFieldNode(h, field(Holder.class, "o"), s));
        Assert.assertEquals("the stored value: the shared ESCAPE row", StringAtoms.Row.SHARED, StringAtoms.rowOf(storeValue, s, false));
        StoreFieldNode storeInto = g.addWithoutUnique(new StoreFieldNode(s, field(String.class, "hash"), zero));
        Assert.assertEquals("the string as the object of a store", StringAtoms.Row.UNCLASSIFIED, StringAtoms.rowOf(storeInto, s, false));
        StoreIndexedNode storeElem = g.addWithoutUnique(new StoreIndexedNode(arr, zero, null, null, JavaKind.Object, s));
        Assert.assertEquals("the stored element: the shared ESCAPE row", StringAtoms.Row.SHARED, StringAtoms.rowOf(storeElem, s, false));
        Assert.assertEquals("an array store's array role (a String is no array)", StringAtoms.Row.UNCLASSIFIED,
                        StringAtoms.rowOf(g.addWithoutUnique(new StoreIndexedNode(s, zero, null, null, JavaKind.Object, arr)), s, false));
        LoadIndexedNode load = g.addWithoutUnique(new LoadIndexedNode(null, s, zero, null, JavaKind.Object));
        Assert.assertEquals(StringAtoms.Row.UNCLASSIFIED, StringAtoms.rowOf(load, s, false));
    }

    /** GetClass is a CLASS_CHECK usage; an exact InstanceOf only when it is a strict class check; IsNull is shared. */
    @Test
    public void classCheckRows() {
        StructuredGraph g = graph();
        ParameterNode s = param(g, 0, String.class);
        GetClassNode gc = g.addWithoutUnique(new GetClassNode(StampFactory.object(TypeReference.createWithoutAssumptions(metaAccess.lookupJavaType(Class.class))), s));
        Assert.assertEquals(StringAtoms.Row.CLASS_CHECK, StringAtoms.rowOf(gc, s, false));
        ParameterNode o = param(g, 1, Object.class); // an Object-typed carrier (a String-typed one folds the tests away)
        InstanceOfNode exact = (InstanceOfNode) g.addOrUnique(InstanceOfNode.create(TypeReference.createWithoutAssumptions(metaAccess.lookupJavaType(Integer.class)), o)); // exact: a leaf
        Assert.assertEquals("an exact test that is a strict class check", StringAtoms.Row.CLASS_CHECK, StringAtoms.rowOf(exact, o, true));
        Assert.assertEquals("an allowed source-shape fold: the shared observation", StringAtoms.Row.SHARED, StringAtoms.rowOf(exact, o, false));
        ResolvedJavaType cs = metaAccess.lookupJavaType(Number.class); // a non-leaf class (an interface target folds on host stamps)
        InstanceOfNode plain = (InstanceOfNode) g.addOrUnique(InstanceOfNode.create(TypeReference.createWithoutAssumptions(cs), o));
        Assert.assertEquals("a non-exact instanceof: an observation", StringAtoms.Row.SHARED, StringAtoms.rowOf(plain, o, true));
        IsNullNode isNull = g.addWithoutUnique(new IsNullNode(s));
        Assert.assertEquals(StringAtoms.Row.SHARED, StringAtoms.rowOf(isNull, s, false));
        Assert.assertTrue(StringAtoms.CLASS_CHECK_NODES.containsAll(java.util.Set.of("GetClassNode", "LoadHubNode", "LoadHubOrNullNode")));
    }

    /** The hand list — the walk continues at the result exactly for the returns-this entries (and the builders). */
    @Test
    public void handListContinuation() {
        String s = "java.lang.String";
        Assert.assertTrue(StringAtoms.continuesAtResult(s, "toString", "", s));
        Assert.assertTrue(StringAtoms.continuesAtResult(s, "substring", "I,I", s));
        Assert.assertTrue(StringAtoms.continuesAtResult(s, "trim", "", s));
        Assert.assertTrue(StringAtoms.continuesAtResult(s, "concat", "Ljava/lang/String;", s));
        Assert.assertTrue("a leak-marked entry that also returns this", StringAtoms.continuesAtResult(s, "toLowerCase", "", s));
        Assert.assertTrue(StringAtoms.continuesAtResult(s, "intern", "", s));
        Assert.assertFalse("inside the returned container: no continuation", StringAtoms.continuesAtResult(s, "split", "Ljava/lang/String;", "[Ljava.lang.String;"));
        Assert.assertFalse("leak-rule domain only", StringAtoms.continuesAtResult(s, "equals", "Ljava/lang/Object;", "boolean"));
        Assert.assertFalse("transform: returnsThis=false (design §15.3 m-5, kept)", StringAtoms.continuesAtResult(s, "transform", "Ljava/util/function/Function;", "java.lang.Object"));
        Assert.assertFalse("not on the list", StringAtoms.continuesAtResult(s, "length", "", "int"));
        Assert.assertFalse("a derived value: not followed", StringAtoms.continuesAtResult(s, "toCharArray", "", "[C"));
        Assert.assertTrue("a builder method returning the builder", StringAtoms.continuesAtResult("java.lang.AbstractStringBuilder", "append", "Ljava/lang/String;",
                        "java.lang.AbstractStringBuilder"));
        Assert.assertFalse("a builder method returning a value", StringAtoms.continuesAtResult("java.lang.StringBuilder", "length", "", "int"));
        int returnsThis = 0;
        for (StringTerminalHandList.Entry e : StringTerminalHandList.STRING_ENTRIES) {
            Assert.assertSame(e, StringAtoms.handEntry(e.declaringClass(), e.name(), e.signature()));
            returnsThis += e.returnsThis() ? 1 : 0;
        }
        Assert.assertEquals("the returns-this entries of the list", 20, returnsThis);
    }

    /** The stringy declaring types; the direct concat shape is exactly String.concat(String). */
    @Test
    public void terminalTypesAndF4() throws NoSuchMethodException {
        Assert.assertTrue(ForwardFixpoint.isStringyDeclaringType("java.lang.String"));
        Assert.assertTrue(ForwardFixpoint.isStringyDeclaringType("java.lang.AbstractStringBuilder"));
        Assert.assertTrue(ForwardFixpoint.isStringyDeclaringType("com.oracle.svm.core.stringrep.StringView"));
        Assert.assertFalse(ForwardFixpoint.isStringyDeclaringType("java.lang.Object"));
        Assert.assertFalse(ForwardFixpoint.isStringyDeclaringType("java.lang.CharSequence"));
        Assert.assertTrue(StringAtoms.isStringConcat(method(String.class, "concat", String.class)));
        Assert.assertFalse(StringAtoms.isStringConcat(method(String.class, "replace", char.class, char.class)));
        Assert.assertFalse(StringAtoms.isStringConcat(method(String.class, "join", CharSequence.class, CharSequence[].class)));
    }

    /** The indy concat shape: linkToTargetMethod with the dynamic operands by position and the constant appendix last. */
    @Test
    public void f1ShapeTest() {
        Assert.assertEquals(StringAtoms.ConcatKind.F1, StringAtoms.f1Shape("linkToTargetMethod", 3, true, 2));
        Assert.assertEquals("one dynamic operand + the appendix", StringAtoms.ConcatKind.F1, StringAtoms.f1Shape("linkToTargetMethod", 2, true, 1));
        Assert.assertEquals("the appendix must be a constant", StringAtoms.ConcatKind.UNRECOGNISED, StringAtoms.f1Shape("linkToTargetMethod", 3, false, 2));
        Assert.assertEquals("operands by position: a count mismatch is not F1", StringAtoms.ConcatKind.UNRECOGNISED, StringAtoms.f1Shape("linkToTargetMethod", 2, true, 2));
        Assert.assertEquals("the child rewrite (concatTrace(String[])) is not F1", StringAtoms.ConcatKind.UNRECOGNISED, StringAtoms.f1Shape("concatTrace", 1, false, 2));
        Assert.assertEquals("a StringConcatHelper call at the site (F2) is not recognised", StringAtoms.ConcatKind.UNRECOGNISED, StringAtoms.f1Shape("simpleConcat", 2, false, 2));
    }

    /** The unrecognised-concat refusal: a new, non-budget name appended last (no earlier name moves). */
    @Test
    public void unrecognisedConcatRefusal() {
        RTrackRefusal[] all = RTrackRefusal.values();
        // the later names follow it in this order, under the same rule (no earlier name moves): JDK_MODEL_UNMODELLED,
        // EQUALS_ARG_NO_SITE, LITERAL_IDENTITY (the SB literal seed), CLASS_ESCAPE (the identity query
        // atoms' class escape), HOLDER_END_UNEXPLAINED, COMPARETO_ARG_NO_SITE, HIDDEN_SINK, MIRROR_ARG_NO_SITE
        Assert.assertEquals(RTrackRefusal.MIRROR_ARG_NO_SITE, all[all.length - 1]);
        Assert.assertEquals(RTrackRefusal.HIDDEN_SINK.ordinal() + 1, RTrackRefusal.MIRROR_ARG_NO_SITE.ordinal());
        Assert.assertEquals(RTrackRefusal.COMPARETO_ARG_NO_SITE.ordinal() + 1, RTrackRefusal.HIDDEN_SINK.ordinal());
        Assert.assertEquals(RTrackRefusal.HOLDER_END_UNEXPLAINED.ordinal() + 1, RTrackRefusal.COMPARETO_ARG_NO_SITE.ordinal());
        Assert.assertEquals(RTrackRefusal.CLASS_ESCAPE.ordinal() + 1, RTrackRefusal.HOLDER_END_UNEXPLAINED.ordinal());
        Assert.assertEquals(RTrackRefusal.LITERAL_IDENTITY.ordinal() + 1, RTrackRefusal.CLASS_ESCAPE.ordinal());
        Assert.assertEquals(RTrackRefusal.EQUALS_ARG_NO_SITE.ordinal() + 1, RTrackRefusal.LITERAL_IDENTITY.ordinal());
        Assert.assertEquals(RTrackRefusal.JDK_MODEL_UNMODELLED.ordinal() + 1, RTrackRefusal.EQUALS_ARG_NO_SITE.ordinal());
        Assert.assertEquals(RTrackRefusal.UNRECOGNISED_CONCAT.ordinal() + 1, RTrackRefusal.JDK_MODEL_UNMODELLED.ordinal());
        Assert.assertFalse(RTrackRefusal.JDK_MODEL_UNMODELLED.budgetClass);
        Assert.assertEquals(RTrackRefusal.NO_CALLER_EXIT.ordinal() + 1, RTrackRefusal.UNRECOGNISED_CONCAT.ordinal());
        Assert.assertFalse(RTrackRefusal.UNRECOGNISED_CONCAT.budgetClass);
    }
    // ------------------------------------------------------------------
    // The engine's classification rows (the pure decisions invokeUsage / concatCrossing / desugaredToString
    // apply), the unreadable concat sites and the strict field usage.
    // ------------------------------------------------------------------

    private static boolean terminal(ResolvedJavaMethod m) {
        return StringAtoms.isTerminalTarget(m.isStatic(), m.isConstructor(), m.getDeclaringClass().toJavaName(true));
    }

    /** The engine's per-slot row for a call whose argument {@code slot} holds the walked string (as invokeUsage computes it). */
    private static StringAtoms.SlotRow slotRow(ResolvedJavaMethod target, int slot) {
        boolean receiverPosition = !target.isStatic() && slot == 0;
        return StringAtoms.invokeSlotRow(slot, receiverPosition && terminal(target), StringAtoms.isStringConcat(target));
    }

    /** Slot 0 of a String-declared instance call is a terminal (not entered); hand-list results continue. */
    @Test
    public void receiverTerminalRow() throws NoSuchMethodException {
        ResolvedJavaMethod replace = method(String.class, "replace", char.class, char.class);
        ResolvedJavaMethod length = method(String.class, "length");
        Assert.assertTrue(terminal(replace));
        Assert.assertEquals(StringAtoms.SlotRow.TERMINAL, slotRow(replace, 0));
        Assert.assertEquals(StringAtoms.SlotRow.TERMINAL, slotRow(length, 0));
        Assert.assertTrue("replace(C,C) may return this: the walk continues at the result", StringAtoms.continuesAtResult("java.lang.String", "replace", "C,C", "java.lang.String"));
        Assert.assertFalse(StringAtoms.continuesAtResult("java.lang.String", "length", "", "int"));
        Assert.assertTrue("a builder receiver is a terminal too", terminal(method(StringBuilder.class, "append", String.class)));
        Assert.assertFalse("a static String method is no terminal (entered)", terminal(method(String.class, "valueOf", Object.class)));
        Assert.assertFalse("a constructor is no terminal", terminal(metaAccess.lookupJavaMethod(String.class.getDeclaredConstructor(String.class))));
        Assert.assertFalse("an Object-declared target is entered (the String cone resolves it first)", terminal(method(Object.class, "toString")));
        Assert.assertFalse("an interface-declared target is entered", terminal(method(CharSequence.class, "length")));
    }

    /** The string as an argument enters the callee's body at that parameter; the self-argument rule. */
    @Test
    public void argumentEntersTheBody() throws NoSuchMethodException {
        Assert.assertEquals("a static call's argument", StringAtoms.SlotRow.ENTER, slotRow(metaAccess.lookupJavaMethod(Holder.class.getDeclaredMethod("id", String.class)), 0));
        Assert.assertEquals("an argument of a String method", StringAtoms.SlotRow.ENTER, slotRow(method(String.class, "equals", Object.class), 1));
        Assert.assertEquals("an argument of a user instance method", StringAtoms.SlotRow.ENTER, slotRow(metaAccess.lookupJavaMethod(Holder.class.getDeclaredMethod("keep", Object.class)), 1));
        // s.equals(s): slot 0 is the terminal, slot 1 is entered (the self-argument rule)
        ResolvedJavaMethod eq = method(String.class, "equals", Object.class);
        Assert.assertEquals(StringAtoms.SlotRow.TERMINAL, slotRow(eq, 0));
        Assert.assertEquals(StringAtoms.SlotRow.ENTER, slotRow(eq, 1));
        Assert.assertEquals("slot 0 of a non-stringy receiver call is entered", StringAtoms.SlotRow.ENTER, slotRow(metaAccess.lookupJavaMethod(Holder.class.getDeclaredMethod("keep", Object.class)),
                        0));
    }

    /** The concat operand rows (String.concat and indy) and the desugared toString() of a non-String operand. */
    @Test
    public void concatOperandRows() throws NoSuchMethodException {
        ResolvedJavaMethod concat = method(String.class, "concat", String.class);
        Assert.assertEquals("F4 receiver: the terminal (and the adapter's operand usage)", StringAtoms.SlotRow.TERMINAL, slotRow(concat, 0));
        Assert.assertEquals("F4 argument: the concat operand, never entered", StringAtoms.SlotRow.CONCAT_OPERAND, slotRow(concat, 1));
        StringAtoms.Concat f1 = new StringAtoms.Concat(StringAtoms.ConcatKind.F1, new boolean[]{true, false}, null);
        Assert.assertEquals(2, f1.operandCount());
        Assert.assertEquals("a String-declared operand of a STRING atom: the operand usage", StringAtoms.ConcatSlot.OPERAND_USAGE, StringAtoms.concatSlot(f1, 0, true));
        Assert.assertEquals("a String-declared operand of a container atom: nothing", StringAtoms.ConcatSlot.NOTHING, StringAtoms.concatSlot(f1, 0, false));
        Assert.assertEquals("a non-String operand: the desugared toString()", StringAtoms.ConcatSlot.DESUGARED_TO_STRING, StringAtoms.concatSlot(f1, 1, true));
        Assert.assertEquals("both kinds cross the desugared call", StringAtoms.ConcatSlot.DESUGARED_TO_STRING, StringAtoms.concatSlot(f1, 1, false));
        Assert.assertEquals("the appendix: the ordinary crossing", StringAtoms.ConcatSlot.APPENDIX, StringAtoms.concatSlot(f1, 2, true));
        Assert.assertNull("F1 is crossed, not refused", StringAtoms.concatRefusal(f1));
        Assert.assertNull("NONE is the ordinary crossing", StringAtoms.concatRefusal(StringAtoms.Concat.NONE));
        // the desugared String.toString() is the listed terminal whose result is the synthetic ConcatOperand
        Assert.assertTrue(terminal(method(String.class, "toString")));
        Assert.assertTrue(StringAtoms.continuesAtResult("java.lang.String", "toString", "", "java.lang.String"));
    }

    /**
     * {@code Long.parseLong(cand, radix)} enters the parser; the parser reads the candidate with
     * terminals only; the error path copies it through the builder ({@code append(String)} is entered at slot 1, where the
     * candidate meets terminals) and the copy (the builder's {@code toString()}, the exception) is dropped.
     */
    @Test
    public void parseLongCopyAndDrop() throws Exception {
        Assert.assertEquals("parseLong: a static call, entered", StringAtoms.SlotRow.ENTER, slotRow(method(Long.class, "parseLong", String.class, int.class), 0));
        Assert.assertEquals(StringAtoms.SlotRow.ENTER, slotRow(method(Integer.class, "parseInt", String.class, int.class), 0));
        Assert.assertEquals("the error path: forInputString(s, radix) entered", StringAtoms.SlotRow.ENTER,
                        slotRow(method(NumberFormatException.class, "forInputString", String.class, int.class), 0));
        Class<?> asb = Class.forName("java.lang.AbstractStringBuilder");
        ResolvedJavaMethod append = metaAccess.lookupJavaMethod(asb.getDeclaredMethod("append", String.class));
        Assert.assertEquals("the candidate as the builder's argument: entered", StringAtoms.SlotRow.ENTER, slotRow(append, 1));
        // inside: terminals whose results are not the candidate
        for (String[] t : new String[][]{{"length", "", "int"}, {"charAt", "I", "char"}, {"coder", "", "byte"}, {"getBytes", "[B,I,B", "void"}}) {
            Assert.assertFalse(t[0] + ": a terminal whose result is not followed", StringAtoms.continuesAtResult("java.lang.String", t[0], t[1], t[2]));
        }
        Assert.assertTrue(terminal(metaAccess.lookupJavaMethod(String.class.getDeclaredMethod("getBytes", byte[].class, int.class, byte.class))));
        Assert.assertFalse("the builder's toString() is a copy: dropped", StringAtoms.continuesAtResult("java.lang.StringBuilder", "toString", "", "java.lang.String"));
        // the per-rep verdict on those usages: StringView admits them all; RopeString too
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("length", "java.lang.String", ""));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("charAt", "java.lang.String", "I"));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("getBytes", "java.lang.String", "[B,I,B"));
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("getBytes", "java.lang.String", "[B,I,B", "ROPE"));
    }

    /** The refusal paths of the string rows: the unrecognised concat (incl. unreadable sites) and the desugared targets. */
    @Test
    public void refusalPaths() {
        Assert.assertEquals(RTrackRefusal.UNRECOGNISED_CONCAT, StringAtoms.concatRefusal(StringAtoms.Concat.UNRECOGNISED));
        // an indy (or linkToTargetMethod) site whose bytecode / bootstrap cannot be read is refused by name
        Assert.assertEquals(StringAtoms.ConcatKind.UNRECOGNISED, StringAtoms.unreadableSite("linkToTargetMethod", false));
        Assert.assertEquals(StringAtoms.ConcatKind.UNRECOGNISED, StringAtoms.unreadableSite("anything", true));
        Assert.assertEquals(StringAtoms.ConcatKind.UNRECOGNISED, StringAtoms.unreadableSite(null, true));
        Assert.assertEquals("an unreadable call that is no indy: the ordinary crossing", StringAtoms.ConcatKind.NONE, StringAtoms.unreadableSite("length", false));
        Assert.assertEquals(StringAtoms.ConcatKind.NONE, StringAtoms.unreadableSite(null, false));
        // a readable non-indy opcode at an indy-adapter invoke is refused by name; other calls are ordinary
        Assert.assertEquals(StringAtoms.ConcatKind.UNRECOGNISED, StringAtoms.nonIndyOpcodeSite("linkToTargetMethod"));
        Assert.assertEquals(StringAtoms.ConcatKind.NONE, StringAtoms.nonIndyOpcodeSite("length"));
        Assert.assertEquals(StringAtoms.ConcatKind.NONE, StringAtoms.nonIndyOpcodeSite(null));
        // the desugared toString()'s target list
        Assert.assertEquals(RTrackRefusal.UNRESOLVED_VALUE, StringAtoms.desugaredTargetRefusal(-1, 8));
        Assert.assertEquals(RTrackRefusal.NO_TARGET, StringAtoms.desugaredTargetRefusal(0, 8));
        Assert.assertEquals(RTrackRefusal.CHA_FAN_CAP, StringAtoms.desugaredTargetRefusal(9, 8));
        Assert.assertNull(StringAtoms.desugaredTargetRefusal(8, 8));
        Assert.assertNull(StringAtoms.desugaredTargetRefusal(1, 8));
        for (RTrackRefusal r : new RTrackRefusal[]{RTrackRefusal.UNRECOGNISED_CONCAT, RTrackRefusal.UNRESOLVED_VALUE, RTrackRefusal.NO_TARGET, RTrackRefusal.CHA_FAN_CAP,
                        RTrackRefusal.UNCLASSIFIED_ACCESS}) {
            Assert.assertFalse(r + " is not budget-class", r.budgetClass);
        }
    }

    /** A strict field usage {@code field:<name>} is never whitelisted, by any representation. */
    @Test
    public void strictFieldUsageNeverWhitelisted() {
        Assert.assertEquals("field:offset", StringAtoms.strictFieldUsageName("offset"));
        String[] decls = {"java.lang.String", "java.lang.StringBuilder", "java.lang.AbstractStringBuilder", "com.oracle.svm.core.stringrep.StringView", "java.lang.Object"};
        String[] fields = {"value", "coder", "hash", "hashIsZero", "length", "offset", "x", ""};
        String[] sigs = {"", null, "I", "[B,I,B"};
        String[] variants = {null, "ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED"};
        for (String f : fields) {
            String name = StringAtoms.strictFieldUsageName(f);
            Assert.assertFalse(AccumulatorWhitelist.isWhitelisted(name));
            Assert.assertFalse(AccumulatorWhitelist.isExtraction(name));
            for (String d : decls) {
                for (String sig : sigs) {
                    Assert.assertFalse(name, StringViewWhitelist.isWhitelisted(name, d, sig));
                    Assert.assertFalse(name, StringViewWhitelist.isWhitelistedUsage(name, d, sig));
                    Assert.assertFalse(name, LazyConcatWhitelist.isWhitelisted(name, d, sig));
                    for (String v : variants) {
                        Assert.assertFalse(name + " " + v, LazyConcatWhitelist.isWhitelisted(name, d, sig, v));
                    }
                }
            }
        }
        // no table entry starts with the prefix (a future prefix / wildcard entry would break the pin above)
        for (String k : StringViewWhitelist.acceptedSignatures()) {
            Assert.assertFalse(k, k.startsWith(StringAtoms.STRICT_FIELD_PREFIX));
        }
        for (String k : LazyConcatWhitelist.SIGNATURES.keySet()) {
            Assert.assertFalse(k, k.startsWith(StringAtoms.STRICT_FIELD_PREFIX));
        }
        for (String k : AccumulatorWhitelist.W_ACCUMULATOR) {
            Assert.assertFalse(k, k.startsWith(StringAtoms.STRICT_FIELD_PREFIX));
        }
    }
}
