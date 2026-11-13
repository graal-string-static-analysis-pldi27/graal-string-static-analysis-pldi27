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

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import org.junit.Assert;
import org.junit.Test;

/**
 * JDK-model mechanism: the shared receiver-atom selector, the sealed effect records, the parser rules (FRESH temps,
 * {@code R} and the sink {@code S} as callback operands, {@code ir-closed}, no abstracted field in a table,
 * {@code requires}) and the re-dispatch depth knob.
 */
public class JdkModelMechanismTest {

    private static JdkModels.Family fam(String id, Set<String> closed, Map<String, String> abstracted, String... lines) {
        return new JdkModels.Family(id + "-" + System.nanoTime(), false, closed, abstracted, lines);
    }

    private static JdkModels.Op parse(String line) {
        return JdkModels.parse(fam("p", Set.of(), Map.of()), line);
    }

    private static void rejected(String why, String line) {
        try {
            parse(line);
        } catch (IllegalArgumentException e) {
            return;
        }
        Assert.fail("the parser accepts " + why + ": " + line);
    }

    private static void invalid(String why, JdkModels.Family... fs) {
        try {
            JdkModels.validate(List.of(fs));
        } catch (IllegalStateException e) {
            return;
        }
        Assert.fail("validate accepts " + why);
    }

    /**
     * The shared selector: a receiver atom of unknown type, or of a type the dispatch rule doubts, selects the whole
     * fan; only a known type narrows. The mutation "return nothing when there is no exact type" (the backward selection
     * returning instead of falling back) fails the first assertion.
     */
    @Test
    public void receiverSelectionFallsBackToTheWholeFan() {
        List<String> fan = List.of("A.m", "B.m", "C.m");
        Function<String, List<String>> dispatch = t -> switch (t) {
            case "B" -> List.of("B.m");
            case "BC" -> List.of("B.m", "C.m");
            default -> null; // a type outside the fan, or a doubt
        };
        Assert.assertEquals("an atom of unknown type (a String, an inexact FRESH object): the whole fan", fan, JdkModelEngine.receiverSelection(null, dispatch, fan));
        Assert.assertEquals("a doubted type: the whole fan", fan, JdkModelEngine.receiverSelection("X", dispatch, fan));
        Assert.assertEquals("a known type narrows", List.of("B.m"), JdkModelEngine.receiverSelection("B", dispatch, fan));
        Assert.assertEquals(List.of("B.m", "C.m"), JdkModelEngine.receiverSelection("BC", dispatch, fan));
    }

    /** The effect records: every kind parses to its record, prints as its table syntax, and lists its operands. */
    @Test
    public void effectRecordsRoundTrip() {
        JdkModels.Op op = parse(
                        "java.util.X#m(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object; : call 1 java.util.function.Supplier#get()Ljava/lang/Object; -> $1 @ java.util.X#m(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;@3" +
                                        " ; fresh [Ljava.lang.Object; -> $2 ; store $2 [] $1 ; fresh java.util.X ; store R <elem> $2.[] ; call 2 java.util.Spliterator#forEachRemaining(Ljava/util/function/Consumer;)V S" +
                                        " @ java.util.X#m(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;@9 ; store R <elem> S ; observe 0");
        List<JdkModels.Effect> es = op.effects();
        Assert.assertTrue(es.get(0) instanceof JdkModels.Callback c && c.bind() == JdkModels.BIND_TEMP);
        Assert.assertTrue(es.get(1) instanceof JdkModels.Fresh f && f.bind() == JdkModels.BIND_TEMP + 1 && f.exact());
        Assert.assertTrue(es.get(3) instanceof JdkModels.Fresh f && f.bind() == JdkModels.BIND_RESULT);
        Assert.assertTrue(op.tempBinder(2) instanceof JdkModels.Fresh);
        Assert.assertTrue(op.tempBinder(1) instanceof JdkModels.Callback);
        Assert.assertEquals("fresh [Ljava.lang.Object; -> $2", es.get(1).toString());
        Assert.assertEquals("store R <elem> S", op.sinkStore().toString());
        Assert.assertEquals(List.of(JdkModels.Ref.parse("2"), JdkModels.Ref.parse("S")), es.get(5).operands());
        Assert.assertTrue(op.hasResultEffect());
        Assert.assertEquals("ir-closed 0", parse("java.util.X#n()V : ir-closed 0").effects().get(0).toString());
    }

    /** The per-entry parser rules of the effect operands. */
    @Test
    public void parserRules() {
        String m = "java.util.X#m(Ljava/lang/Object;)Ljava/lang/Object;";
        String site = " @ java.util.X#m(Ljava/lang/Object;)Ljava/lang/Object;@1";
        rejected("R without a FRESH result", m + " : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V R" + site + " ; alias 1");
        rejected("alias R", m + " : fresh java.util.X ; alias R");
        rejected("a temp without a binder", m + " : alias $1");
        rejected("a temp with two binders", m + " : fresh java.util.X -> $1 ; fresh java.util.Y -> $1 ; alias $1");
        rejected("S as a callback receiver", m + " : call S java.util.function.Consumer#accept(Ljava/lang/Object;)V 1" + site + " ; store 1 <elem> S ; alias 1");
        rejected("S passed but stored nowhere", m + " : call 1 java.util.Spliterator#forEachRemaining(Ljava/util/function/Consumer;)V S" + site + " ; alias 1");
        rejected("S stored but never passed", m + " : store 1 <elem> S ; alias 1");
        rejected("S stored twice", m + " : call 1 java.util.Spliterator#forEachRemaining(Ljava/util/function/Consumer;)V S" + site + " ; fresh java.util.X ; store R <elem> S ; store 1 <elem> S");
        rejected("S as a store owner", m + " : call 1 java.util.Spliterator#forEachRemaining(Ljava/util/function/Consumer;)V S" + site + " ; store S <elem> 1 ; alias 1");
        rejected("S with a member", m + " : call 1 java.util.Spliterator#forEachRemaining(Ljava/util/function/Consumer;)V S.<elem>" + site + " ; fresh java.util.X ; store R <elem> S");
        rejected("two FRESH results", m + " : fresh java.util.X ; fresh java.util.Y");
        rejected("a FRESH result beside result ir", m + " : fresh java.util.X ; result ir");
        rejected("a malformed fresh", m + " : fresh java.util.X $1");
        rejected("a malformed result", m + " : result walk");
        // accepted forms: R and a FRESH temp as callback operands
        parse(m + " : fresh java.util.X ; call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V R" + site);
        parse(m + " : fresh java.util.X -> $1 ; call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V $1" + site + " ; alias 1");
    }

    /** The cross-family rules ({@link JdkModels#validate}): the committed families pass; each control is caught. */
    @Test
    public void crossFamilyRules() {
        JdkModels.validate(JdkModels.FAMILIES);
        JdkModels.Family rep = fam("rep", Set.of("java.util.ArrayList"), Map.of("java.util.ArrayList.elementData", "<elem>[]"),
                        "java.util.ArrayList#size()I : observe 0");
        invalid("a store of an abstracted field", rep, fam("st", Set.of(), Map.of(), "java.util.Y#f(Ljava/lang/Object;)V : store 0 java.util.ArrayList.elementData 1"));
        invalid("a load of an abstracted field", rep, fam("ld", Set.of(), Map.of(), "java.util.Y#g(Ljava/lang/Object;)Ljava/lang/Object; : load 1 java.util.ArrayList.elementData []"));
        invalid("ir in a closed class", rep, fam("ir", Set.of(), Map.of(), "java.util.ArrayList#isEmpty()Z : ir 0"));
        invalid("result ir in a closed class", rep, fam("rir", Set.of(), Map.of(), "java.util.ArrayList#iterator()Ljava/util/Iterator; : ir-closed 0 ; result ir"));
        invalid("ir-closed in an open class", rep, fam("irc", Set.of(), Map.of(), "java.util.Y#h()V : ir-closed 0"));
        JdkModels.validate(List.of(rep, fam("ok", Set.of(), Map.of(), "java.util.ArrayList#isEmpty()Z : ir-closed 0",
                        "java.util.ArrayList#iterator()Ljava/util/Iterator; : ir-closed 0 ; result ir-closed")));
        // a record component field is a slot's too (no entry may name it)
        JdkModels.Family rec = fam("rec", Set.of(), Map.of(), "java.util.Z#sup()Ljava/lang/Object; : load 0 <supplier>");
        rec.recordSlots = Map.of("java.util.Z.sup", "<supplier>");
        invalid("a load of a record component field", rec, fam("rl", Set.of(), Map.of(), "java.util.Y#k(Ljava/lang/Object;)Ljava/lang/Object; : load 1 java.util.Z.sup"));
        invalid("a store of a record component field", rec, fam("rs", Set.of(), Map.of(), "java.util.Y#k(Ljava/lang/Object;)V : store 0 java.util.Z.sup 1"));
        JdkModels.Family req = new JdkModels.Family("req-" + System.nanoTime(), false, Set.of(), Map.of(), Set.of(), Set.of(), Set.of("nosuch"));
        invalid("requires an unknown family", req);
        JdkModels.Family self = new JdkModels.Family("self", false, Set.of(), Map.of(), Set.of(), Set.of(), Set.of("self"));
        invalid("requires itself", self);
    }

    /** The re-dispatch depth knob's default. */
    @Test
    public void depthKnob() {
        Assert.assertEquals(Integer.getInteger("svm.stringanalysis.fwd.jdkmodel.depth", 4).intValue(), JdkModelEngine.MAX_DEPTH);
    }
}
