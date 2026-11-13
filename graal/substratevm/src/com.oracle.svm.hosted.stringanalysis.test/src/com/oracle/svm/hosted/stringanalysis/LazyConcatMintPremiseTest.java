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

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

/**
 * Premise: {@link LazyConcatMint#mintedRep} is the one function both sides use, and it names what will exist.
 * <ol>
 * <li>Over an exhaustive enumeration of (variant, dynamic count, recipe shape), every non-null minted rep is a
 * registered {@link InlineCacheRegistry} name, and the factory the parent resolves for it
 * ({@link LazyConcatMint#factoryMethod}), called with that many parts, returns an object of exactly the registry class
 * (the class the rep-type chain guards).</li>
 * <li>The parent's mint decision equals the reference rule below on every enumerated input (the gate is the total part
 * count for every site), and the child's total-parts name {@link LazyConcatMint#shapeVariant} always mints itself.</li>
 * <li>The child names the same rep: {@link HeuristicOrchestrator#repTypeOf} of a LAZY_CONCAT decision on a concat vertex
 * carrying (dynamic count, recipe) is {@code mintedRep} — the case {@code suffix + "_" + counter} (ROPE, dyn 2,
 * 3 parts) names ARRAY_LAZY, not ROPE; a {@code String.concat} vertex names ROPE.</li>
 * </ol>
 */
public class LazyConcatMintPremiseTest {

    private static final String[] VARIANTS = {"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED", "SV", null};

    /** Recipes for {@code dyn} dynamic operands: bare makeConcat (null) and every placement of literal runs/\2 tags. */
    private static List<String> recipes(int dyn) {
        List<String> out = new ArrayList<>();
        out.add(null);
        String[] fills = {"", "_", "ab", "\u0002", "x\u0002"};
        // slots: before, between each pair, after (dyn + 1 slots); enumerate a bounded product
        int slots = dyn + 1;
        int total = 1;
        for (int i = 0; i < slots; i++) {
            total *= fills.length;
        }
        for (int code = 0; code < total; code++) {
            StringBuilder sb = new StringBuilder();
            int c = code;
            for (int i = 0; i < slots; i++) {
                sb.append(fills[c % fills.length]);
                c /= fills.length;
                if (i < dyn) {
                    sb.append('\u0001');
                }
            }
            out.add(sb.toString());
        }
        // the interleaved shape with a uniform delimiter
        StringBuilder il = new StringBuilder("\u0001");
        for (int i = 1; i < dyn; i++) {
            il.append(", \u0001");
        }
        out.add(il.toString());
        return out;
    }

    /** The parent mint rule (reference copy; the total-parts gate for every site). */
    private static String parentMintRule(String variant, int dynamicCount, String recipe) {
        boolean isRope = "ROPE".equals(variant);
        boolean isThreeWay = "THREE_WAY".equals(variant);
        boolean isFixed4 = "FIXED4".equals(variant);
        boolean isArrayLazy = "ARRAY_LAZY".equals(variant);
        boolean isInterleaved = "INTERLEAVED".equals(variant);
        if (!isRope && !isThreeWay && !isFixed4 && !isArrayLazy && !isInterleaved) {
            return null;
        }
        if (dynamicCount < 1) {
            return null;
        }
        int totalParts;
        if (recipe != null) {
            int constants = 0;
            boolean inLiteral = false;
            for (int i = 0; i < recipe.length(); i++) {
                char c = recipe.charAt(i);
                if (c == '\u0001') {
                    inLiteral = false;
                } else if (c == '\u0002') {
                    constants++;
                    inLiteral = false;
                } else {
                    if (!inLiteral) {
                        constants++;
                        inLiteral = true;
                    }
                }
            }
            totalParts = dynamicCount + constants;
        } else {
            totalParts = dynamicCount;
        }
        int gateParts = totalParts; // the total-parts gate for every site
        if (gateParts < 2) {
            return null;
        }
        if ((isInterleaved || isArrayLazy) && gateParts < 5) {
            return null;
        }
        if (isInterleaved) {
            if (recipe == null) {
                return null;
            }
            return LazyConcatMint.interleavedDelimiter(recipe, dynamicCount) == null ? null : "INTERLEAVED";
        }
        if (isRope && totalParts == 2) {
            return "ROPE";
        }
        if (isThreeWay && totalParts == 3) {
            return "THREE_WAY";
        }
        if (isFixed4 && totalParts == 4) {
            return "FIXED4";
        }
        return "ARRAY_LAZY";
    }

    @Test
    public void everyMintedRepIsRegisteredAndItsFactoryBuildsExactlyThatClass() throws Exception {
        int checked = 0;
        for (String variant : VARIANTS) {
            for (int dyn = 0; dyn <= 7; dyn++) {
                for (String recipe : recipes(dyn)) {
                    String minted = LazyConcatMint.mintedRep(variant, dyn, recipe);
                    Assert.assertEquals("parent rule changed for " + variant + "/" + dyn + "/" + show(recipe), parentMintRule(variant, dyn, recipe), minted);
                    if (minted == null) {
                        continue;
                    }
                    Class<?> repClass = InlineCacheRegistry.getRepClass(minted);
                    Assert.assertNotNull("minted rep " + minted + " is not a registry name", repClass);
                    Object built = invokeFactory(minted, LazyConcatMint.totalParts(recipe, dyn), recipe, dyn);
                    Assert.assertSame("factory of " + minted + " (" + variant + "/" + dyn + "/" + show(recipe) + ")", repClass, built.getClass());
                    checked++;
                }
            }
        }
        Assert.assertTrue("enumeration too small: " + checked, checked > 1000);
    }

    /** The child's total-parts name mints exactly itself, and is null only below 2 total parts. */
    @Test
    public void theShapeVariantMintsItself() {
        int checked = 0;
        for (int dyn = 0; dyn <= 7; dyn++) {
            for (String recipe : recipes(dyn)) {
                String name = LazyConcatMint.shapeVariant(dyn, recipe);
                if (dyn < 1 || LazyConcatMint.totalParts(recipe, dyn) < 2) {
                    Assert.assertNull(dyn + "/" + show(recipe), name);
                    continue;
                }
                Assert.assertNotNull(dyn + "/" + show(recipe), name);
                Assert.assertEquals("name != minted for " + dyn + "/" + show(recipe), name, LazyConcatMint.mintedRep(name, dyn, recipe));
                int total = LazyConcatMint.totalParts(recipe, dyn);
                String expect = switch (total) {
                    case 2 -> "ROPE";
                    case 3 -> "THREE_WAY";
                    case 4 -> "FIXED4";
                    default -> name;
                };
                Assert.assertEquals(expect, name);
                checked++;
            }
        }
        Assert.assertTrue("enumeration too small: " + checked, checked > 1000);
        // examples: "string"+i+"string"+i -> FIXED4; "string"+z+b -> THREE_WAY; \1,\1,\1 -> INTERLEAVED
        Assert.assertEquals("FIXED4", LazyConcatMint.shapeVariant(2, "string\u0001string\u0001"));
        Assert.assertEquals("THREE_WAY", LazyConcatMint.shapeVariant(2, "string\u0001\u0001"));
        Assert.assertEquals("INTERLEAVED", LazyConcatMint.shapeVariant(3, "\u0001,\u0001,\u0001"));
        Assert.assertEquals("ARRAY_LAZY", LazyConcatMint.shapeVariant(5, "\u0001\u0001\u0001\u0001\u0001"));
        Assert.assertEquals("ARRAY_LAZY", LazyConcatMint.shapeVariant(2, "a\u0001b\u0001c"));
        Assert.assertNull(LazyConcatMint.shapeVariant(1, "\u0001"));
    }

    private static Object invokeFactory(String minted, int totalParts, String recipe, int dyn) throws Exception {
        Method f = LazyConcatMint.factoryMethod(minted);
        Assert.assertNotNull(f);
        String[] parts = new String[totalParts];
        for (int i = 0; i < totalParts; i++) {
            parts[i] = "p" + i;
        }
        return switch (minted) {
            case "ROPE" -> f.invoke(null, parts[0], parts[1]);
            case "THREE_WAY" -> f.invoke(null, parts[0], parts[1], parts[2]);
            case "FIXED4" -> f.invoke(null, parts[0], parts[1], parts[2], parts[3]);
            case "ARRAY_LAZY" -> f.invoke(null, (Object) parts);
            case "INTERLEAVED" -> f.invoke(null, java.util.Arrays.copyOf(parts, dyn), LazyConcatMint.interleavedDelimiter(recipe, dyn));
            default -> throw new AssertionError(minted);
        };
    }

    /**
     * The ROPE factory is the force-inlined empty-operand prologue {@code ropeInlinePrologue} with the out-of-line
     * construction {@code ropeOutOfLine}, with the same semantics as the plain {@code rope}.
     */
    @Test
    public void theRopeFactoryIsTheInlinePrologue() throws Exception {
        Method off = LazyConcatFactory.class.getDeclaredMethod("rope", String.class, String.class);
        Method on = LazyConcatMint.factoryMethod("ROPE");
        Assert.assertNull(off.getAnnotation(com.oracle.svm.core.AlwaysInline.class));
        Assert.assertEquals("ropeInlinePrologue", on.getName());
        Assert.assertNotNull("the prologue is force-inlined", on.getAnnotation(com.oracle.svm.core.AlwaysInline.class));
        Method outOfLine = LazyConcatFactory.class.getDeclaredMethod("ropeOutOfLine", String.class, String.class);
        Assert.assertNotNull("the construction stays out of line", outOfLine.getAnnotation(com.oracle.svm.core.NeverInline.class));
        // the same semantics: an empty side with a plain other side gives a new plain String equal to it; otherwise a rope
        String rep = (String) off.invoke(null, "x", "y");
        String[][] cases = {{"", "ab"}, {"ab", ""}, {"", ""}, {"a", "b"}, {"", null}, {null, ""}};
        for (String[] c : cases) {
            String a = c[0] == null ? rep : c[0];
            String b = c[1] == null ? rep : c[1];
            Object r0 = off.invoke(null, a, b);
            Object r1 = on.invoke(null, a, b);
            String what = "(" + (c[0] == null ? "<rope>" : '"' + a + '"') + ", " + (c[1] == null ? "<rope>" : '"' + b + '"') + ")";
            Assert.assertSame(what, r0.getClass(), r1.getClass());
            Assert.assertEquals(what, r0.toString(), r1.toString());
            Assert.assertNotSame(what, a, r1);
            Assert.assertNotSame(what, b, r1);
        }
    }

    private static String show(String recipe) {
        return recipe == null ? "<makeConcat>" : recipe.replace('\u0001', '#').replace('\u0002', '$');
    }

    private static SugVertex concatVertex(String methodName, int dyn, String recipe) {
        SugVertex v = new SugVertex(1);
        v.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        v.setMethodName(methodName);
        v.setDynamicOperandCount(dyn);
        v.setConcatRecipe(recipe);
        return v;
    }

    @Test
    public void theChildNamesTheMintedRepThroughTheSameFunction() {
        for (String variant : new String[]{"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED"}) {
            for (int dyn = 1; dyn <= 7; dyn++) {
                for (String recipe : recipes(dyn)) {
                    SugVertex v = concatVertex(recipe == null ? "makeConcat" : "makeConcatWithConstants", dyn, recipe);
                    InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, variant);
                    Assert.assertEquals(variant + "/" + dyn + "/" + show(recipe), LazyConcatMint.mintedRep(variant, dyn, recipe), HeuristicOrchestrator.repTypeOf(d));
                }
            }
        }
    }

    @Test
    public void theAd2SiteNamesArrayLazy() {
        // Directory#getTempFileName@8: prefix + "_" + Long.toString(counter, 36) -> recipe \1_\1, dyn 2, 3 parts
        SugVertex v = concatVertex("makeConcatWithConstants", 2, "\u0001_\u0001");
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "ROPE");
        Assert.assertEquals("ARRAY_LAZY", HeuristicOrchestrator.repTypeOf(d));
        Assert.assertEquals(6, HeuristicOrchestrator.crossRepPriority(d));
        // a pure 2-dynamic rope stays a rope; "k=" + x is a rope (2 parts)
        Assert.assertEquals("ROPE", HeuristicOrchestrator.repTypeOf(new InstrumentationDecision(concatVertex("makeConcatWithConstants", 2, "\u0001\u0001"), OptimizationType.LAZY_CONCAT, "ROPE")));
        Assert.assertEquals("ROPE", HeuristicOrchestrator.repTypeOf(new InstrumentationDecision(concatVertex("makeConcatWithConstants", 1, "k=\u0001"), OptimizationType.LAZY_CONCAT, "ROPE")));
    }

    @Test
    public void stringConcatCallMintsARopeOnlyAtARopeSite() {
        SugVertex v = concatVertex("concat", 2, null);
        Assert.assertEquals("ROPE", HeuristicOrchestrator.repTypeOf(new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "ROPE")));
        Assert.assertNull(HeuristicOrchestrator.repTypeOf(new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "THREE_WAY")));
        Assert.assertEquals("ROPE", LazyConcatMint.mintedRepForStringConcat("ROPE"));
    }
}
