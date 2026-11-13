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
import java.lang.reflect.Modifier;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.StringJoiner;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.InterleavedStringArray;

/**
 * {@code java.util.StringJoiner} as an accumulator kind. Pins the joiner's pass-1 table (every public method
 * StringJoiner declares is classified exactly once; {@code merge} only as the receiver: as the argument it rewrites
 * {@code elts[0, size)} in place), the {@code return this} rule, the knob-gated seeding and name tables, the profile
 * line, the mint floor, and the rep layout (no field for the joiner variant). The joiner variant's semantics are
 * checked in the image: its alias of the StringJoiner fields does not resolve on the
 * JVM.
 */
public class StringJoinerAccumulatorTest {

    private static final String SJ = "java.util.StringJoiner";

    @Test
    public void everyPublicJoinerMethodIsClassified() {
        Set<String> seen = new TreeSet<>();
        for (Method m : StringJoiner.class.getDeclaredMethods()) {
            if (!Modifier.isPublic(m.getModifiers()) || m.isSynthetic() || m.isBridge()) {
                continue;
            }
            String n = m.getName();
            seen.add(n);
            int classes = (AccumulatorWhitelist.JOINER_GROWING_METHODS.contains(n) ? 1 : 0) + (AccumulatorWhitelist.JOINER_READ_ONLY_METHODS.contains(n) ? 1 : 0);
            Assert.assertEquals("unclassified (or doubly classified) StringJoiner method " + n, 1, classes);
        }
        for (Set<String> set : List.of(AccumulatorWhitelist.JOINER_GROWING_METHODS, AccumulatorWhitelist.JOINER_READ_ONLY_METHODS)) {
            for (String n : set) {
                Assert.assertTrue("stale entry " + n, n.equals("<init>") || seen.contains(n));
            }
        }
        Assert.assertEquals(Set.of("add", "merge", "setEmptyValue", "toString", "length"), seen);
    }

    @Test
    public void decisionRows() {
        for (String n : List.of("<init>", "add", "merge", "setEmptyValue", "toString", "length")) {
            Assert.assertEquals(n, AccumulatorWhitelist.AccRow.GROWING, AccumulatorWhitelist.accumulatorUsageRow(SJ, n, UsageRole.RECEIVER));
        }
        // the merge ARGUMENT: other.compactElts() rewrites elts[0, size) in place
        Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow(SJ, "merge", UsageRole.PARAMETER));
        // a walk entering merge at its argument meets the private compactElts and raw field reads: REJECT
        for (String n : List.of("compactElts", "checkAddLength", "field:elts", "field:size", "field:emptyValue")) {
            Assert.assertEquals(n, AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow(SJ, n, UsageRole.RECEIVER));
        }
        // the identity reads stay reads; the builder tables are not widened by the joiner's names
        Assert.assertEquals(AccumulatorWhitelist.AccRow.READ, AccumulatorWhitelist.accumulatorUsageRow("java.lang.Object", "hashCode", UsageRole.RECEIVER));
        Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow("java.lang.StringBuilder", "add", UsageRole.RECEIVER));
        Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow("java.io.StringWriter", "merge", UsageRole.RECEIVER));
        Assert.assertTrue(AccumulatorWhitelist.isTableDeclaring(SJ));
    }

    @Test
    public void returnThisRule() {
        Assert.assertTrue(AccumulatorWhitelist.returnsThis(SJ, "add"));
        Assert.assertTrue(AccumulatorWhitelist.returnsThis(SJ, "merge"));
        Assert.assertTrue(AccumulatorWhitelist.returnsThis(SJ, "setEmptyValue"));
        Assert.assertFalse(AccumulatorWhitelist.returnsThis(SJ, "toString"));
        Assert.assertFalse(AccumulatorWhitelist.returnsThis(SJ, "length"));
    }

    @Test
    public void seedingAndNameTablesIncludeTheJoiner() {
        Assert.assertTrue(StringAtoms.ACC_SEED_TYPES.contains(SJ));
        Assert.assertTrue(AccumulatorWhitelist.isSeedableExtraction(SJ, "toString", ""));
        Assert.assertFalse(AccumulatorWhitelist.isSeedableExtraction(SJ, "length", ""));
        Assert.assertTrue(SugNameTables.STRINGY_ALLOC_TYPES.contains(SJ));
        Assert.assertTrue(SugNameTables.ACCUMULATOR_RECEIVERS.contains(SJ));
        Assert.assertTrue(StringTerminalHandList.BUILDER_TYPES.contains(SJ));
        Assert.assertTrue(Arrays.asList(LfgWalk.STRINGY_RAW_MEM_TYPE_NAMES).contains(SJ));
        // a receiver call on a joiner is a terminal usage; its constructor too; the result of add/merge/setEmptyValue is the joiner
        Assert.assertTrue(StringAtoms.isTerminalTarget(false, false, SJ));
        Assert.assertTrue(StringAtoms.isTerminalTarget(false, true, SJ));
        Assert.assertTrue(StringAtoms.continuesAtResult(SJ, "add", "Ljava/lang/CharSequence;", SJ));
        // JDK-internal joiners (Collectors.joining) are never seeds: ACC seeding is user-code only
        Assert.assertFalse(StringAnalysisPolicy.isUserCodeClass("java.util.stream.Collectors"));
    }

    @Test
    public void profileLine() throws Exception {
        Assert.assertTrue(RepresentationProfileLoader.isJoinerLine("LAZY_CONCAT", "INTERLEAVED", SJ));
        Assert.assertFalse(RepresentationProfileLoader.isJoinerLine("LAZY_CONCAT", "INTERLEAVED", "java.lang.StringBuilder"));
        Assert.assertFalse(RepresentationProfileLoader.isJoinerLine("LAZY_CONCAT", "ARRAY_LAZY", SJ));
        Assert.assertFalse(RepresentationProfileLoader.isJoinerLine("STRING_VIEW", "INTERLEAVED", SJ));
        Path tmp = Files.createTempFile("c97sj", ".txt");
        try {
            Files.writeString(tmp, "J#join([Ljava/lang/String;)Ljava/lang/String;@39 LAZY_CONCAT INTERLEAVED java.util.StringJoiner\n");
            ProfileEntry e = RepresentationProfileLoader.load(tmp.toString()).getEntry("J#join([Ljava/lang/String;)Ljava/lang/String;@39", OptimizationType.LAZY_CONCAT);
            Assert.assertEquals("INTERLEAVED", e.getVariant());
            Assert.assertEquals(SJ, e.getAccumulatorClass());
            for (String bad : List.of("K#m()V@1 LAZY_CONCAT INTERLEAVED java.lang.StringBuilder", "K#m()V@1 LAZY_CONCAT ARRAY_LAZY java.util.StringJoiner")) {
                Files.writeString(tmp, bad + "\n");
                try {
                    RepresentationProfileLoader.load(tmp.toString());
                    Assert.fail("a four-token line other than the accumulator/joiner forms must be refused: " + bad);
                } catch (IllegalArgumentException expected) {
                }
            }
        } finally {
            Files.deleteIfExists(tmp);
        }
    }

    @Test
    public void mintsOnlyAboveTheFloorAndNeverForSizeZero() {
        // size 0 (emptyValue identity / prefix+suffix) and short joins run the JDK body itself; the floor is on the
        // joiner's len (parts + delimiters, no affixes): at 9 chars the JDK result (Latin-1 >= 56 B, UTF-16 >= 64 B) is
        // at least the rep (56 B); at 8 chars without affixes a Latin-1 result is 48 B
        Assert.assertEquals(9, InterleavedStringArray.JOINER_MIN_CHARS);
        Assert.assertFalse(InterleavedStringArray.joinerMintsRep(0, 0));
        Assert.assertFalse(InterleavedStringArray.joinerMintsRep(0, 100)); // size 0 after an add's OutOfMemoryError
        Assert.assertFalse(InterleavedStringArray.joinerMintsRep(1, 8));
        Assert.assertTrue(InterleavedStringArray.joinerMintsRep(5, 9)); // jdk-micro count=5 length=1 (a tie: 56 B)
        Assert.assertTrue(InterleavedStringArray.joinerMintsRep(1, 9));
        Assert.assertTrue(InterleavedStringArray.joinerMintsRep(5, 44)); // jdk-micro count=5 length=8
        Assert.assertTrue(InterleavedStringArray.joinerMintsRep(20, 39)); // jdk-micro count=20 length=1
    }

    /**
     * The premise of {@code ofJoiner}'s one inline compare ({@code len < JOINER_MIN_CHARS}, the size test out
     * of line): the JDK joiner's {@code len} (= {@code length()} minus the affixes while no empty value is set) is 0 at
     * size 0 and counts the parts and the delimiters between them, nothing else.
     */
    @Test
    public void joinerLenIsZeroAtSizeZeroAndCountsPartsAndDelimiters() {
        StringJoiner j = new StringJoiner(", ", "[[", "]");
        Assert.assertEquals(0, j.length() - 3);
        Assert.assertTrue(j.length() - 3 < InterleavedStringArray.JOINER_MIN_CHARS);
        j.add("abc");
        Assert.assertEquals(3, j.length() - 3);
        j.add("de");
        Assert.assertEquals(3 + 2 + 2, j.length() - 3);
        j.add("");
        Assert.assertEquals(3 + 2 + 2 + 2, j.length() - 3);
        Assert.assertTrue(InterleavedStringArray.joinerMintsRep(3, j.length() - 3));
        StringJoiner m = new StringJoiner("-");
        m.add("x").add("y");
        j.merge(m); // the receiver grows by one part ("x-y") and one delimiter
        Assert.assertEquals(9 + 2 + 3, j.length() - 3);
        Assert.assertEquals("[[abc, de, , x-y]", j.toString());
    }

    /**
     * The joiner variant adds no field. The instance layout stays at 56 bytes: the parts,
     * their count, the length and one delimiter slot, typed {@code Object} because it holds either the delimiter String
     * or the StringJoiner (whose affixes and delimiter are read through the alias).
     */
    @Test
    public void theJoinerVariantAddsNoField() {
        Set<String> fields = new TreeSet<>();
        for (java.lang.reflect.Field f : InterleavedStringArray.class.getDeclaredFields()) {
            if (!Modifier.isStatic(f.getModifiers())) {
                fields.add(f.getName() + ":" + f.getType().getSimpleName());
            }
        }
        Assert.assertEquals(new TreeSet<>(List.of("count:int", "delimiter:Object", "elements:String[]", "length:int")), fields);
    }
}
