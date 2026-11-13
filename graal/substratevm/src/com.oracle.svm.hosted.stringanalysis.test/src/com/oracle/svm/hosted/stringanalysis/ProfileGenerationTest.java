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
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

public class ProfileGenerationTest {

    private Path tempFile;

    @Before
    public void setUp() throws IOException {
        tempFile = Files.createTempFile("gen_profile", ".txt");
        tempFile.toFile().deleteOnExit();
    }

    @After
    public void tearDown() throws IOException {
        if (tempFile != null && Files.exists(tempFile)) {
            Files.deleteIfExists(tempFile);
        }
    }

    private static InstrumentationDecision decision(String sourceLocation, OptimizationType type, String variant) {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex vertex = graph.newVertex();
        vertex.setSourceLocation(sourceLocation);
        return new InstrumentationDecision(vertex, type, variant);
    }

    @Test
    public void roundTripAllTypesWithVariant() throws IOException {
        List<InstrumentationDecision> decisions = new ArrayList<>();
        decisions.add(decision("RopeConcatTest#test()V@6", OptimizationType.LAZY_CONCAT, "ROPE"));
        decisions.add(decision("StringViewTest#test()V@10", OptimizationType.STRING_VIEW, null));
        decisions.add(decision("SingleByteTest#test()V@5", OptimizationType.SINGLE_BYTE, null));

        StringAnalysisFeature.dumpProfile(decisions, tempFile.toAbsolutePath().toString());

        RepresentationProfile profile = RepresentationProfileLoader.load(tempFile.toAbsolutePath().toString());
        Assert.assertEquals(3, profile.getTotalCount());

        ProfileEntry rope = profile.getEntry("RopeConcatTest#test()V@6");
        Assert.assertNotNull(rope);
        Assert.assertEquals(OptimizationType.LAZY_CONCAT, rope.getType());
        Assert.assertEquals("ROPE", rope.getVariant());

        ProfileEntry view = profile.getEntry("StringViewTest#test()V@10");
        Assert.assertNotNull(view);
        Assert.assertEquals(OptimizationType.STRING_VIEW, view.getType());
        Assert.assertNull(view.getVariant());

        ProfileEntry single = profile.getEntry("SingleByteTest#test()V@5");
        Assert.assertNotNull(single);
        Assert.assertEquals(OptimizationType.SINGLE_BYTE, single.getType());
        Assert.assertNull(single.getVariant());
    }

    @Test
    public void noneDecisionsAreSkipped() throws IOException {
        List<InstrumentationDecision> decisions = new ArrayList<>();
        decisions.add(decision("A#m()V@1", OptimizationType.LAZY_CONCAT, "ROPE"));
        decisions.add(decision("B#m()V@2", OptimizationType.NONE, null));
        decisions.add(decision("C#m()V@3", OptimizationType.SINGLE_BYTE, null));

        StringAnalysisFeature.dumpProfile(decisions, tempFile.toAbsolutePath().toString());

        RepresentationProfile profile = RepresentationProfileLoader.load(tempFile.toAbsolutePath().toString());
        Assert.assertEquals(2, profile.getTotalCount());
        Assert.assertTrue(profile.hasEntry("A#m()V@1"));
        Assert.assertFalse(profile.hasEntry("B#m()V@2"));
        Assert.assertTrue(profile.hasEntry("C#m()V@3"));
    }

    @Test
    public void emptyDecisionListProducesEmptyProfile() throws IOException {
        List<InstrumentationDecision> decisions = new ArrayList<>();
        StringAnalysisFeature.dumpProfile(decisions, tempFile.toAbsolutePath().toString());
        RepresentationProfile profile = RepresentationProfileLoader.load(tempFile.toAbsolutePath().toString());
        Assert.assertEquals(0, profile.getTotalCount());
    }

    @Test
    public void generatedFileMatchesExpectedLineFormat() throws IOException {
        List<InstrumentationDecision> decisions = new ArrayList<>();
        decisions.add(decision("X#m()V@1", OptimizationType.LAZY_CONCAT, "ROPE"));
        decisions.add(decision("Y#m()V@2", OptimizationType.STRING_VIEW, null));

        StringAnalysisFeature.dumpProfile(decisions, tempFile.toAbsolutePath().toString());

        List<String> lines = Files.readAllLines(tempFile);
        Assert.assertEquals(2, lines.size());
        Assert.assertEquals("X#m()V@1 LAZY_CONCAT ROPE", lines.get(0));
        Assert.assertEquals("Y#m()V@2 STRING_VIEW", lines.get(1));
    }

    @Test
    public void ioErrorOnInvalidPathThrows() {
        List<InstrumentationDecision> decisions = new ArrayList<>();
        decisions.add(decision("A#m()V@1", OptimizationType.SINGLE_BYTE, null));
        try {
            StringAnalysisFeature.dumpProfile(decisions, "/nonexistent/dir/does/not/exist/profile.txt");
            Assert.fail("Expected RuntimeException for invalid path");
        } catch (RuntimeException e) {
            Assert.assertTrue("Expected 'Failed to dump' in message: " + e.getMessage(),
                            e.getMessage().contains("Failed to dump"));
        }
    }

    @Test
    public void duplicateSameSourceSameTypeVariantDedupedSilently() throws IOException {
        List<InstrumentationDecision> decisions = new ArrayList<>();
        decisions.add(decision("D#m()V@1", OptimizationType.LAZY_CONCAT, "ROPE"));
        decisions.add(decision("D#m()V@1", OptimizationType.LAZY_CONCAT, "ROPE"));

        StringAnalysisFeature.dumpProfile(decisions, tempFile.toAbsolutePath().toString());

        RepresentationProfile profile = RepresentationProfileLoader.load(tempFile.toAbsolutePath().toString());
        Assert.assertEquals(1, profile.getTotalCount());
        ProfileEntry entry = profile.getEntry("D#m()V@1");
        Assert.assertNotNull(entry);
        Assert.assertEquals(OptimizationType.LAZY_CONCAT, entry.getType());
        Assert.assertEquals("ROPE", entry.getVariant());
    }

    @Test
    public void duplicateSameSourceDifferentTypeKeepsBoth() throws IOException {
        List<InstrumentationDecision> decisions = new ArrayList<>();
        decisions.add(decision("E#m()V@1", OptimizationType.LAZY_CONCAT, "ROPE"));
        decisions.add(decision("E#m()V@1", OptimizationType.SINGLE_BYTE, null));

        StringAnalysisFeature.dumpProfile(decisions, tempFile.toAbsolutePath().toString());

        RepresentationProfile profile = RepresentationProfileLoader.load(tempFile.toAbsolutePath().toString());
        Assert.assertEquals(2, profile.getTotalCount());
        ProfileEntry lazy = profile.getEntry("E#m()V@1", OptimizationType.LAZY_CONCAT);
        Assert.assertNotNull(lazy);
        Assert.assertEquals(OptimizationType.LAZY_CONCAT, lazy.getType());
        Assert.assertEquals("ROPE", lazy.getVariant());
        ProfileEntry single = profile.getEntry("E#m()V@1", OptimizationType.SINGLE_BYTE);
        Assert.assertNotNull(single);
        Assert.assertEquals(OptimizationType.SINGLE_BYTE, single.getType());
    }

    @Test
    public void unknownSourceLocationRoundTrip() throws IOException {
        List<InstrumentationDecision> decisions = new ArrayList<>();
        decisions.add(decision("<unknown>#<unknown>@-1", OptimizationType.STRING_VIEW, null));

        StringAnalysisFeature.dumpProfile(decisions, tempFile.toAbsolutePath().toString());

        RepresentationProfile profile = RepresentationProfileLoader.load(tempFile.toAbsolutePath().toString());
        Assert.assertEquals(1, profile.getTotalCount());
        ProfileEntry entry = profile.getEntry("<unknown>#<unknown>@-1");
        Assert.assertNotNull(entry);
        Assert.assertEquals(OptimizationType.STRING_VIEW, entry.getType());
        Assert.assertNull(entry.getVariant());
    }
}