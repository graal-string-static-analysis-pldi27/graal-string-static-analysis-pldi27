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

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Map;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

public class RepresentationProfileTest {

    private File tempFile;

    @Before
    public void setUp() throws IOException {
        tempFile = File.createTempFile("rep_profile", ".txt");
        tempFile.deleteOnExit();
    }

    @After
    public void tearDown() {
        if (tempFile != null && tempFile.exists()) {
            tempFile.delete();
        }
        RepresentationProfileHolder.clear();
    }

    private void writeProfile(String content) throws IOException {
        Files.writeString(tempFile.toPath(), content);
    }

    private RepresentationProfile loadProfile() throws IOException {
        return RepresentationProfileLoader.load(tempFile.getAbsolutePath());
    }

    @Test
    public void validProfileThreeEntries() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n" +
                        "StringViewTest#test()V@10 STRING_VIEW\n" +
                        "SingleByteTest#test()V@5 SINGLE_BYTE\n");
        RepresentationProfile profile = loadProfile();
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
    public void commentsAndBlankLinesIgnored() throws IOException {
        writeProfile("# This is a comment\n" +
                        "\n" +
                        "   # indented comment\n" +
                        "RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n" +
                        "\n" +
                        "  \n" +
                        "StringViewTest#test()V@10 STRING_VIEW\n" +
                        "# another comment\n");
        RepresentationProfile profile = loadProfile();
        Assert.assertEquals(2, profile.getTotalCount());
        Assert.assertTrue(profile.hasEntry("RopeConcatTest#test()V@6"));
        Assert.assertTrue(profile.hasEntry("StringViewTest#test()V@10"));
    }

    @Test
    public void lazyConcatRopeVariant() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n");
        RepresentationProfile profile = loadProfile();
        ProfileEntry entry = profile.getEntry("RopeConcatTest#test()V@6");
        Assert.assertNotNull(entry);
        Assert.assertEquals("ROPE", entry.getVariant());
    }

    @Test
    public void singleByteNoVariant() throws IOException {
        writeProfile("SingleByteTest#test()V@5 SINGLE_BYTE\n");
        RepresentationProfile profile = loadProfile();
        ProfileEntry entry = profile.getEntry("SingleByteTest#test()V@5");
        Assert.assertNotNull(entry);
        Assert.assertNull(entry.getVariant());
    }

    @Test
    public void stringViewNoVariant() throws IOException {
        writeProfile("StringViewTest#test()V@10 STRING_VIEW\n");
        RepresentationProfile profile = loadProfile();
        ProfileEntry entry = profile.getEntry("StringViewTest#test()V@10");
        Assert.assertNotNull(entry);
        Assert.assertNull(entry.getVariant());
    }

    @Test
    public void conflictSameSourceDifferentTypes() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n" +
                        "RopeConcatTest#test()V@6 SINGLE_BYTE\n");
        RepresentationProfile profile = loadProfile();
        Assert.assertEquals(2, profile.getTotalCount());
        ProfileEntry lazy = profile.getEntry("RopeConcatTest#test()V@6", OptimizationType.LAZY_CONCAT);
        Assert.assertNotNull(lazy);
        Assert.assertEquals(OptimizationType.LAZY_CONCAT, lazy.getType());
        ProfileEntry single = profile.getEntry("RopeConcatTest#test()V@6", OptimizationType.SINGLE_BYTE);
        Assert.assertNotNull(single);
        Assert.assertEquals(OptimizationType.SINGLE_BYTE, single.getType());
    }

    @Test
    public void conflictSameSourceSameTypeDifferentVariant() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n" +
                        "RopeConcatTest#test()V@6 LAZY_CONCAT ARRAY\n");
        try {
            loadProfile();
            Assert.fail("Expected IllegalArgumentException for conflicting variants");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue("Expected 'Conflicting' in message: " + e.getMessage(),
                            e.getMessage().contains("Conflicting"));
        }
    }

    @Test
    public void duplicateIdempotent() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n" +
                        "RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n");
        RepresentationProfile profile = loadProfile();
        Assert.assertEquals(1, profile.getTotalCount());
    }

    @Test
    public void nonExistentFileThrows() {
        try {
            RepresentationProfileLoader.load("/nonexistent/path/to/profile.txt");
            Assert.fail("Expected IOException for non-existent file");
        } catch (IOException e) {
            // expected
        }
    }

    @Test
    public void invalidTypeStringThrows() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 INVALID\n");
        try {
            loadProfile();
            Assert.fail("Expected IllegalArgumentException for invalid type");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue("Expected 'Invalid optimization type' in message: " + e.getMessage(),
                            e.getMessage().contains("Invalid optimization type"));
        }
    }

    @Test
    public void wrongFieldCountOneFieldThrows() throws IOException {
        writeProfile("RopeConcatTest#test()V@6\n");
        try {
            loadProfile();
            Assert.fail("Expected IllegalArgumentException for wrong field count");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue("Expected 'Invalid profile entry' in message: " + e.getMessage(),
                            e.getMessage().contains("Invalid profile entry"));
        }
    }

    @Test
    public void wrongFieldCountFourFieldsThrows() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE EXTRA\n");
        try {
            loadProfile();
            Assert.fail("Expected IllegalArgumentException for wrong field count");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue("Expected 'Invalid profile entry' in message: " + e.getMessage(),
                            e.getMessage().contains("Invalid profile entry"));
        }
    }

    @Test
    public void getEntryReturnsCorrectEntry() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n");
        RepresentationProfile profile = loadProfile();
        ProfileEntry entry = profile.getEntry("RopeConcatTest#test()V@6");
        Assert.assertNotNull(entry);
        Assert.assertEquals(OptimizationType.LAZY_CONCAT, entry.getType());
    }

    @Test
    public void getEntryNonexistentReturnsNull() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n");
        RepresentationProfile profile = loadProfile();
        Assert.assertNull(profile.getEntry("Nonexistent#test()V@99"));
    }

    @Test
    public void hasEntryTrueAndFalse() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n");
        RepresentationProfile profile = loadProfile();
        Assert.assertTrue(profile.hasEntry("RopeConcatTest#test()V@6"));
        Assert.assertFalse(profile.hasEntry("Nonexistent#test()V@99"));
    }

    @Test
    public void getAllEntriesUnmodifiable() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n");
        RepresentationProfile profile = loadProfile();
        Map<String, ProfileEntry> all = profile.getAllEntries();
        try {
            all.put("Hacked#test()V@1", new ProfileEntry("Hacked#test()V@1", OptimizationType.NONE, null));
            Assert.fail("Expected UnsupportedOperationException");
        } catch (UnsupportedOperationException e) {
            // expected
        }
    }

    @Test
    public void profileEntryToStringWithVariant() {
        ProfileEntry entry = new ProfileEntry("RopeConcatTest#test()V@6", OptimizationType.LAZY_CONCAT, "ROPE");
        Assert.assertEquals("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE", entry.toString());
    }

    @Test
    public void profileEntryToStringWithoutVariant() {
        ProfileEntry entry = new ProfileEntry("SingleByteTest#test()V@5", OptimizationType.SINGLE_BYTE, null);
        Assert.assertEquals("SingleByteTest#test()V@5 SINGLE_BYTE", entry.toString());
    }

    @Test
    public void allThreeTypesInOneFile() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n" +
                        "StringViewTest#test()V@10 STRING_VIEW\n" +
                        "SingleByteTest#test()V@5 SINGLE_BYTE\n");
        RepresentationProfile profile = loadProfile();
        Assert.assertEquals(3, profile.getTotalCount());
        Assert.assertEquals(OptimizationType.LAZY_CONCAT, profile.getEntry("RopeConcatTest#test()V@6").getType());
        Assert.assertEquals(OptimizationType.STRING_VIEW, profile.getEntry("StringViewTest#test()V@10").getType());
        Assert.assertEquals(OptimizationType.SINGLE_BYTE, profile.getEntry("SingleByteTest#test()V@5").getType());
    }

    @Test
    public void emptyFileZeroEntries() throws IOException {
        writeProfile("");
        RepresentationProfile profile = loadProfile();
        Assert.assertEquals(0, profile.getTotalCount());
    }

    @Test
    public void onlyCommentsZeroEntries() throws IOException {
        writeProfile("# comment 1\n# comment 2\n   # indented comment\n");
        RepresentationProfile profile = loadProfile();
        Assert.assertEquals(0, profile.getTotalCount());
    }

    @Test
    public void holderSetGetClear() throws IOException {
        writeProfile("RopeConcatTest#test()V@6 LAZY_CONCAT ROPE\n");
        RepresentationProfile profile = loadProfile();
        Assert.assertFalse(RepresentationProfileHolder.hasProfile());
        RepresentationProfileHolder.setInstance(profile);
        Assert.assertTrue(RepresentationProfileHolder.hasProfile());
        Assert.assertSame(profile, RepresentationProfileHolder.getInstance());
        RepresentationProfileHolder.clear();
        Assert.assertFalse(RepresentationProfileHolder.hasProfile());
        Assert.assertNull(RepresentationProfileHolder.getInstance());
    }
}