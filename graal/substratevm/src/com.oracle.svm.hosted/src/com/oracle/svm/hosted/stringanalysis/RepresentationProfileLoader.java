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

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public final class RepresentationProfileLoader {

    private RepresentationProfileLoader() {
    }

    public static RepresentationProfile load(String filePath) throws IOException {
        Map<String, Map<OptimizationType, ProfileEntry>> entries = new LinkedHashMap<>();
        Map<String, Set<String>> pairs = new LinkedHashMap<>();
        Map<String, String> concatCopy = new LinkedHashMap<>();
        Set<String> exactRecv = new LinkedHashSet<>();
        Map<String, String> mirror = new LinkedHashMap<>();
        Map<String, String> typeCheck = new LinkedHashMap<>();
        try (BufferedReader reader = Files.newBufferedReader(Paths.get(filePath))) {
            String line;
            int lineNum = 0;
            while ((line = reader.readLine()) != null) {
                lineNum++;
                line = line.trim();
                if (line.isEmpty() || line.startsWith("#")) {
                    continue;
                }

                String[] parts = line.split("\\s+");
                if (parts.length >= 2 && TypeCheckLines.LINE_TYPE.equals(parts[1])) {
                    // Type-check IC: <key> TYPE_CHECK CAST|INST <variant> (the child's per-site rep set of a String type check)
                    if (!TypeCheckLines.isLine(parts)) {
                        throw new IllegalArgumentException("Invalid " + TypeCheckLines.LINE_TYPE + " entry at line " + lineNum + ": expected '<key> " + TypeCheckLines.LINE_TYPE +
                                        " CAST|INST <variant>', got: " + line);
                    }
                    String v = parts[2] + " " + parts[3];
                    String prev = typeCheck.putIfAbsent(parts[0], v);
                    if (prev != null && !prev.equals(v)) {
                        throw new IllegalArgumentException("Conflicting " + TypeCheckLines.LINE_TYPE + " entry at line " + lineNum + ": " + parts[0] + " is already " + prev + ", got: " + line);
                    }
                    continue;
                }
                if (parts.length >= 2 && AppendMirror.LINE_TYPE.equals(parts[1])) {
                    // <key> MIRROR <KIND> <rep,...> (a builder entry-point site the parent lowers to the mirror chain)
                    if (!isMirrorLine(parts)) {
                        throw new IllegalArgumentException("Invalid " + AppendMirror.LINE_TYPE + " entry at line " + lineNum + ": expected '<key> " + AppendMirror.LINE_TYPE +
                                        " APPEND|APPEND_RANGE|INSERT|INSERT_SEQ|INSERT_RANGE|REPLACE|INIT <rep,...>', got: " + line);
                    }
                    String v = parts[2] + " " + parts[3];
                    String prev = mirror.putIfAbsent(parts[0], v);
                    if (prev != null && !prev.equals(v)) {
                        throw new IllegalArgumentException("Conflicting " + AppendMirror.LINE_TYPE + " entry at line " + lineNum + ": " + parts[0] + " is already " + prev + ", got: " + line);
                    }
                    continue;
                }
                // A fourth token is the exact accumulator class of a STRING_VIEW ACCUMULATOR_VIEW(_SHARED) entry. Trusted
                // input: the parent lowers the site on this class behind an analysis-only filter that is removed in
                // ic.exactpi modes 0/1; it is validated (a ClassCastException on a wrong class) only in CHECK mode
                // (ic.exactpi=2). A forced/hand-written profile must be validated with ic.exactpi=2.
                boolean accLine = parts.length == 4 && "STRING_VIEW".equals(parts[1]) && ("ACCUMULATOR_VIEW".equals(parts[2]) || "ACCUMULATOR_VIEW_SHARED".equals(parts[2]));
                // A StringJoiner extraction is '<key> LAZY_CONCAT INTERLEAVED java.util.StringJoiner' (the same trusted class token)
                accLine |= parts.length == 4 && isJoinerLine(parts[1], parts[2], parts[3]);
                if (parts.length < 2 || (parts.length > 3 && !accLine)) {
                    throw new IllegalArgumentException(
                                    "Invalid profile entry at line " + lineNum +
                                                    ": expected '<key> TYPE [VARIANT]', '<key> STRING_VIEW ACCUMULATOR_VIEW[_SHARED] <class>' or '<key> LAZY_CONCAT INTERLEAVED java.util.StringJoiner' (key = class#method@bci), got: " +
                                                    line);
                }
                if (parts.length == 3 && StringViewHeuristic.CONCAT_COPY_TYPE.equals(parts[1])) {
                    // <key> CONCAT_COPY UNARY|BINARY (a copying indy concat the parent lowers with RepConcat)
                    if (!isConcatCopyShape(parts[2]) || parts[0].indexOf('@') < 0) {
                        throw new IllegalArgumentException("Invalid CONCAT_COPY entry at line " + lineNum + ": expected '<key> CONCAT_COPY UNARY|BINARY', got: " + line);
                    }
                    String prev = concatCopy.putIfAbsent(parts[0], parts[2]);
                    if (prev != null && !prev.equals(parts[2])) {
                        throw new IllegalArgumentException("Conflicting CONCAT_COPY entry at line " + lineNum + ": " + parts[0] + " is already " + prev + ", got: " + line);
                    }
                    continue;
                }
                if (parts.length >= 2 && ExactReceiverSites.LINE_TYPE.equals(parts[1])) {
                    // <key> EXACT_RECV STRING (the child's exact-{String} receiver proof at a supertype site)
                    if (parts.length != 3 || !ExactReceiverSites.VARIANT.equals(parts[2]) || parts[0].indexOf('@') < 0) {
                        throw new IllegalArgumentException("Invalid " + ExactReceiverSites.LINE_TYPE + " entry at line " + lineNum + ": expected '<key> " + ExactReceiverSites.LINE_TYPE + " " +
                                        ExactReceiverSites.VARIANT + "', got: " + line);
                    }
                    exactRecv.add(parts[0]);
                    continue;
                }
                if (parts.length == 3 && LazyOperandPairing.PAIR_TYPE.equals(parts[1])) {
                    // KT precision: <inner> LAZY_PAIR <outer> (the child's pairing contract, LazyOperandPairing)
                    pairs.computeIfAbsent(parts[0], k -> new LinkedHashSet<>()).add(parts[2]);
                    continue;
                }
                String source = parts[0];
                if (source.indexOf('@') < 0) {
                    throw new IllegalArgumentException(
                                    "Profile entry at line " + lineNum +
                                                    " uses the old 'file:line' key format of an older version. Regenerate the profile with -H:+StringAnalysis. Got: " + line);
                }
                String typeStr = parts[1];
                String variant = parts.length >= 3 ? parts[2] : null;
                String accClass = accLine ? parts[3] : null;

                OptimizationType type;
                try {
                    type = OptimizationType.valueOf(typeStr);
                } catch (IllegalArgumentException e) {
                    throw new IllegalArgumentException(
                                    "Invalid optimization type at line " + lineNum +
                                                    ": '" + typeStr + "'. Expected one of: SINGLE_BYTE, STRING_VIEW, LAZY_CONCAT, EQUALS_MATRIX, INLINE_CACHE, NONE");
                }

                Map<OptimizationType, ProfileEntry> sourceEntries = entries.get(source);
                if (sourceEntries == null) {
                    sourceEntries = new LinkedHashMap<>();
                    entries.put(source, sourceEntries);
                }
                ProfileEntry existing = sourceEntries.get(type);
                if (existing != null) {
                    if (!Objects.equals(existing.getVariant(), variant) || !Objects.equals(existing.getAccumulatorClass(), accClass)) {
                        throw new IllegalArgumentException(
                                        "Conflicting profile entry at line " + lineNum +
                                                        ": source '" + source + "' type " + typeStr +
                                                        " is already mapped to variant " +
                                                        (existing.getVariant() != null ? existing.getVariant() : "<null>") +
                                                        (existing.getAccumulatorClass() != null ? " " + existing.getAccumulatorClass() : "") +
                                                        ", cannot also map to variant " +
                                                        (variant != null ? variant : "<null>") + (accClass != null ? " " + accClass : ""));
                    }
                } else {
                    sourceEntries.put(type, new ProfileEntry(source, type, variant, accClass));
                }
            }
        }
        for (String key : concatCopy.keySet()) {
            Map<OptimizationType, ProfileEntry> e = entries.get(key);
            if (e != null && e.containsKey(OptimizationType.LAZY_CONCAT)) {
                // The child's invariant (StringViewHeuristic.concatCopyLines): a lowered copying site is never a lazy site
                throw new IllegalArgumentException("Profile key " + key + " has both a CONCAT_COPY and a LAZY_CONCAT entry");
            }
        }
        for (String key : mirror.keySet()) {
            if (entries.containsKey(key) || concatCopy.containsKey(key) || exactRecv.contains(key) || pairs.containsKey(key)) {
                // A builder entry-point site carries no other entry (the child's keys are disjoint by construction)
                throw new IllegalArgumentException("Profile key " + key + " has both a " + AppendMirror.LINE_TYPE + " and another entry");
            }
        }
        return new RepresentationProfile(entries, true, pairs, concatCopy, exactRecv, mirror, typeCheck);
    }

    /** Pure (pinned by JUnit): the shape of a {@code MIRROR} line: a site key, a known kind, a non-empty rep list. */
    static boolean isMirrorLine(String[] parts) {
        if (parts.length != 4 || parts[0].indexOf('@') < 0) {
            return false;
        }
        try {
            AppendMirror.Kind.valueOf(parts[2]);
        } catch (IllegalArgumentException e) {
            return false;
        }
        for (String r : parts[3].split(",")) {
            if (r.isEmpty()) {
                return false;
            }
        }
        return true;
    }

    /** Pure: the shape token of a {@code CONCAT_COPY} line. */
    static boolean isConcatCopyShape(String token) {
        return StringAtoms.CopyShape.UNARY.name().equals(token) || StringAtoms.CopyShape.BINARY.name().equals(token);
    }

    /** Pure (pinned by JUnit): the 4-token joiner extraction line {@code LAZY_CONCAT INTERLEAVED java.util.StringJoiner}. */
    static boolean isJoinerLine(String type, String variant, String accClass) {
        return "LAZY_CONCAT".equals(type) && LazyConcatMint.INTERLEAVED.equals(variant) && AccumulatorWhitelist.JOINER.equals(accClass);
    }
}
