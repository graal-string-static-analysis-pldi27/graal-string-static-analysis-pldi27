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

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

public final class RepresentationProfile {

    private final Map<String, Map<OptimizationType, ProfileEntry>> entriesBySource;
    private final int totalCount;
    /** KT precision: inner key -> its paired outer keys ({@link LazyOperandPairing}); the outer keys of any pair. */
    private final Map<String, Set<String>> lazyPairs;
    private final Set<String> pairedOuters;
    /** The copying indy concat sites the parent lowers with RepConcat: key -> UNARY|BINARY ({@code CONCAT_COPY}). */
    private final Map<String, String> concatCopy;
    /** The supertype-declared IC sites whose receiver the child proved exactly {String} ({@code EXACT_RECV}). */
    private final Set<String> exactRecv;
    /** The builder entry-point sites the parent lowers to the mirror chain: key -> "KIND rep,rep" ({@code MIRROR}). */
    private final Map<String, String> mirror;
    /** Type-check IC: the String type-check sites: key -> "CAST|INST variant" ({@code TYPE_CHECK}). */
    private final Map<String, String> typeCheck;

    public RepresentationProfile(Map<String, ProfileEntry> entries) {
        Map<String, Map<OptimizationType, ProfileEntry>> multi = new LinkedHashMap<>();
        int count = 0;
        for (Map.Entry<String, ProfileEntry> e : entries.entrySet()) {
            ProfileEntry pe = e.getValue();
            multi.computeIfAbsent(e.getKey(), k -> new LinkedHashMap<>()).put(pe.getType(), pe);
            count++;
        }
        this.entriesBySource = Collections.unmodifiableMap(multi);
        this.totalCount = count;
        this.lazyPairs = Collections.emptyMap();
        this.pairedOuters = Collections.emptySet();
        this.concatCopy = Collections.emptyMap();
        this.exactRecv = Collections.emptySet();
        this.mirror = Collections.emptyMap();
        this.typeCheck = Collections.emptyMap();
    }

    public RepresentationProfile(Map<String, Map<OptimizationType, ProfileEntry>> entries, boolean multi) {
        this(entries, multi, Collections.emptyMap());
    }

    public RepresentationProfile(Map<String, Map<OptimizationType, ProfileEntry>> entries, boolean multi, Map<String, Set<String>> pairs) {
        this(entries, multi, pairs, Collections.emptyMap());
    }

    public RepresentationProfile(Map<String, Map<OptimizationType, ProfileEntry>> entries, boolean multi, Map<String, Set<String>> pairs, Map<String, String> concatCopy) {
        this(entries, multi, pairs, concatCopy, Collections.emptySet());
    }

    public RepresentationProfile(Map<String, Map<OptimizationType, ProfileEntry>> entries, boolean multi, Map<String, Set<String>> pairs, Map<String, String> concatCopy,
                    Set<String> exactRecv) {
        this(entries, multi, pairs, concatCopy, exactRecv, Collections.emptyMap());
    }

    public RepresentationProfile(Map<String, Map<OptimizationType, ProfileEntry>> entries, boolean multi, Map<String, Set<String>> pairs, Map<String, String> concatCopy,
                    Set<String> exactRecv, Map<String, String> mirror) {
        this(entries, multi, pairs, concatCopy, exactRecv, mirror, Collections.emptyMap());
    }

    public RepresentationProfile(Map<String, Map<OptimizationType, ProfileEntry>> entries, boolean multi, Map<String, Set<String>> pairs, Map<String, String> concatCopy,
                    Set<String> exactRecv, Map<String, String> mirror, Map<String, String> typeCheck) {
        Map<String, Map<OptimizationType, ProfileEntry>> copy = new LinkedHashMap<>();
        int count = 0;
        for (Map.Entry<String, Map<OptimizationType, ProfileEntry>> e : entries.entrySet()) {
            copy.put(e.getKey(), new LinkedHashMap<>(e.getValue()));
            count += e.getValue().size();
        }
        this.entriesBySource = Collections.unmodifiableMap(copy);
        this.totalCount = count;
        Map<String, Set<String>> pairCopy = new LinkedHashMap<>();
        Set<String> outers = new LinkedHashSet<>();
        for (Map.Entry<String, Set<String>> e : pairs.entrySet()) {
            pairCopy.put(e.getKey(), Collections.unmodifiableSet(new LinkedHashSet<>(e.getValue())));
            outers.addAll(e.getValue());
        }
        this.lazyPairs = Collections.unmodifiableMap(pairCopy);
        this.pairedOuters = Collections.unmodifiableSet(outers);
        this.concatCopy = Collections.unmodifiableMap(new LinkedHashMap<>(concatCopy));
        this.exactRecv = Collections.unmodifiableSet(new LinkedHashSet<>(exactRecv));
        this.mirror = Collections.unmodifiableMap(new LinkedHashMap<>(mirror));
        this.typeCheck = Collections.unmodifiableMap(new LinkedHashMap<>(typeCheck));
    }

    /** Type-check IC: the {@code TYPE_CHECK} line at {@code key} as "CAST|INST variant", or null (stock). */
    public String getTypeCheck(String key) {
        return typeCheck.get(key);
    }

    public Map<String, String> getTypeCheckSites() {
        return typeCheck;
    }

    /** The {@code MIRROR} line at {@code key} as "KIND rep,rep", or null (the invoke stays stock). */
    public String getMirror(String key) {
        return mirror.get(key);
    }

    public Map<String, String> getMirrorSites() {
        return mirror;
    }

    /** Whether the child proved the receiver of the supertype-declared invoke at {@code key} exactly {String}. */
    public boolean hasExactReceiver(String key) {
        return exactRecv.contains(key);
    }

    public Set<String> getExactReceiverSites() {
        return exactRecv;
    }

    /** The {@code CONCAT_COPY} shape (UNARY/BINARY) of the indy concat at {@code key}, or null (stock lowering). */
    public String getConcatCopyShape(String key) {
        return concatCopy.get(key);
    }

    public Map<String, String> getConcatCopy() {
        return concatCopy;
    }

    /**
     * Pairing contract (1): whether the LAZY_CONCAT site {@code innerKey} may be lowered lazily: every outer the child
     * paired it with has a lazy LAZY_CONCAT entry (an inner without pairs is unconstrained). Profile only.
     */
    public boolean pairedOutersLowered(String innerKey) {
        Set<String> outers = lazyPairs.get(innerKey);
        if (outers == null) {
            return true;
        }
        for (String outer : outers) {
            ProfileEntry e = getEntry(outer, OptimizationType.LAZY_CONCAT);
            if (e == null || !LazyConcatMint.isLazyVariant(e.getVariant())) {
                return false;
            }
        }
        return true;
    }

    /** KT precision, pairing contract (2): whether some inner's lazy lowering relies on {@code key} being lowered lazily. */
    public boolean isPairedOuter(String key) {
        return pairedOuters.contains(key);
    }

    public Map<String, Set<String>> getLazyPairs() {
        return lazyPairs;
    }

    public ProfileEntry getEntry(String sourceLocation) {
        Map<OptimizationType, ProfileEntry> inner = entriesBySource.get(sourceLocation);
        if (inner == null || inner.isEmpty()) {
            return null;
        }
        return inner.values().iterator().next();
    }

    public ProfileEntry getEntry(String sourceLocation, OptimizationType type) {
        Map<OptimizationType, ProfileEntry> inner = entriesBySource.get(sourceLocation);
        if (inner == null) {
            return null;
        }
        return inner.get(type);
    }

    public boolean hasEntry(String sourceLocation) {
        return entriesBySource.containsKey(sourceLocation);
    }

    public int getTotalCount() {
        return totalCount;
    }

    private volatile Boolean admitsNoRep;

    /**
     * Zero-admit images: true iff this profile names no representation: no creation decision
     * ({@code SINGLE_BYTE}/{@code STRING_VIEW}/{@code LAZY_CONCAT}), no {@code INLINE_CACHE} variant listing a rep (every
     * token after {@code KT:} is {@code UNKNOWN}/{@code EXACT_STRING}/{@code EXACT}/{@code UNPROVEN}), no
     * {@code EQUALS_MATRIX REDIRECT}, {@code CONCAT_COPY}, {@code LAZY_PAIR} or {@code MIRROR}. The parent then mints no
     * rep and may compile String as stock; the binding's afterAnalysis check fails the build otherwise.
     */
    public boolean admitsNoRep() {
        Boolean b = admitsNoRep;
        if (b == null) {
            b = computeAdmitsNoRep();
            admitsNoRep = b;
        }
        return b;
    }

    private boolean computeAdmitsNoRep() {
        if (!concatCopy.isEmpty() || !lazyPairs.isEmpty() || !mirror.isEmpty()) {
            return false;
        }
        for (Map<OptimizationType, ProfileEntry> inner : entriesBySource.values()) {
            for (ProfileEntry e : inner.values()) {
                switch (e.getType()) {
                    case SINGLE_BYTE, STRING_VIEW, LAZY_CONCAT:
                        return false;
                    case EQUALS_MATRIX:
                        if (EqualsMatrixHeuristic.VARIANT_REDIRECT.equals(e.getVariant())) {
                            return false;
                        }
                        break;
                    case INLINE_CACHE:
                        if (!repFreeVariant(e.getVariant())) {
                            return false;
                        }
                        break;
                    default:
                        return false; // an unknown type: not provably rep-free
                }
            }
        }
        return true;
    }

    static boolean repFreeVariant(String variant) {
        if (variant == null) {
            return true;
        }
        String v = variant.startsWith("KT:") ? variant.substring(3) : variant;
        for (String t : v.split(",")) {
            switch (t) {
                case "UNKNOWN", "EXACT_STRING", "EXACT", "UNPROVEN":
                    break;
                default:
                    return false;
            }
        }
        return true;
    }

    public Map<String, ProfileEntry> getAllEntries() {
        Map<String, ProfileEntry> flat = new LinkedHashMap<>();
        for (Map.Entry<String, Map<OptimizationType, ProfileEntry>> e : entriesBySource.entrySet()) {
            if (!e.getValue().isEmpty()) {
                flat.put(e.getKey(), e.getValue().values().iterator().next());
            }
        }
        return Collections.unmodifiableMap(flat);
    }
}