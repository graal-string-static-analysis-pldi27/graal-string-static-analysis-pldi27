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
import java.util.Set;

/**
 * The hand list of the stringy receiver terminals that may return or leak their receiver {@code this}. No listed body
 * is walked or IR-checked; at a terminal usage on the list the walk also continues at the call's result.
 * <p>
 * The list is also the source of the leak rule's JUnit ({@code HandListLeakWhitelistTest}): an entry marked as leaking
 * {@code this} other than by its return value must not be whitelisted by any representation whose runtime body for
 * that method is the inherited default body. Entries with {@code returnsThis == false} and a leak mark are listed for
 * the leak rule's domain only. The conservative leak marks ({@code intern()} STORE, {@code splitWithDelimiters}
 * IN_RETURNED_CONTAINER, {@code matches} VIA_MATCHER, {@code compareToIgnoreCase}/{@code equals}/
 * {@code offsetByCodePoints} AS_ARGUMENT) only constrain the whitelists.
 * <p>
 * The list describes the default String implementation; representation-derived results (StringView
 * {@code trim}/{@code strip*} views) are an open item. Signatures use the {@code SiteKeys.formatSignature} format.
 */
public final class StringTerminalHandList {

    private StringTerminalHandList() {
    }

    /** How a listed terminal may leak {@code this} other than as its return value. */
    enum Leak {
        /** Only the return value may be {@code this}. */
        NONE,
        /** Stored into the heap by the default body ({@code toLowerCase}/{@code toUpperCase}: special casing). */
        STORE,
        /** Held by a heap object the default body creates ({@code replaceAll}/{@code replaceFirst}: a Matcher). */
        VIA_MATCHER,
        /** Contained in the returned object ({@code split}: {@code {this}}; {@code describeConstable}). */
        IN_RETURNED_CONTAINER,
        /** Passed as an argument by the default body ({@code transform}: {@code f.apply(this)}; {@code formatted}). */
        AS_ARGUMENT
    }

    /** One entry: the resolved method, whether its result may be {@code this}, and its kind of leak otherwise. */
    record Entry(String declaringClass, String name, String signature, boolean returnsThis, Leak leak) {
        boolean isLeakMarked() {
            return leak != Leak.NONE;
        }
    }

    static final String STRING = "java.lang.String";

    /** The {@code String} entries (the return-this terminals plus the conservative leak-marked additions). */
    static final List<Entry> STRING_ENTRIES = List.of(
                    // returns this, no other leak
                    new Entry(STRING, "toString", "", true, Leak.NONE),
                    new Entry(STRING, "substring", "I", true, Leak.NONE),
                    new Entry(STRING, "substring", "I,I", true, Leak.NONE),
                    new Entry(STRING, "subSequence", "I,I", true, Leak.NONE),
                    new Entry(STRING, "concat", "Ljava/lang/String;", true, Leak.NONE),
                    new Entry(STRING, "replace", "C,C", true, Leak.NONE),
                    new Entry(STRING, "replace", "Ljava/lang/CharSequence;,Ljava/lang/CharSequence;", true, Leak.NONE),
                    new Entry(STRING, "trim", "", true, Leak.NONE),
                    new Entry(STRING, "strip", "", true, Leak.NONE),
                    new Entry(STRING, "stripLeading", "", true, Leak.NONE),
                    new Entry(STRING, "stripTrailing", "", true, Leak.NONE),
                    new Entry(STRING, "repeat", "I", true, Leak.NONE),
                    // conservative: SVM's intern substitute stores this in the global intern table
                    // (StringInternSupport putIfAbsent(result, result))
                    new Entry(STRING, "intern", "", true, Leak.STORE),
                    new Entry(STRING, "resolveConstantDesc", "Ljava/lang/invoke/MethodHandles$Lookup;", true, Leak.NONE),
                    // returns this (StringLatin1/UTF16.to*Case(this, ...) returns str) and leaks by a store
                    new Entry(STRING, "toLowerCase", "", true, Leak.STORE),
                    new Entry(STRING, "toLowerCase", "Ljava/util/Locale;", true, Leak.STORE),
                    new Entry(STRING, "toUpperCase", "", true, Leak.STORE),
                    new Entry(STRING, "toUpperCase", "Ljava/util/Locale;", true, Leak.STORE),
                    // returns this through the heap (text.toString()) and leaks via a Matcher
                    new Entry(STRING, "replaceAll", "Ljava/lang/String;,Ljava/lang/String;", true, Leak.VIA_MATCHER),
                    new Entry(STRING, "replaceFirst", "Ljava/lang/String;,Ljava/lang/String;", true, Leak.VIA_MATCHER),
                    // this inside the returned container
                    new Entry(STRING, "split", "Ljava/lang/String;", false, Leak.IN_RETURNED_CONTAINER),
                    new Entry(STRING, "split", "Ljava/lang/String;,I", false, Leak.IN_RETURNED_CONTAINER),
                    new Entry(STRING, "describeConstable", "", false, Leak.IN_RETURNED_CONTAINER),
                    // conservative addition: split(regex, limit, true) may return {this}
                    new Entry(STRING, "splitWithDelimiters", "Ljava/lang/String;,I", false, Leak.IN_RETURNED_CONTAINER),
                    // this as an argument
                    new Entry(STRING, "transform", "Ljava/util/function/Function;", false, Leak.AS_ARGUMENT),
                    new Entry(STRING, "formatted", "[Ljava/lang/Object;", false, Leak.AS_ARGUMENT),
                    // conservative, leak rule's domain only: Pattern.matches(regex, this) (a Matcher holds this);
                    // CASE_INSENSITIVE_ORDER.compare(this, str); the deflection anObject.equals(this);
                    // Character.offsetByCodePoints(this, ...)
                    new Entry(STRING, "matches", "Ljava/lang/String;", false, Leak.VIA_MATCHER),
                    new Entry(STRING, "compareToIgnoreCase", "Ljava/lang/String;", false, Leak.AS_ARGUMENT),
                    new Entry(STRING, "equals", "Ljava/lang/Object;", false, Leak.AS_ARGUMENT),
                    new Entry(STRING, "offsetByCodePoints", "I,I", false, Leak.AS_ARGUMENT));

    /**
     * The builder row: on these types every method returning {@code this} ({@code append*}, {@code insert*},
     * {@code delete*}, {@code replace}, {@code reverse}, {@code appendCodePoint}) is on the list, with no other leak.
     */
    static final Set<String> BUILDER_TYPES = AccumulatorWhitelist.withJoiner(Set.of(
                    "java.lang.AbstractStringBuilder", "java.lang.StringBuilder", "java.lang.StringBuffer", "java.io.StringWriter"));

    /**
     * Flat delivery: the leak-marked entries whose default body hands {@code this} to code the walk treats as ordinary:
     * an argument of a walked callee ({@code transform}: {@code f.apply(this)}; {@code formatted}:
     * {@code Formatter.format(this, ..)}; {@code offsetByCodePoints}: {@code Character.offsetByCodePoints(this, ..)};
     * {@code matches}/{@code replaceAll}/{@code replaceFirst}: a {@code Matcher} over {@code this}; the case mappings:
     * {@code StringLatin1/UTF16.to*Case(this, ..)}), or the content of a returned container ({@code describeConstable}:
     * {@code Optional.of(this)}; {@code split}/{@code splitWithDelimiters}: {@code {this}}). A value-carrying rep inherits
     * these bodies (a value-null rep is rejected at them: none whitelists a leak-marked default body), so for an atom
     * that may become one (an SB seed) the walk enters the body at the terminal (RecursiveTracking.flatHandOffEnters) and
     * tags the downstream sites. A member the SB rep declares itself (the case mappings and {@code offsetByCodePoints},
     * whose bodies never hand {@code this} on) is not entered for an SB seed ({@code RecursiveTracking.sbsDeclares}).
     * Not here: {@code intern} (rejects SINGLE_BYTE outright), {@code equals} (the deflection runs a rep's own body) and
     * {@code compareToIgnoreCase} ({@code String$CaseInsensitiveComparator}, a terminal body).
     */
    static final Set<String> FLAT_HANDOFF_NAMES = Set.of("transform", "formatted", "describeConstable", "split", "splitWithDelimiters", "matches",
                    "replaceAll", "replaceFirst", "offsetByCodePoints", "toLowerCase", "toUpperCase");

    /**
     * The private String helpers the public split entries delegate to ({@code split(regex, limit, withDelimiters)} and
     * its one-char fast path, whose no-match case returns {@code {this}}): a call on {@code this} inside an entered split
     * body is a terminal again, so they are hand-offs too.
     */
    static final Set<String> FLAT_HANDOFF_PRIVATE = Set.of("split(Ljava/lang/String;,I,Z)", "split(C,I,Z)");

    /** Whether the String method (declaring class, name, usage-site signature) is a flat hand-off ({@link #FLAT_HANDOFF_NAMES}). */
    static boolean isFlatHandOff(String declaringClass, String name, String signature) {
        if (STRING.equals(declaringClass) && FLAT_HANDOFF_PRIVATE.contains(name + "(" + signature + ")")) {
            return true;
        }
        Entry e = StringAtoms.handEntry(declaringClass, name, signature);
        return e != null && e.declaringClass().equals(STRING) && e.isLeakMarked() && FLAT_HANDOFF_NAMES.contains(e.name());
    }

    /** The leak-marked entries: the domain of the leak rule. */
    static List<Entry> leakMarked() {
        return STRING_ENTRIES.stream().filter(Entry::isLeakMarked).toList();
    }
}
