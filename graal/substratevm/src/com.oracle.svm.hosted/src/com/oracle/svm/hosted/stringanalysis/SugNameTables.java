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

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;

/**
 * The name/classifier constant tables of the SUG builder, extracted verbatim from {@link SugBuilderV2}.
 */
final class SugNameTables {
    static final Set<String> STRINGY_ALLOC_TYPES = AccumulatorWhitelist.withJoiner(Set.of(
                    "java.lang.String",
                    "java.lang.StringBuilder",
                    "java.lang.StringBuffer",
                    "java.io.StringWriter",
                    "java.lang.AbstractStringBuilder"));

    static final Set<String> STRINGY_INVOKE_RECEIVERS = AccumulatorWhitelist.withJoiner(Set.of(
                    "java.lang.String",
                    "java.lang.StringBuilder",
                    "java.lang.StringBuffer",
                    "java.io.StringWriter",
                    "java.lang.invoke.StringConcatFactory"));

    static final Set<String> ACCUMULATOR_RECEIVERS = AccumulatorWhitelist.withJoiner(Set.of(
                    "java.lang.StringBuilder",
                    "java.lang.StringBuffer",
                    "java.io.StringWriter",
                    "java.lang.AbstractStringBuilder"));

    static final Set<String> STRINGY_REP_TYPES = Set.of(
                    "com.oracle.svm.core.stringrep.StringView",
                    "com.oracle.svm.core.stringrep.SingleByteString",
                    "com.oracle.svm.core.stringrep.TrivialString",
                    "com.oracle.svm.core.stringrep.RopeString",
                    "com.oracle.svm.core.stringrep.ArrayLazyString",
                    "com.oracle.svm.core.stringrep.InterleavedStringArray",
                    "com.oracle.svm.core.stringrep.ThreeWayString",
                    "com.oracle.svm.core.stringrep.FixedConcat4");

    static final Set<String> CONCAT_INVOKE_NAMES = Set.of(
                    "makeConcat", "makeConcatWithConstants");

    /**
     * The recording feed: every invoke on a traced stringy value whose name is here gets a usage site and is recorded;
     * the whitelist verdict at emit is the only filter. Soundness requires recorded ⊇ every non-whitelisted stringy
     * method (a non-whitelisted call that is never recorded is a silent-admit leak, e.g. a missing {@code coder()}).
     * Hence the table includes {@code equalsIgnoreCase}/{@code matches}/{@code regionMatches} (not whitelisted) and the
     * strict-class-check family {@code getClass}/{@code isInstance}/{@code cast}: getClass is whitelisted for no rep,
     * so a live-arm class check rejects through the ordinary verdict (a dead-arm one is skipped). Identity ops
     * ({@code wait}/{@code notify}/{@code notifyAll}) stay out: identity behaviour is invariant under complete
     * substitution.
     */
    static final Set<String> STRINGY_METHOD_NAMES = withIcMemberNames(Set.of(
                    "intern", "equals",
                    "makeConcat", "makeConcatWithConstants",
                    "substring", "subSequence", "valueOf", "charAt", "length",
                    "hashCode", "compareTo", "compareToIgnoreCase", "concat",
                    "toString", "append", "insert", "replace", "replaceAll",
                    "replaceFirst", "trim", "strip", "stripLeading", "stripTrailing",
                    "toLowerCase", "toUpperCase", "toCharArray", "getBytes",
                    "isEmpty", "isBlank", "split", "startsWith", "endsWith",
                    "contains", "indexOf", "lastIndexOf", "format", "join",
                    "codePointAt", "codePointBefore", "codePointCount",
                    "offsetByCodePoints", "getChars", "repeat", "chars",
                    "codePoints", "lines", "indent", "translateEscapes",
                    "describeConstable", "resolveConstantDesc", "transform",
                    "copyValueOf", "newString", "clone", "ensureCapacity",
                    "capacity", "setLength", "setCharAt", "flush", "close",
                    "write", "getBuffer",
                    "getBytesNoRepl", "getBytesUTF8NoRepl", "countNonZeroAscii",
                    "coder", "isLatin1", "contentEquals", "equalsIgnoreCase",
                    "matches", "regionMatches",
                    "getClass", "isInstance", "cast"));

    /**
     * Every name of the inline cache's method set ({@link StringIcMethods}) also gets a Phase-A vertex, so an IC member
     * never lacks the vertex its profile entry is keyed on. The verdict does not depend on it: receiver usages are
     * recorded by declaring type with or without a vertex ({@code RecursiveTracking.stringTerminal}).
     */
    private static Set<String> withIcMemberNames(Set<String> base) {
        Set<String> all = new HashSet<>(base);
        for (String d : StringIcMethods.descriptors()) {
            all.add(d.substring(0, d.indexOf('(')));
        }
        return Set.copyOf(all);
    }

    static final String STRING_INTERN_SUPPORT_CLASS = "com.oracle.svm.core.jdk.StringInternSupport";

    /**
     * The usage names of a raw {@code String.value}/{@code String.coder} field read on a walked value (a
     * {@code JDK_LIBRARY_CALL} site declared by String; the parentheses avoid any collision with a method name).
     * {@code value(raw)} is whitelisted by no rep (every rep except SingleByteString keeps {@code value == null};
     * SINGLE_BYTE validates no usage list); {@code coder(raw)} wherever {@code coder()} is (a rep's inherited coder
     * field equals its {@code coder()} answer).
     */
    static final String RAW_VALUE_USAGE = "value(raw)";
    static final String RAW_CODER_USAGE = "coder(raw)";

    /**
     * The raw-read usage name for a String instance field, or {@code null} when a raw read is not a usage.
     * {@code hash}/{@code hashIsZero} are not usages: every rep keeps the String hash-cache protocol on them (the "not
     * computed" pair {@code (0, false)} set by {@code String(byte)}, the true content hash cached by the rep's own
     * {@code hashCode}, or, for SingleByteString, the real String's pair copied by {@code String(String)}), and the only
     * non-receiver reader, {@code String(String original)}, copies the pair as a cache.
     */
    static String rawStringFieldUsageName(String fieldName) {
        if ("value".equals(fieldName)) {
            return RAW_VALUE_USAGE;
        }
        if ("coder".equals(fieldName)) {
            return RAW_CODER_USAGE;
        }
        return null;
    }

    /**
     * The strict-class-check family: operations that observe the runtime class of the traced value, the substitution
     * contract's single behavioural exception. Shapes: (a) the intrinsified {@code GetClassNode} (a CLASS_CHECK
     * vertex); (b) the {@code Object.getClass} invoke (final on Object, so the declared class is always Object);
     * (c) {@code Class.isInstance(x)} / {@code Class.cast(x)} with the value as the argument. Consumers of the
     * getClass result and class-mirror {@code ==} compares are covered by (a)/(b). {@code instanceof} is not in the
     * family (rep-invariant: reps are Strings).
     */
    static boolean isStrictClassCheckName(String methodName, String declaringClass) {
        if (methodName == null || declaringClass == null) {
            return false;
        }
        if (methodName.equals("getClass")) {
            return declaringClass.equals("java.lang.Object") || declaringClass.equals("java.lang.String");
        }
        return (methodName.equals("isInstance") || methodName.equals("cast")) && declaringClass.equals("java.lang.Class");
    }

    static final Set<String> HASH_CONTAINER_CLASSES = Set.of(
                    "java.util.HashMap",
                    "java.util.LinkedHashMap",
                    "java.util.HashSet",
                    "java.util.LinkedHashSet",
                    "java.util.concurrent.ConcurrentHashMap",
                    "java.util.Hashtable",
                    "java.util.WeakHashMap");

    static final Set<String> MAP_LOOKUP_CLASSES = Set.of(
                    "java.util.HashMap",
                    "java.util.LinkedHashMap",
                    "java.util.concurrent.ConcurrentHashMap",
                    "java.util.Hashtable",
                    "java.util.WeakHashMap",
                    "java.util.Map",
                    "java.util.concurrent.ConcurrentMap");

    static final Set<String> HASH_CONTAINER_KEY_METHODS = Set.of(
                    "put", "putIfAbsent",
                    "get", "getOrDefault", "containsKey", "contains", "remove",
                    "add");

    static final Set<String> HASH_CONTAINER_STORING_METHODS = Set.of(
                    "put", "putIfAbsent", "add");

    static final Set<String> HASH_SET_CONTAINS_CLASSES = Set.of(
                    "java.util.HashSet",
                    "java.util.LinkedHashSet");

    static final Set<String> CONTAINER_DERIVED_VIEW_METHODS = Set.of(
                    "entrySet", "keySet", "values");

    static final Set<String> ENTRY_ACCESSOR_METHODS = Set.of(
                    "getKey", "getValue");

    static boolean isKeyParamIndex(String methodName, int paramIdx) {
        return switch (methodName) {
            case "put", "putIfAbsent", "get", "getOrDefault", "containsKey", "contains", "remove", "add" -> paramIdx == 1;
            default -> false;
        };
    }

    /**
     * Can a value of declared type {@code t} be a stringy value, in the closed world? ({@link SugBuilderV2#canHoldStringy}
     * delegates here.) {@code null} conservatively holds. A type holds iff some stringy type is a subtype of it: the
     * holder set is {@code stringy ∪ supertypes(stringy)}, the stringy runtime types being the subtype closure of
     * {@link #STRINGY_ALLOC_TYPES} ∪ {@link #STRINGY_REP_TYPES}. A String value reaches a slot of declared type
     * {@code t} iff {@code t} is a supertype of some stringy type, so finality is irrelevant and a type with no stringy
     * subtype is never a holder (e.g. {@code Function} as a {@code computeIfAbsent} mapping function). Arrays never hold
     * (an array is an element-keyed container).
     *
     * <p>The holder set is computed once per universe, at first use: every consumer runs post-fixpoint, so every type
     * carrying a stringy value's state is already registered; types looked up later carry no states and cannot hold
     * stringy values (sound to freeze). The set is order-independent.</p>
     */
    static boolean canHoldStringy(AnalysisType t) {
        if (t == null) {
            return true;
        }
        if (t.isArray()) {
            return false;
        }
        return holderNames(t.getUniverse()).contains(t.toJavaName(true));
    }

    /** Per-universe holder-name sets (identity keys; one universe per image build). */
    private static final Map<AnalysisUniverse, Set<String>> STRINGY_HOLDER_NAMES = new ConcurrentHashMap<>();

    private static Set<String> holderNames(AnalysisUniverse universe) {
        return STRINGY_HOLDER_NAMES.computeIfAbsent(universe, u -> {
            List<AnalysisType> snapshot = new ArrayList<>(u.getTypes());
            snapshot.sort(Comparator.comparingInt(AnalysisType::getId));
            Set<String> holders = new HashSet<>();
            for (AnalysisType type : snapshot) {
                if (!type.isArray() && isStringyRuntimeType(type)) {
                    markHolderClosure(type, holders);
                }
            }
            return holders;
        });
    }

    /**
     * Does {@code t}'s transitive ancestor chain (self, superclasses, interfaces) contain a base-set member? Unlike the
     * exact-name alloc classifiers, this includes subtypes.
     */
    private static boolean isStringyRuntimeType(AnalysisType t) {
        return chainHasBase(t, new HashSet<>());
    }

    private static boolean chainHasBase(AnalysisType t, Set<AnalysisType> visited) {
        if (t == null || !visited.add(t)) {
            return false;
        }
        if (STRINGY_ALLOC_TYPES.contains(t.toJavaName(true)) || STRINGY_REP_TYPES.contains(t.toJavaName(true))) {
            return true;
        }
        if (chainHasBase(t.getSuperclass(), visited)) {
            return true;
        }
        for (AnalysisType interf : t.getInterfaces()) {
            if (chainHasBase(interf, visited)) {
                return true;
            }
        }
        return false;
    }

    /** Mark {@code t} and its full ancestor closure as holders (supertypes of stringy). */
    private static void markHolderClosure(AnalysisType t, Set<String> holders) {
        if (t == null || !holders.add(t.toJavaName(true))) {
            return;
        }
        markHolderClosure(t.getSuperclass(), holders);
        for (AnalysisType interf : t.getInterfaces()) {
            markHolderClosure(interf, holders);
        }
    }

}
