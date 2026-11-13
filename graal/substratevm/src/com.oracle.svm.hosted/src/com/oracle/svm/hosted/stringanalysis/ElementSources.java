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
import java.util.Map;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import com.oracle.svm.core.stringrep.ElementSourceFactory;

/**
 * The element-source API table. Each row is an exact {@code (declaringClass, name, Phase-A signature)} of a JDK method
 * whose result is a fresh container whose elements are substrings of the input: a {@code Stream<String>} (member
 * {@code <elem>} of the fresh stream head) or a {@code String[]} (member {@code []}). {@code Pattern} and {@code String}
 * are final, so the user call's target is exact. A call to a row in user code is an {@code ELEM} STRING seed whose atom
 * is placed as the container's element ({@code RecursiveTracking.mintElementString}), judged by the String View check;
 * the parent replaces an admitted call with the row's {@link ElementSourceFactory} method (the JDK algorithm with the
 * pieces as views).
 */
final class ElementSources {

    private ElementSources() {
    }

    /** The container kind of a row. */
    enum Kind {
        /** A {@code Stream<String>}: the fresh {@code ReferencePipeline$Head}, member {@code <elem>}. */
        STREAM,
        /** A {@code String[]}: a fresh array, member {@code []}. */
        ARRAY
    }

    static final String PATTERN_CLASS = "java.util.regex.Pattern";
    static final String STRING_CLASS = "java.lang.String";
    static final String CS = "Ljava/lang/CharSequence;";
    static final String STR = "Ljava/lang/String;";

    /** The rows as {@code decl#name(sig)} -> kind. */
    static final Map<String, Kind> ROWS = Map.of(
                    PATTERN_CLASS + "#splitAsStream(" + CS + ")", Kind.STREAM,
                    STRING_CLASS + "#lines()", Kind.STREAM,
                    PATTERN_CLASS + "#split(" + CS + ")", Kind.ARRAY,
                    PATTERN_CLASS + "#split(" + CS + ",I)", Kind.ARRAY,
                    PATTERN_CLASS + "#splitWithDelimiters(" + CS + ",I)", Kind.ARRAY,
                    STRING_CLASS + "#split(" + STR + ")", Kind.ARRAY,
                    STRING_CLASS + "#split(" + STR + ",I)", Kind.ARRAY,
                    STRING_CLASS + "#splitWithDelimiters(" + STR + ",I)", Kind.ARRAY);

    /** The profile variant of an admitted row whose pieces are not stored (the parent lowers {@code StringView.create}). */
    static final String ELEMENT_VIEW = "ELEMENT_VIEW";
    /** The profile variant of an admitted row whose pieces are stored (the parent lowers {@code StringView.createStored}). */
    static final String ELEMENT_VIEW_STORED = "ELEMENT_VIEW_STORED";

    /** The method names of the rows (Phase A makes a call vertex for a row only if its name passes the name filter). */
    static final java.util.Set<String> ROW_NAMES = ROWS.keySet().stream().map(r -> r.substring(r.indexOf('#') + 1, r.indexOf('('))).collect(java.util.stream.Collectors.toUnmodifiableSet());

    static boolean isRowName(String name) {
        return ROW_NAMES.contains(name);
    }

    /** The row's kind, or null when {@code (decl, name, sig)} is not a row (independent of the knob). */
    static Kind kindOf(String decl, String name, String sig) {
        return decl == null || name == null || sig == null ? null : ROWS.get(decl + "#" + name + "(" + sig + ")");
    }

    static boolean isSource(String decl, String name, String sig) {
        return kindOf(decl, name, sig) != null;
    }

    /** Whether {@code v} is a user-code call vertex (STRING_METHOD_CALL) of a row. */
    static boolean isSource(SugVertex v) {
        return v != null && v.getNodeType() == SugNodeType.STRING_METHOD_CALL && isSource(v.getDeclaringClass(), v.getMethodName(), v.getMethodSignature());
    }

    static boolean isElementVariant(String variant) {
        return ELEMENT_VIEW.equals(variant) || ELEMENT_VIEW_STORED.equals(variant);
    }

    /** Pure (pinned by JUnit): the variant of an admitted row: stored pieces take the half-occupancy rule. */
    static String variant(boolean stored) {
        return stored ? ELEMENT_VIEW_STORED : ELEMENT_VIEW;
    }

    /**
     * The row's factory: a static method of {@link ElementSourceFactory} whose parameters are the call's (receiver
     * first) plus a trailing {@code boolean stored}; null when not a row.
     */
    static Method factoryMethod(String decl, String name, String sig) throws NoSuchMethodException {
        Kind k = kindOf(decl, name, sig);
        if (k == null) {
            return null;
        }
        Class<?> f = ElementSourceFactory.class;
        boolean pattern = PATTERN_CLASS.equals(decl);
        boolean limit = sig.endsWith(",I");
        return switch (name) {
            case "splitAsStream" -> f.getDeclaredMethod("splitAsStream", Pattern.class, CharSequence.class, boolean.class);
            case "lines" -> f.getDeclaredMethod("lines", String.class, boolean.class);
            case "split" -> pattern
                            ? (limit ? f.getDeclaredMethod("patternSplit", Pattern.class, CharSequence.class, int.class, boolean.class)
                                            : f.getDeclaredMethod("patternSplit", Pattern.class, CharSequence.class, boolean.class))
                            : (limit ? f.getDeclaredMethod("stringSplit", String.class, String.class, int.class, boolean.class)
                                            : f.getDeclaredMethod("stringSplit", String.class, String.class, boolean.class));
            case "splitWithDelimiters" -> pattern
                            ? f.getDeclaredMethod("patternSplitWithDelimiters", Pattern.class, CharSequence.class, int.class, boolean.class)
                            : f.getDeclaredMethod("stringSplitWithDelimiters", String.class, String.class, int.class, boolean.class);
            default -> null;
        };
    }

    /** The factory's declared result type matches the row's container (a JUnit premise). */
    static Class<?> containerClass(Kind k) {
        return k == Kind.STREAM ? Stream.class : String[].class;
    }
}
