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

import java.util.Set;

public final class AccumulatorWhitelist {

    static final Set<String> W_ACCUMULATOR = Set.of(
                    "append", "capacity", "charAt", "codePointAt", "codePointBefore",
                    "codePointCount", "ensureCapacity", "getChars", "length",
                    "offsetByCodePoints", "toString", "substring", "subSequence",
                    "flush", "close");

    static final Set<String> M_TARGET = Set.of("toString", "substring", "subSequence");

    /*
     * java.util.StringJoiner is a fourth accumulator kind: a stack-confined admitted extraction is lowered to an
     * interleaved string over the joiner's array (a stored one stays stock). Declared here, in a class with no static
     * dependencies, because other classes' name tables read it in their static initializers.
     */

    /** The joiner accumulator class (the table entry, as the builders and the writer are listed). */
    static final String JOINER = "java.util.StringJoiner";

    /** {@code base} plus {@link #JOINER}. */
    static Set<String> withJoiner(Set<String> base) {
        java.util.Set<String> s = new java.util.HashSet<>(base);
        s.add(JOINER);
        return Set.copyOf(s);
    }

    static final Set<String> ACCUMULATOR_TYPES = withJoiner(Set.of(
                    "java.lang.StringBuilder",
                    "java.lang.StringBuffer",
                    "java.io.StringWriter",
                    "java.lang.AbstractStringBuilder"));

    static boolean isAccumulatorType(String declaringClass) {
        return declaringClass != null && ACCUMULATOR_TYPES.contains(declaringClass);
    }

    static boolean isWhitelisted(String methodName) {
        return methodName != null && W_ACCUMULATOR.contains(methodName);
    }

    static boolean isExtraction(String methodName) {
        return methodName != null && M_TARGET.contains(methodName);
    }

    // ------------------------------------------------------------------
    // The only-growing decision table of pass 1 (W_accumulator).
    // ------------------------------------------------------------------
    /** The builder classes whose methods the table judges (the declaring classes of a builder atom's terminal usages). */
    static final Set<String> BUILDER_DECLARING = Set.of("java.lang.AbstractStringBuilder", "java.lang.StringBuilder", "java.lang.StringBuffer");

    /*
     * Every public method of AbstractStringBuilder / StringBuilder / StringBuffer (JDK 25) is classified by name into
     * exactly one of the three sets below; AccumulatorDecisionTableTest enumerates the classes by reflection, so a new JDK
     * method fails the test until it is classified here. No GROWING or READ_ONLY method writes below count
     * (AbstractStringBuilder.java).
     */
    /**
     * Only growing / content-preserving: {@code append*}, {@code appendCodePoint} (= {@code append(char)} /
     * {@code append(char[])}, :1055) and both {@code repeat} (:2085, :2129, :2166: write from {@code count} on, after
     * {@code ensureCapacityNewCoder}) write at {@code count}, reallocating or inflating into a new array;
     * {@code ensureCapacity} and {@code trimToSize} (:358, {@code Arrays.copyOf}) replace the array by a copy and leave
     * the old one intact; the constructors initialise an empty object.
     */
    static final Set<String> GROWING_METHODS = Set.of("<init>", "append", "appendCodePoint", "repeat", "ensureCapacity", "trimToSize");

    /**
     * Read-only queries ({@code chars}/{@code codePoints} (:1752/:1776) capture {@code this} and read the fields when the
     * stream runs: reads only).
     */
    static final Set<String> READ_ONLY_METHODS = Set.of("capacity", "charAt", "chars", "codePointAt", "codePointBefore", "codePointCount",
                    "codePoints", "compareTo", "getChars", "indexOf", "lastIndexOf", "length", "offsetByCodePoints", "subSequence", "substring",
                    "toString");

    /** Rewrite content below {@code count} in place (or shrink {@code count}): REJECT. */
    static final Set<String> MUTATING_METHODS = Set.of("delete", "deleteCharAt", "insert", "replace", "reverse", "setCharAt", "setLength");

    /** The pass-1 whitelist: growing or read-only. Everything else on a builder (incl. internal methods, field reads) rejects. */
    static final Set<String> W_GROW;

    static {
        java.util.Set<String> w = new java.util.HashSet<>(GROWING_METHODS);
        w.addAll(READ_ONLY_METHODS);
        W_GROW = java.util.Set.copyOf(w);
    }

    /** The growing methods that return {@code this} (receiver proof: their result is the builder). */
    static final Set<String> RETURNS_THIS = Set.of("append", "appendCodePoint", "repeat");

    /** The non-builder sites a builder atom may be used at without touching its content (role RECEIVER). */
    static final Set<String> OBJECT_READS = Set.of("getClass", "equals", "hashCode");

    /*
     * java.io.StringWriter as an accumulator kind. A writer wraps a private, final StringBuffer buf
     * (allocated by its constructor, never reassigned). Every public method StringWriter declares (JDK 25; pinned by
     * StringWriterAccumulatorTest):
     *   <init>(), <init>(int)              allocate buf (Writer.<init>(Object) only sets lock = buf)        GROWING
     *   write(int|char[],int,int|String|String,int,int), append(CharSequence|CharSequence,int,int|char)
     *                                      buf.append(...) only (append = write + return this)             GROWING
     *   flush(), close()                   empty bodies                                                     GROWING (no-op)
     *   toString()                         buf.toString(): a copy                                           READ_ONLY (the extraction)
     *   getBuffer()                        hands out buf (mutable: setLength/insert/delete reach it)        REJECT
     * Inherited Writer methods (write(char[]); nullWriter is static) are entered by the walk: their this.write(cbuf, 0,
     * len) is a StringWriter usage. The protected Writer.lock (= buf) is a field: a raw field usage is REJECT.
     */
    /** The declaring class of the writer accumulator's own methods. */
    static final Set<String> WRITER_DECLARING = Set.of("java.io.StringWriter");

    /** StringWriter's growing / no-op methods (each body is {@code buf.append(...)}, a constructor, or empty). */
    static final Set<String> WRITER_GROWING_METHODS = Set.of("<init>", "write", "append", "flush", "close");

    /** StringWriter's read-only methods: {@code toString} copies the buffer. */
    static final Set<String> WRITER_READ_ONLY_METHODS = Set.of("toString");

    /** StringWriter's escaping methods: {@code getBuffer} hands out the mutable buffer. */
    static final Set<String> WRITER_ESCAPING_METHODS = Set.of("getBuffer");

    /** The writer pass-1 whitelist (growing or read-only); everything else declared by StringWriter rejects. */
    static final Set<String> W_GROW_WRITER;

    static {
        java.util.Set<String> w = new java.util.HashSet<>(WRITER_GROWING_METHODS);
        w.addAll(WRITER_READ_ONLY_METHODS);
        W_GROW_WRITER = java.util.Set.copyOf(w);
    }

    /*
     * java.util.StringJoiner (JDK 25, final). Every public method it declares (pinned by
     * StringJoinerAccumulatorTest):
     *   <init>(CharSequence), <init>(CharSequence,CharSequence,CharSequence)  snapshot the affixes/delimiter   GROWING
     *   add(CharSequence)          writes elts[size++] or Arrays.copyOf into a NEW array; return this        GROWING
     *   merge(StringJoiner) as the RECEIVER   = add(other.elts[0]); return this                              GROWING
     *   setEmptyValue(CharSequence)           sets emptyValue only (a later size-0 toString); return this    GROWING
     *   toString(), length()                  read only (toString = JLA.join(...), the extraction)           READ_ONLY
     * Being the argument of merge runs other.compactElts(): elts[0] = join, Arrays.fill(elts, 1, sz, null), size = 1,
     * an in-place rewrite of elts[0, size): MUTATING. The row rejects every non-RECEIVER use of a joiner-declared method,
     * and a walk entering merge at its argument meets the private compactElts (REJECT) and raw field reads.
     */
    /** The declaring class of the joiner accumulator's own methods. */
    static final Set<String> JOINER_DECLARING = Set.of(JOINER);

    /** StringJoiner's growing / content-preserving methods (as a RECEIVER). */
    static final Set<String> JOINER_GROWING_METHODS = Set.of("<init>", "add", "merge", "setEmptyValue");

    /** StringJoiner's read-only methods. */
    static final Set<String> JOINER_READ_ONLY_METHODS = Set.of("toString", "length");

    /** The joiner methods whose result is the receiver ({@code return this}). */
    static final Set<String> JOINER_RETURNS_THIS = Set.of("add", "merge", "setEmptyValue");

    /** The joiner pass-1 whitelist (growing or read-only, as a RECEIVER); everything else declared by StringJoiner rejects. */
    static final Set<String> W_GROW_JOINER;

    static {
        java.util.Set<String> w = new java.util.HashSet<>(JOINER_GROWING_METHODS);
        w.addAll(JOINER_READ_ONLY_METHODS);
        W_GROW_JOINER = java.util.Set.copyOf(w);
    }

    /** The receiver proof's {@code return this} rule: a growing method whose result is the receiver accumulator. */
    static boolean returnsThis(String declaringClass, String methodName) {
        if (declaringClass == null || methodName == null) {
            return false;
        }
        if (BUILDER_DECLARING.contains(declaringClass)) {
            return RETURNS_THIS.contains(methodName);
        }
        if (JOINER_DECLARING.contains(declaringClass)) {
            return JOINER_RETURNS_THIS.contains(methodName); // add/merge/setEmptyValue return this
        }
        return WRITER_DECLARING.contains(declaringClass) && "append".equals(methodName); // StringWriter.append: return this
    }

    enum AccRow {
        /** A whitelisted builder method: the builder stays only growing. */
        GROWING,
        /** A use that cannot touch the builder's content (a terminal argument, a class check, an identity read, a concat operand). */
        READ,
        /** Anything else: a mutating or unvetted builder method, a raw field read of the builder, an unknown use. */
        REJECT
    }

    /**
     * The pure decision row of one usage of a builder atom (pinned by {@code AccumulatorDecisionTableTest}). A field usage of
     * the builder (a raw {@code value}/{@code count}/{@code coder} read by JDK code holding it as an argument) is a
     * builder-declared {@code field:} name, i.e. not in {@link #W_GROW}: REJECT (the read array is not tracked).
     */
    static AccRow accumulatorUsageRow(String declaringClass, String methodName, UsageRole role) {
        if (declaringClass != null && BUILDER_DECLARING.contains(declaringClass)) {
            return methodName != null && W_GROW.contains(methodName) && role == UsageRole.RECEIVER ? AccRow.GROWING : AccRow.REJECT;
        }
        if (declaringClass != null && WRITER_DECLARING.contains(declaringClass)) {
            return methodName != null && W_GROW_WRITER.contains(methodName) && role == UsageRole.RECEIVER ? AccRow.GROWING : AccRow.REJECT;
        }
        if (declaringClass != null && JOINER_DECLARING.contains(declaringClass)) {
            // Only as the RECEIVER; the merge argument (role PARAMETER) is the in-place rewrite: REJECT
            return methodName != null && W_GROW_JOINER.contains(methodName) && role == UsageRole.RECEIVER ? AccRow.GROWING : AccRow.REJECT;
        }
        if (role == UsageRole.PARAMETER || role == UsageRole.NONE) {
            return AccRow.READ; // the terminal-argument rules (equals/compareTo/Blackhole) and the concat operand: the body is not run on the builder
        }
        if (role == UsageRole.RECEIVER && methodName != null && OBJECT_READS.contains(methodName) &&
                        ("java.lang.Object".equals(declaringClass) || "java.lang.String".equals(declaringClass))) {
            // the class-check site (Object.getClass) and Object.equals/hashCode (Phase A labels a virtual Object.equals as
            // String.equals): identity reads, never the content
            return AccRow.READ;
        }
        return AccRow.REJECT;
    }

    // ------------------------------------------------------------------
    // Dispatch-owner rule: a call whose receiver is the tracked accumulator is classified as the accumulator's own
    // method, whatever the declared owner of the call.
    // ------------------------------------------------------------------

    /** The classes whose methods the accumulator tables name (a site declared by one of them names the target's own method). */
    static boolean isTableDeclaring(String declaringClass) {
        return declaringClass != null && (BUILDER_DECLARING.contains(declaringClass) || WRITER_DECLARING.contains(declaringClass) ||
                        JOINER_DECLARING.contains(declaringClass));
    }

    /**
     * The dispatched owner of a RECEIVER call on a tracked accumulator (pure; pinned by {@code AccumulatorDispatchTest}): null
     * when the site already names a table class ({@link #isTableDeclaring}: the declared method is the target's own method
     * family); else the declaring class of the declaration that {@code invokevirtual}/
     * {@code invokeinterface} of {@code declared} selects for a receiver of class {@code exact}
     * ({@link TerminalBodyKinds#selectedDeclaration}, JVMS 5.4.6); a method no class of {@code exact} declares (e.g. an
     * interface default method) is named by {@code declared}'s own class, which no table admits (REJECT).
     *
     * <p>A RECEIVER usage of a tracked accumulator atom at a call declared by a wider owner (CharSequence, Appendable,
     * Object, Writer, ...) is recorded with the declaring class of the method the JVM selects on the accumulator's exact
     * class (this method), and the tables above classify it by that class.
     */
    static String dispatchedOwner(String siteDeclaring, Class<?> exact, java.lang.reflect.Method declared) {
        if (exact == null || declared == null || isTableDeclaring(siteDeclaring)) {
            return null;
        }
        java.lang.reflect.Method d = TerminalBodyKinds.selectedDeclaration(exact, declared);
        return (d != null ? d.getDeclaringClass() : declared.getDeclaringClass()).getName();
    }

    /** The owner a usage is classified by: its dispatched owner when recorded, else the site's declared owner. */
    static String classifyingOwner(String siteDeclaring, String dispatchOwner) {
        return dispatchOwner != null ? dispatchOwner : siteDeclaring;
    }

    /**
     * The extraction methods pass 2 seeds and the parent lowers ({@code StringView.create(StringBuilder|StringBuffer)}; a
     * StringWriter's as {@code StringView.create(writer.buf)}).
     */
    static boolean isSeedableExtraction(String declaringClass, String methodName, String signature) {
        return "toString".equals(methodName) && (signature == null || signature.isEmpty()) && declaringClass != null &&
                        StringAtoms.ACC_SEED_TYPES.contains(declaringClass);
    }
}
