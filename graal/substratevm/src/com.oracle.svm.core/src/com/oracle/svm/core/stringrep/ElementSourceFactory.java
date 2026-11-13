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
package com.oracle.svm.core.stringrep;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.function.Consumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * The factories of the element-source API table ({@code ElementSources} in the analysis), used only at admitted call
 * sites. Each is the JDK 25 algorithm of the replaced call ({@code Pattern.splitAsStream} / {@code Pattern.split} /
 * {@code String.split} / {@code String.lines}) with one change: a piece of an exact {@code java.lang.String} input is a
 * {@link StringView} over the input ({@code createStored} when the analysis saw the pieces stored) instead of a copy.
 * A rep input runs a separate {@code rep*} copy of the same algorithm (so the exact-String path's parameters stay
 * exact), whose pieces are nested views for a {@code StringView}, else the rep's own {@code substring}; the rep is
 * never handed to the stock split/lines code (which would then see a {@code StringView} image-wide). Any other input
 * (a non-String {@code CharSequence}, null) makes the whole call the stock call. The JDK's identities are kept: a split
 * piece covering the whole input is the input itself, an empty piece is {@code ""}, and {@code lines()} never returns
 * the receiver.
 */
public final class ElementSourceFactory {

    private ElementSourceFactory() {
    }

    private static boolean exactString(Object o) {
        return o != null && o.getClass() == String.class;
    }

    /** A split piece of the exact String {@code s}: the JDK's {@code s.substring(b, e)} (identity for the whole range), as a view. */
    static String splitPiece(String s, int b, int e, boolean stored) {
        if (b == 0 && e == s.length()) {
            return s; // String.substring: `if (beginIndex == 0 && endIndex == length) return this;`
        }
        return stored ? StringView.createStored(s, b, e) : StringView.create(s, b, e);
    }

    /**
     * A split piece of the rep {@code r}: the JDK's {@code r.subSequence(b, e).toString()} / {@code r.substring(b, e)}
     * (identity for the whole range), a nested view for a {@code StringView}, else the rep's own {@code substring}.
     */
    static String repPiece(String r, int b, int e, boolean stored) {
        if (b == 0 && e == r.length()) {
            return r; // String.substring / toString: the whole range is the input itself
        }
        if (r instanceof StringView sv) {
            return stored ? StringView.createViewStored(sv, b, e) : StringView.createView(sv, b, e);
        }
        return r.substring(b, e);
    }

    // ------------------------------------------------------------------
    // Pattern.splitAsStream(CharSequence): Pattern.java:6055-6121
    // ------------------------------------------------------------------

    /** {@code p.splitAsStream(input)}. */
    public static Stream<String> splitAsStream(Pattern p, CharSequence input, boolean stored) {
        if (p == null || !exactString(input)) {
            if (p != null && input instanceof String r) {
                return repSplitAsStream(p, r, stored);
            }
            return p.splitAsStream(input);
        }
        return StreamSupport.stream(Spliterators.spliteratorUnknownSize(
                        new MatcherIterator(p, (String) input, stored), Spliterator.ORDERED | Spliterator.NONNULL), false);
    }

    /** {@code p.splitAsStream(r)} for a non-null rep input {@code r} (out of line: the exact-String entry stays small). */
    private static Stream<String> repSplitAsStream(Pattern p, String r, boolean stored) {
        return StreamSupport.stream(Spliterators.spliteratorUnknownSize(
                        new RepMatcherIterator(p, r, stored), Spliterator.ORDERED | Spliterator.NONNULL), false);
    }

    /** The JDK's local {@code MatcherIterator}, over an exact String input. */
    private static final class MatcherIterator implements Iterator<String> {
        private final Pattern pattern;
        private final String input;
        private final boolean stored;
        private Matcher matcher;
        // The start position of the next sub-sequence of input
        // when current == input.length there are no more elements
        private int current;
        // null if the next element, if any, needs to obtained
        private String nextElement;
        // > 0 if there are N next empty elements
        private int emptyElementCount;

        MatcherIterator(Pattern pattern, String input, boolean stored) {
            this.pattern = pattern;
            this.input = input;
            this.stored = stored;
        }

        @Override
        public String next() {
            if (!hasNext()) {
                throw new NoSuchElementException();
            }
            if (emptyElementCount == 0) {
                String n = nextElement;
                nextElement = null;
                return n;
            } else {
                emptyElementCount--;
                return "";
            }
        }

        @Override
        public boolean hasNext() {
            if (matcher == null) {
                matcher = pattern.matcher(input);
                // If the input is an empty string then the result can only be a
                // stream of the input. Induce that by setting the empty
                // element count to 1
                emptyElementCount = input.length() == 0 ? 1 : 0;
            }
            if (nextElement != null || emptyElementCount > 0) {
                return true;
            }
            if (current == input.length()) {
                return false;
            }
            // Consume the next matching element
            // Count sequence of matching empty elements
            while (matcher.find()) {
                nextElement = splitPiece(input, current, matcher.start(), stored);
                current = matcher.end();
                if (!nextElement.isEmpty()) {
                    return true;
                } else if (current > 0) { // no empty leading substring for zero-width
                                          // match at the beginning of the input
                    emptyElementCount++;
                }
            }
            // Consume last matching element
            nextElement = splitPiece(input, current, input.length(), stored);
            current = input.length();
            if (!nextElement.isEmpty()) {
                return true;
            } else {
                // Ignore a terminal sequence of matching empty elements
                emptyElementCount = 0;
                nextElement = null;
                return false;
            }
        }
    }

    /** {@link MatcherIterator} over a rep input (pieces: {@link #repPiece}). */
    private static final class RepMatcherIterator implements Iterator<String> {
        private final Pattern pattern;
        private final String input;
        private final boolean stored;
        private Matcher matcher;
        // The start position of the next sub-sequence of input
        // when current == input.length there are no more elements
        private int current;
        // null if the next element, if any, needs to obtained
        private String nextElement;
        // > 0 if there are N next empty elements
        private int emptyElementCount;

        RepMatcherIterator(Pattern pattern, String input, boolean stored) {
            this.pattern = pattern;
            this.input = input;
            this.stored = stored;
        }

        @Override
        public String next() {
            if (!hasNext()) {
                throw new NoSuchElementException();
            }
            if (emptyElementCount == 0) {
                String n = nextElement;
                nextElement = null;
                return n;
            } else {
                emptyElementCount--;
                return "";
            }
        }

        @Override
        public boolean hasNext() {
            if (matcher == null) {
                matcher = pattern.matcher(input);
                // If the input is an empty string then the result can only be a
                // stream of the input. Induce that by setting the empty
                // element count to 1
                emptyElementCount = input.length() == 0 ? 1 : 0;
            }
            if (nextElement != null || emptyElementCount > 0) {
                return true;
            }
            if (current == input.length()) {
                return false;
            }
            // Consume the next matching element
            // Count sequence of matching empty elements
            while (matcher.find()) {
                nextElement = repPiece(input, current, matcher.start(), stored);
                current = matcher.end();
                if (!nextElement.isEmpty()) {
                    return true;
                } else if (current > 0) { // no empty leading substring for zero-width
                                          // match at the beginning of the input
                    emptyElementCount++;
                }
            }
            // Consume last matching element
            nextElement = repPiece(input, current, input.length(), stored);
            current = input.length();
            if (!nextElement.isEmpty()) {
                return true;
            } else {
                // Ignore a terminal sequence of matching empty elements
                emptyElementCount = 0;
                nextElement = null;
                return false;
            }
        }
    }

    // ------------------------------------------------------------------
    // Pattern.split / splitWithDelimiters: Pattern.java:1305-1482
    // ------------------------------------------------------------------

    /** {@code p.split(input)}. */
    public static String[] patternSplit(Pattern p, CharSequence input, boolean stored) {
        return patternSplit(p, input, 0, stored);
    }

    /** {@code p.split(input, limit)}. */
    public static String[] patternSplit(Pattern p, CharSequence input, int limit, boolean stored) {
        if (p == null || !exactString(input)) {
            if (p != null && input instanceof String r) {
                return repPatternSplit(p, r, limit, false, stored);
            }
            return p.split(input, limit);
        }
        return patternSplit(p, (String) input, limit, false, stored);
    }

    /** {@code p.splitWithDelimiters(input, limit)}. */
    public static String[] patternSplitWithDelimiters(Pattern p, CharSequence input, int limit, boolean stored) {
        if (p == null || !exactString(input)) {
            if (p != null && input instanceof String r) {
                return repPatternSplit(p, r, limit, true, stored);
            }
            return p.splitWithDelimiters(input, limit);
        }
        return patternSplit(p, (String) input, limit, true, stored);
    }

    /** The JDK's private {@code Pattern.split(CharSequence, int, boolean)}, over an exact String input. */
    private static String[] patternSplit(Pattern p, String input, int limit, boolean withDelimiters, boolean stored) {
        int matchCount = 0;
        int index = 0;
        boolean matchLimited = limit > 0;
        ArrayList<String> matchList = new ArrayList<>();
        Matcher m = p.matcher(input);

        // Add segments before each match found
        while (m.find()) {
            if (!matchLimited || matchCount < limit - 1) {
                if (index == 0 && index == m.start() && m.start() == m.end()) {
                    // no empty leading substring included for zero-width match
                    // at the beginning of the input char sequence.
                    continue;
                }
                String match = splitPiece(input, index, m.start(), stored);
                matchList.add(match);
                index = m.end();
                if (withDelimiters) {
                    matchList.add(splitPiece(input, m.start(), index, stored));
                }
                ++matchCount;
            } else if (matchCount == limit - 1) { // last one
                String match = splitPiece(input, index, input.length(), stored);
                matchList.add(match);
                index = m.end();
                ++matchCount;
            }
        }

        // If no match was found, return this
        if (index == 0) {
            return new String[]{input};
        }

        // Add remaining segment
        if (!matchLimited || matchCount < limit) {
            matchList.add(splitPiece(input, index, input.length(), stored));
        }

        // Construct result
        int resultSize = matchList.size();
        if (limit == 0) {
            while (resultSize > 0 && matchList.get(resultSize - 1).isEmpty()) {
                resultSize--;
            }
        }
        String[] result = new String[resultSize];
        return matchList.subList(0, resultSize).toArray(result);
    }

    /** The JDK's private {@code Pattern.split(CharSequence, int, boolean)}, over a rep input (pieces: {@link #repPiece}). */
    private static String[] repPatternSplit(Pattern p, String input, int limit, boolean withDelimiters, boolean stored) {
        int matchCount = 0;
        int index = 0;
        boolean matchLimited = limit > 0;
        ArrayList<String> matchList = new ArrayList<>();
        Matcher m = p.matcher(input);

        // Add segments before each match found
        while (m.find()) {
            if (!matchLimited || matchCount < limit - 1) {
                if (index == 0 && index == m.start() && m.start() == m.end()) {
                    // no empty leading substring included for zero-width match
                    // at the beginning of the input char sequence.
                    continue;
                }
                String match = repPiece(input, index, m.start(), stored);
                matchList.add(match);
                index = m.end();
                if (withDelimiters) {
                    matchList.add(repPiece(input, m.start(), index, stored));
                }
                ++matchCount;
            } else if (matchCount == limit - 1) { // last one
                String match = repPiece(input, index, input.length(), stored);
                matchList.add(match);
                index = m.end();
                ++matchCount;
            }
        }

        // If no match was found, return this
        if (index == 0) {
            return new String[]{input};
        }

        // Add remaining segment
        if (!matchLimited || matchCount < limit) {
            matchList.add(repPiece(input, index, input.length(), stored));
        }

        // Construct result
        int resultSize = matchList.size();
        if (limit == 0) {
            while (resultSize > 0 && matchList.get(resultSize - 1).isEmpty()) {
                resultSize--;
            }
        }
        String[] result = new String[resultSize];
        return matchList.subList(0, resultSize).toArray(result);
    }

    // ------------------------------------------------------------------
    // String.split / splitWithDelimiters: String.java:3688-3906
    // ------------------------------------------------------------------

    /** {@code s.split(regex)}. */
    public static String[] stringSplit(String s, String regex, boolean stored) {
        return stringSplit(s, regex, 0, stored);
    }

    /** {@code s.split(regex, limit)}. */
    public static String[] stringSplit(String s, String regex, int limit, boolean stored) {
        if (!exactString(s)) {
            if (s != null) {
                return repStringSplit(s, regex, limit, false, stored);
            }
            return s.split(regex, limit);
        }
        return stringSplit(s, regex, limit, false, stored);
    }

    /** {@code s.splitWithDelimiters(regex, limit)}. */
    public static String[] stringSplitWithDelimiters(String s, String regex, int limit, boolean stored) {
        if (!exactString(s)) {
            if (s != null) {
                return repStringSplit(s, regex, limit, true, stored);
            }
            return s.splitWithDelimiters(regex, limit);
        }
        return stringSplit(s, regex, limit, true, stored);
    }

    /** The JDK's private {@code String.split(String, int, boolean)} (the fastpath test verbatim). */
    private static String[] stringSplit(String s, String regex, int limit, boolean withDelimiters, boolean stored) {
        /*
         * fastpath if the regex is a (1) one-char String and this character is not one of the RegEx's meta characters
         * ".$|()[{^?*+\\", or (2) two-char String and the first char is the backslash and the second is not the ascii
         * digit or ascii letter.
         */
        char ch = 0;
        if (((regex.length() == 1 &&
                        ".$|()[{^?*+\\".indexOf(ch = regex.charAt(0)) == -1) ||
                        (regex.length() == 2 &&
                                        regex.charAt(0) == '\\' &&
                                        (((ch = regex.charAt(1)) - '0') | ('9' - ch)) < 0 &&
                                        ((ch - 'a') | ('z' - ch)) < 0 &&
                                        ((ch - 'A') | ('Z' - ch)) < 0)) &&
                        (ch < Character.MIN_HIGH_SURROGATE ||
                                        ch > Character.MAX_LOW_SURROGATE)) {
            return charSplit(s, ch, limit, withDelimiters, stored);
        }
        Pattern pattern = Pattern.compile(regex);
        return patternSplit(pattern, s, limit, withDelimiters, stored);
    }

    /** The JDK's private {@code String.split(char, int, boolean)}. */
    private static String[] charSplit(String s, char ch, int limit, boolean withDelimiters, boolean stored) {
        int matchCount = 0;
        int off = 0;
        int next;
        boolean limited = limit > 0;
        ArrayList<String> list = new ArrayList<>();
        String del = withDelimiters ? String.valueOf(ch) : null;
        while ((next = s.indexOf(ch, off)) != -1) {
            if (!limited || matchCount < limit - 1) {
                list.add(splitPiece(s, off, next, stored));
                if (withDelimiters) {
                    list.add(del);
                }
                off = next + 1;
                ++matchCount;
            } else {    // last one
                int last = s.length();
                list.add(splitPiece(s, off, last, stored));
                off = last;
                ++matchCount;
                break;
            }
        }
        // If no match was found, return this
        if (off == 0) {
            return new String[]{s};
        }

        // Add remaining segment
        if (!limited || matchCount < limit) {
            list.add(splitPiece(s, off, s.length(), stored));
        }

        // Construct result
        int resultSize = list.size();
        if (limit == 0) {
            while (resultSize > 0 && list.get(resultSize - 1).isEmpty()) {
                resultSize--;
            }
        }
        String[] result = new String[resultSize];
        return list.subList(0, resultSize).toArray(result);
    }

    /** The JDK's private {@code String.split(String, int, boolean)} over a rep receiver (the fastpath test verbatim). */
    private static String[] repStringSplit(String s, String regex, int limit, boolean withDelimiters, boolean stored) {
        /*
         * fastpath if the regex is a (1) one-char String and this character is not one of the RegEx's meta characters
         * ".$|()[{^?*+\\", or (2) two-char String and the first char is the backslash and the second is not the ascii
         * digit or ascii letter.
         */
        char ch = 0;
        if (((regex.length() == 1 &&
                        ".$|()[{^?*+\\".indexOf(ch = regex.charAt(0)) == -1) ||
                        (regex.length() == 2 &&
                                        regex.charAt(0) == '\\' &&
                                        (((ch = regex.charAt(1)) - '0') | ('9' - ch)) < 0 &&
                                        ((ch - 'a') | ('z' - ch)) < 0 &&
                                        ((ch - 'A') | ('Z' - ch)) < 0)) &&
                        (ch < Character.MIN_HIGH_SURROGATE ||
                                        ch > Character.MAX_LOW_SURROGATE)) {
            return repCharSplit(s, ch, limit, withDelimiters, stored);
        }
        Pattern pattern = Pattern.compile(regex);
        return repPatternSplit(pattern, s, limit, withDelimiters, stored);
    }

    /** The JDK's private {@code String.split(char, int, boolean)} over a rep receiver (pieces: {@link #repPiece}). */
    private static String[] repCharSplit(String s, char ch, int limit, boolean withDelimiters, boolean stored) {
        int matchCount = 0;
        int off = 0;
        int next;
        boolean limited = limit > 0;
        ArrayList<String> list = new ArrayList<>();
        String del = withDelimiters ? String.valueOf(ch) : null;
        while ((next = s.indexOf(ch, off)) != -1) {
            if (!limited || matchCount < limit - 1) {
                list.add(repPiece(s, off, next, stored));
                if (withDelimiters) {
                    list.add(del);
                }
                off = next + 1;
                ++matchCount;
            } else {    // last one
                int last = s.length();
                list.add(repPiece(s, off, last, stored));
                off = last;
                ++matchCount;
                break;
            }
        }
        // If no match was found, return this
        if (off == 0) {
            return new String[]{s};
        }

        // Add remaining segment
        if (!limited || matchCount < limit) {
            list.add(repPiece(s, off, s.length(), stored));
        }

        // Construct result
        int resultSize = list.size();
        if (limit == 0) {
            while (resultSize > 0 && list.get(resultSize - 1).isEmpty()) {
                resultSize--;
            }
        }
        String[] result = new String[resultSize];
        return list.subList(0, resultSize).toArray(result);
    }

    // ------------------------------------------------------------------
    // String.lines(): StringLatin1/StringUTF16.LinesSpliterator (char indices)
    // ------------------------------------------------------------------

    /** {@code s.lines()}. */
    public static Stream<String> lines(String s, boolean stored) {
        if (!exactString(s)) {
            if (s != null) {
                return repLines(s, stored);
            }
            return s.lines();
        }
        return StreamSupport.stream(new LinesSpliterator(s, 0, s.length(), stored), false);
    }

    /** {@code r.lines()} for a non-null rep input {@code r} (out of line: the exact-String entry stays small). */
    private static Stream<String> repLines(String r, boolean stored) {
        return StreamSupport.stream(new RepLinesSpliterator(r, 0, r.length(), stored), false);
    }

    /**
     * The JDK's {@code LinesSpliterator} over an exact String; a line is a view. The scan reads the input's
     * {@code byte[]} as the JDK does, never a per-char {@code s.charAt} (a virtual call on the de-finalized
     * {@code String}).
     */
    private static final class LinesSpliterator implements Spliterator<String> {
        private final String s;
        private final byte[] value;
        private final byte coder;
        private final boolean stored;
        private int index;        // current index, modified on advance/split
        private final int fence;  // one past last index

        LinesSpliterator(String s, int start, int length, boolean stored) {
            this(s, s.value(), s.coder(), start, length, stored);
        }

        private LinesSpliterator(String s, byte[] value, byte coder, int start, int length, boolean stored) {
            this.s = s;
            this.value = value;
            this.coder = coder;
            this.stored = stored;
            this.index = start;
            this.fence = start + length;
        }

        /** {@code StringLatin1.getChar} / {@code StringUTF16.getChar} of the input's array. */
        private char getChar(int i) {
            return coder == 0 ? (char) (value[i] & 0xff) : RepParts.getChar(value, i);
        }

        private int indexOfLineSeparator(int start) {
            for (int current = start; current < fence; current++) {
                char ch = getChar(current);
                if (ch == '\n' || ch == '\r') {
                    return current;
                }
            }
            return fence;
        }

        private int skipLineSeparator(int start) {
            if (start < fence) {
                if (getChar(start) == '\r') {
                    int next = start + 1;
                    if (next < fence && getChar(next) == '\n') {
                        return next + 1;
                    }
                }
                return start + 1;
            }
            return fence;
        }

        private String next() {
            int start = index;
            int end = indexOfLineSeparator(start);
            index = skipLineSeparator(end);
            return stored ? StringView.createStored(s, start, end) : StringView.create(s, start, end);
        }

        @Override
        public boolean tryAdvance(Consumer<? super String> action) {
            if (action == null) {
                throw new NullPointerException("tryAdvance action missing");
            }
            if (index != fence) {
                action.accept(next());
                return true;
            }
            return false;
        }

        @Override
        public void forEachRemaining(Consumer<? super String> action) {
            if (action == null) {
                throw new NullPointerException("forEachRemaining action missing");
            }
            while (index != fence) {
                action.accept(next());
            }
        }

        @Override
        public Spliterator<String> trySplit() {
            int half = (fence + index) >>> 1;
            int mid = skipLineSeparator(indexOfLineSeparator(half));
            if (mid < fence) {
                int start = index;
                index = mid;
                return new LinesSpliterator(s, value, coder, start, mid - start, stored);
            }
            return null;
        }

        @Override
        public long estimateSize() {
            return fence - index + 1;
        }

        @Override
        public int characteristics() {
            return Spliterator.ORDERED | Spliterator.IMMUTABLE | Spliterator.NONNULL;
        }
    }

    /**
     * {@link LinesSpliterator} over a rep (the JDK's {@code LinesSpliterator} on the rep's chars, read through the rep's
     * own {@code charAt}). A line is a new String, never the receiver (the JDK's {@code newString}): a nested view for a
     * {@code StringView} (always a new object), else the rep's {@code substring}, copied when it covers the whole rep.
     */
    private static final class RepLinesSpliterator implements Spliterator<String> {
        private final String s;
        private final boolean stored;
        private int index;        // current index, modified on advance/split
        private final int fence;  // one past last index

        RepLinesSpliterator(String s, int start, int length, boolean stored) {
            this.s = s;
            this.stored = stored;
            this.index = start;
            this.fence = start + length;
        }

        private int indexOfLineSeparator(int start) {
            for (int current = start; current < fence; current++) {
                char ch = s.charAt(current);
                if (ch == '\n' || ch == '\r') {
                    return current;
                }
            }
            return fence;
        }

        private int skipLineSeparator(int start) {
            if (start < fence) {
                if (s.charAt(start) == '\r') {
                    int next = start + 1;
                    if (next < fence && s.charAt(next) == '\n') {
                        return next + 1;
                    }
                }
                return start + 1;
            }
            return fence;
        }

        private String next() {
            int start = index;
            int end = indexOfLineSeparator(start);
            index = skipLineSeparator(end);
            if (s instanceof StringView sv) {
                return stored ? StringView.createViewStored(sv, start, end) : StringView.createView(sv, start, end);
            }
            if (start == 0 && end == s.length()) {
                return new StringBuilder(end).append(s).toString(); // never the receiver (the JDK's newString)
            }
            return s.substring(start, end);
        }

        @Override
        public boolean tryAdvance(Consumer<? super String> action) {
            if (action == null) {
                throw new NullPointerException("tryAdvance action missing");
            }
            if (index != fence) {
                action.accept(next());
                return true;
            }
            return false;
        }

        @Override
        public void forEachRemaining(Consumer<? super String> action) {
            if (action == null) {
                throw new NullPointerException("forEachRemaining action missing");
            }
            while (index != fence) {
                action.accept(next());
            }
        }

        @Override
        public Spliterator<String> trySplit() {
            int half = (fence + index) >>> 1;
            int mid = skipLineSeparator(indexOfLineSeparator(half));
            if (mid < fence) {
                int start = index;
                index = mid;
                return new RepLinesSpliterator(s, start, mid - start, stored);
            }
            return null;
        }

        @Override
        public long estimateSize() {
            return fence - index + 1;
        }

        @Override
        public int characteristics() {
            return Spliterator.ORDERED | Spliterator.IMMUTABLE | Spliterator.NONNULL;
        }
    }
}
