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

/**
 * The one source of truth for which lazy-concat rep class an admitted LAZY_CONCAT site mints.
 *
 * <p>
 * A {@code LAZY_CONCAT} variant is a decision name; the rep the replacement constructs is decided by the site's total
 * parts (dynamic operands + recipe constants), with {@code ARRAY_LAZY} as the catch-all when the count does not fit the
 * variant's fixed shape. The heuristic names an indy site by its total parts too ({@link #shapeVariant}), so the name is
 * the minted rep. If the two sides used different rules, an admit could mint a class its downstream {@code INLINE_CACHE}
 * tags do not name, and the IC chain would send the minted value-null rep down the direct {@code String.<m>} else: an
 * NPE. Both sides therefore call {@link #mintedRep}: the parent ({@link StringRepresentationReplacementPlugin}) picks
 * its factory from it, and the child names every LC rep through it ({@link HeuristicOrchestrator#repTypeOf},
 * {@link LazyConcatHeuristic}'s whitelist). The result is an {@link InlineCacheRegistry} rep name, or {@code null} when
 * the parent does not replace the site (a plain String).
 */
final class LazyConcatMint {

    static final char RECIPE_DYNAMIC_TAG = '\u0001';
    static final char RECIPE_CONSTANT_TAG = '\u0002';

    static final String ROPE = "ROPE";
    static final String THREE_WAY = "THREE_WAY";
    static final String FIXED4 = "FIXED4";
    static final String ARRAY_LAZY = "ARRAY_LAZY";
    static final String INTERLEAVED = "INTERLEAVED";

    /**
     * Print-only (default off): one {@code [lc-mintlog] child} line per admitted LAZY_CONCAT decision (its predicted rep)
     * and one {@code [lc-mintlog] parent} line per replaced concat; joined by site they must agree.
     */
    static final boolean MINT_LOG = Boolean.getBoolean("svm.stringanalysis.lc.mintlog");

    private LazyConcatMint() {
    }

    /** Whether {@code variant} is a lazy-concat decision variant. */
    static boolean isLazyVariant(String variant) {
        return ROPE.equals(variant) || THREE_WAY.equals(variant) || FIXED4.equals(variant) || ARRAY_LAZY.equals(variant) || INTERLEAVED.equals(variant);
    }

    /**
     * The total part count of an indy concat site: the dynamic operands plus one part per maximal literal run and per
     * {@code \2} constant of the recipe ({@code recipe == null}: {@code makeConcat}, every part dynamic).
     */
    static int totalParts(String recipe, int dynamicCount) {
        if (recipe == null) {
            return dynamicCount;
        }
        int constants = 0;
        boolean inLiteral = false;
        for (int i = 0; i < recipe.length(); i++) {
            char c = recipe.charAt(i);
            if (c == RECIPE_DYNAMIC_TAG) {
                inLiteral = false;
            } else if (c == RECIPE_CONSTANT_TAG) {
                constants++;
                inLiteral = false;
            } else if (!inLiteral) {
                constants++;
                inLiteral = true;
            }
        }
        return dynamicCount + constants;
    }

    /**
     * The single delimiter of an interleaved recipe ({@code \1 d \1 d ... \1}, no {@code \2} constants, every separator
     * equal), or {@code null} when the recipe is not of that form.
     */
    static String interleavedDelimiter(String recipe, int dynamicCount) {
        if (recipe == null || recipe.indexOf(RECIPE_CONSTANT_TAG) >= 0) {
            return null;
        }
        String[] segments = recipe.split(String.valueOf(RECIPE_DYNAMIC_TAG), -1);
        if (segments.length != dynamicCount + 1) {
            return null;
        }
        if (!segments[0].isEmpty() || !segments[dynamicCount].isEmpty()) {
            return null;
        }
        if (dynamicCount < 2) {
            return null;
        }
        String delimiter = segments[1];
        for (int i = 2; i < dynamicCount; i++) {
            if (!segments[i].equals(delimiter)) {
                return null;
            }
        }
        return delimiter;
    }

    /**
     * The rep the replacement mints at an indy concat site with profile variant {@code variant}, {@code dynamicCount}
     * dynamic operands and {@code recipe} ({@code null} for {@code makeConcat}); {@code null} = not replaced.
     */
    static String mintedRep(String variant, int dynamicCount, String recipe) {
        if (variant == null || dynamicCount < 1) {
            return null;
        }
        boolean isRope = ROPE.equals(variant);
        boolean isThreeWay = THREE_WAY.equals(variant);
        boolean isFixed4 = FIXED4.equals(variant);
        boolean isArrayLazy = ARRAY_LAZY.equals(variant);
        boolean isInterleaved = INTERLEAVED.equals(variant);
        if (!isRope && !isThreeWay && !isFixed4 && !isArrayLazy && !isInterleaved) {
            return null;
        }
        int totalParts = totalParts(recipe, dynamicCount);
        // Every site gates on its total parts, so the total-parts name of shapeVariant always mints itself.
        if (totalParts < 2) {
            return null;
        }
        if ((isInterleaved || isArrayLazy) && totalParts < 5) {
            return null;
        }
        if (isInterleaved) {
            return interleavedDelimiter(recipe, dynamicCount) != null ? INTERLEAVED : null;
        }
        if (isRope && totalParts == 2) {
            return ROPE;
        }
        if (isThreeWay && totalParts == 3) {
            return THREE_WAY;
        }
        if (isFixed4 && totalParts == 4) {
            return FIXED4;
        }
        return ARRAY_LAZY; // the catch-all: the variant's fixed shape does not fit the part count
    }

    /**
     * The decision variant of an indy concat site, named by its total parts so that it is exactly the minted rep
     * ({@code mintedRep(shapeVariant(d, r), d, r) == shapeVariant(d, r)}): 2 -> ROPE, 3 -> THREE_WAY, 4 -> FIXED4, 5+ ->
     * INTERLEAVED for a single non-empty-delimiter recipe, else ARRAY_LAZY; {@code null} below 2 parts.
     */
    static String shapeVariant(int dynamicCount, String recipe) {
        if (dynamicCount < 1) {
            return null;
        }
        int total = totalParts(recipe, dynamicCount);
        switch (total) {
            case 0, 1:
                return null;
            case 2:
                return ROPE;
            case 3:
                return THREE_WAY;
            case 4:
                return FIXED4;
            default:
                String delimiter = interleavedDelimiter(recipe, dynamicCount);
                return delimiter != null && !delimiter.isEmpty() ? INTERLEAVED : ARRAY_LAZY;
        }
    }

    /** The {@link LazyConcatFactory} converter for a dynamic operand of static type {@code type} (JLS conversion, no box). */
    static java.lang.reflect.Method converterMethod(Class<?> type) throws NoSuchMethodException {
        Class<?> param;
        if (type == String.class) {
            param = String.class;
        } else if (!type.isPrimitive()) {
            param = Object.class;
        } else if (type == byte.class || type == short.class || type == int.class) {
            param = int.class;
        } else {
            param = type; // long, char, boolean, float, double
        }
        return LazyConcatFactory.class.getDeclaredMethod("str", param);
    }

    /**
     * The {@link LazyConcatFactory} method that mints {@code minted} (the parent resolves exactly this method; the premise
     * test checks the returned object's class is the registry class of {@code minted}). A replaced 2-part concat uses
     * {@link LazyConcatFactory#ropeInlinePrologue}, whose empty-operand fast cases are force-inlined into the site (as
     * stock decides them inline) while the rope construction stays out of line. Codegen only: same semantics and minted
     * class; the child does not see it. The other lazy factories have no trivial fast case.
     */
    static java.lang.reflect.Method factoryMethod(String minted) throws NoSuchMethodException {
        if (minted == null) {
            return null;
        }
        return switch (minted) {
            case ROPE -> LazyConcatFactory.class.getDeclaredMethod("ropeInlinePrologue", String.class, String.class);
            case THREE_WAY -> LazyConcatFactory.class.getDeclaredMethod("threeWay", String.class, String.class, String.class);
            case FIXED4 -> LazyConcatFactory.class.getDeclaredMethod("fixed4", String.class, String.class, String.class, String.class);
            case ARRAY_LAZY -> LazyConcatFactory.class.getDeclaredMethod("arrayLazy", String[].class);
            case INTERLEAVED -> LazyConcatFactory.class.getDeclaredMethod("interleaved", String[].class, String.class);
            default -> null;
        };
    }

    /** The {@link LazyConcatFactory} replacement of the {@code String.join} with signature {@code sig}; {@code null} = none. */
    static java.lang.reflect.Method joinFactoryMethod(String sig) throws NoSuchMethodException {
        if (JOIN_ARRAY_SIG.equals(sig)) {
            return LazyConcatFactory.class.getDeclaredMethod("join", CharSequence.class, CharSequence[].class);
        }
        if (JOIN_ITERABLE_SIG.equals(sig)) {
            return LazyConcatFactory.class.getDeclaredMethod("join", CharSequence.class, Iterable.class);
        }
        return null;
    }

    /** The rep minted at a {@code String.concat(String)} site: a 2-operand rope at a {@code ROPE} site, else none. */
    static String mintedRepForStringConcat(String variant) {
        return ROPE.equals(variant) ? ROPE : null;
    }

    /**
     * The {@code String.join} lazy source table: {@code join(CharSequence, CharSequence...)} and
     * {@code join(CharSequence, Iterable)}, whose result the replacement builds as an
     * {@link com.oracle.svm.core.stringrep.InterleavedStringArray} (parts stringified at the call, as the JDK does). Keyed by
     * the {@code SiteKeys.formatSignature} format. Such a call is a LAZY_CONCAT candidate on its STRING_METHOD_CALL
     * vertex, judged by the same machinery as every concat; its variant and minted rep are {@link #INTERLEAVED}.
     */
    static final String JOIN_CLASS = "java.lang.String";
    static final String JOIN_NAME = "join";
    static final String JOIN_ARRAY_SIG = "Ljava/lang/CharSequence;,[Ljava/lang/CharSequence;";
    static final String JOIN_ITERABLE_SIG = "Ljava/lang/CharSequence;,Ljava/lang/Iterable;";
    static final java.util.Set<String> JOIN_SIGNATURES = java.util.Set.of(JOIN_ARRAY_SIG, JOIN_ITERABLE_SIG);

    /** Whether {@code (decl, name, sig)} is an entry of the join source table. */
    static boolean isJoinSource(String decl, String name, String sig) {
        return JOIN_CLASS.equals(decl) && JOIN_NAME.equals(name) && sig != null && JOIN_SIGNATURES.contains(sig);
    }

    /** Whether {@code v} is a join source call site (a STRING_METHOD_CALL vertex of a join source table entry). */
    static boolean isJoinSource(SugVertex v) {
        return v != null && v.getNodeType() == SugNodeType.STRING_METHOD_CALL && isJoinSource(v.getDeclaringClass(), v.getMethodName(), v.getMethodSignature());
    }

    /** The rep the replacement mints at a join source call site: an interleaved string at an {@code INTERLEAVED} site. */
    static String mintedRepForStringJoin(String variant) {
        return INTERLEAVED.equals(variant) ? INTERLEAVED : null;
    }

    /** The child side: the rep minted for the admitted LAZY_CONCAT candidate {@code concat} with variant {@code variant}. */
    static String mintedRep(SugVertex concat, String variant) {
        if (concat != null && concat.isStringConcatCall()) {
            return mintedRepForStringConcat(variant);
        }
        if (isJoinSource(concat)) {
            return mintedRepForStringJoin(variant);
        }
        int dyn = concat != null ? concat.getDynamicOperandCount() : -1;
        if (concat == null || dyn < 1) {
            // No recorded operand shape: a hand-built (JUnit) vertex or an invoke-based CONCAT_EXPRESSION vertex the parent
            // never replaces. The variant's own rep: over-naming a rep the parent does not mint is sound.
            return variant;
        }
        return mintedRep(variant, dyn, concat.getConcatRecipe());
    }
}
