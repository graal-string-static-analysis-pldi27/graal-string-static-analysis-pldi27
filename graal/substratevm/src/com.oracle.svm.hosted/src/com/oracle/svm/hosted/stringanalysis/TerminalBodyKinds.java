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
import java.lang.reflect.Modifier;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;

/**
 * Kind-level terminal-body IC entries: gives the IC sites inside the terminal bodies (where the walk stops while the
 * runtime body continues: {@code String} / {@code CharSequence} bodies and the concat machinery,
 * {@link StringAnalysisPolicy#isConcatMachineryClass}) a complete rep set, computed per kind from the image's admitted
 * decisions:
 * <ul>
 * <li><b>String/CharSequence bodies</b>: a rep kind K runs the instance body {@code D.m} with itself as {@code this}
 * iff K's whitelist admits {@code m} and K inherits {@code D.m} (no class between K and D declares it):
 * {@link #entryBodies} (E_K). A flat kind ({@link InlineCacheRegistry#isValueCarryingFlatRep}, e.g. SingleByteString)
 * has no whitelist and may run any inherited body, so it is listed at every terminal-body site. The inherited bodies
 * that hand {@code this} to walked code ({@code formatted}, {@code transform}, {@code split}, ...) are entered by the
 * walk for a flat candidate ({@code StringTerminalHandList.FLAT_HANDOFF_NAMES}), so their downstream sites carry the
 * flat kind through the walk's receiver tags (except members the flat rep declares itself, whose body hands
 * {@code this} nowhere); a non-flat kind never escapes that way (the E_K closure). The argument-deflection bodies
 * ({@link #isDeflectionBody}) run with every admitted kind as their argument.</li>
 * <li><b>the concat group</b> ({@code StringConcatHelper}, {@code StringConcatFactory} and its nested classes, the hidden
 * {@code String$$StringConcat} classes): reached by a rep only as a concat operand. A StringView is an operand only at
 * a non-copying concat (or a copying one lowered with RepConcat), a lazy rep only at a non-copying concat and only when it overrides
 * {@code getBytes(byte[],int,byte)} ({@code LazyConcatHeuristic.isLazyOperandOk}; any other concat usage rejects it),
 * so a non-flat kind is listed iff an admitted decision of it has such a usage; flat kinds always. A lazy kind is
 * listed only when one of those usages is an outer that stays stock; the other inners are paired with their lazy
 * outers in the profile ({@link LazyOperandPairing}, revert {@code ic.ktprecise=0}).</li>
 * </ul>
 * The kind set is united with the walk's own receiver tags (which carry the argument channels). The entry is an
 * ordinary INLINE_CACHE variant behind the marker {@link #KT_PREFIX}: a marked entry is complete inside a terminal
 * body, so the terminal-body decline ({@link StringAnalysisPolicy#alwaysVirtJdkTrivialApplies}) does not apply to it.
 * String's nested classes and the rep classes keep no marked entry. The hidden {@code String$$StringConcat} keys are
 * per-build (never matching a parent site). The rest of {@code java.lang.invoke} is walked like any JDK code and keeps
 * its entry unmarked. Premises pinned by {@code KindTerminalPremiseTest}.
 */
final class TerminalBodyKinds {

    /** The profile marker of a kind-level terminal-body entry: {@code <key> INLINE_CACHE KT:<variant>}. */
    static final String KT_PREFIX = "KT:";

    enum Group {
        STRING_BODY,
        CONCAT,
        NONE
    }

    static Group group(String enclosingClass) {
        if (enclosingClass == null) {
            return Group.NONE;
        }
        if (enclosingClass.equals("java.lang.String") || enclosingClass.equals("java.lang.CharSequence")) {
            return Group.STRING_BODY;
        }
        if (StringAnalysisPolicy.isConcatMachineryClass(enclosingClass)) {
            return Group.CONCAT;
        }
        return Group.NONE;
    }

    /** A rep kind's admission whitelist over (name, declaring class, usage signature). */
    interface Whitelist {
        boolean admits(String name, String declaringClass, String signature);
    }

    /** The whitelist the verdict layer applies to a kind; null for a flat (value-carrying) kind, which has none. */
    static Whitelist whitelistOf(String kind) {
        if (isFlat(kind)) {
            return null;
        }
        if ("SV".equals(kind)) {
            return StringViewWhitelist::isWhitelistedUsage;
        }
        if (LazyConcatMint.isLazyVariant(kind)) {
            return (n, d, s) -> LazyConcatWhitelist.isWhitelisted(n, d, s, kind);
        }
        throw new IllegalArgumentException("unknown rep kind " + kind);
    }

    static boolean isFlat(String kind) {
        Class<?> c = InlineCacheRegistry.getRepClass(kind);
        return c != null && InlineCacheRegistry.isValueCarryingFlatRep(c);
    }

    static boolean isKnownKind(String kind) {
        return InlineCacheRegistry.getRepClass(kind) != null;
    }

    /** {@code name + descriptor} of a reflected method, the key form of {@link #methodKey(String)}. */
    static String nameAndDescriptor(Method m) {
        StringBuilder sb = new StringBuilder(m.getName()).append('(');
        for (Class<?> p : m.getParameterTypes()) {
            sb.append(p.descriptorString());
        }
        return sb.append(')').append(m.getReturnType().descriptorString()).toString();
    }

    /** The usage-signature format of the whitelists: parameter descriptors joined by ",". */
    static String usageSignature(Method m) {
        StringBuilder sb = new StringBuilder();
        for (Class<?> p : m.getParameterTypes()) {
            if (sb.length() > 0) {
                sb.append(',');
            }
            sb.append(p.descriptorString());
        }
        return sb.toString();
    }

    /**
     * The class whose declaration of {@code m} runs for a receiver of class {@code rep}: the JVM's
     * selection ({@link #selectedDeclaration}). Null only if no class from {@code rep} up declares a selectable method.
     */
    static Class<?> implementingClass(Class<?> rep, Method m) {
        Method d = selectedDeclaration(rep, m);
        return d == null ? null : d.getDeclaringClass();
    }

    /**
     * The single override decision of the IC machinery (plugin branches, E_K, the REDIRECT override test, the premise
     * pins). The declaration that {@code invokevirtual} of {@code m} selects for a receiver of class {@code receiver}
     * (JVMS 5.4.6): from {@code receiver} up, the first class declaring an instance method with {@code m}'s name and
     * exact descriptor (a covariant override is a different method; the bridge with {@code m}'s descriptor is selected)
     * that is {@code m} or can override it (JVMS 5.4.5, {@link #canOverride}). Bridges and synthetic methods are
     * included. Null if nothing is selected (an interface method no class implements).
     */
    static Method selectedDeclaration(Class<?> receiver, Method m) {
        for (Class<?> c = receiver; c != null; c = c.getSuperclass()) {
            for (Method d : c.getDeclaredMethods()) {
                if (d.equals(m) || (sameNameAndDescriptor(d, m) && canOverride(d, m))) {
                    return d;
                }
            }
        }
        return null;
    }

    /**
     * JVMS 5.4.5: does {@code mC} override {@code mA}? {@code mC}'s class is a subclass (or implementor) of
     * {@code mA}'s; same name and descriptor; {@code mC} is an instance method and not private; and {@code mA} is public
     * or protected, or package-private and either declared in {@code mC}'s run-time package (package name and defining
     * loader) or overridden transitively through an {@code mB} declared strictly between the two classes.
     */
    static boolean canOverride(Method mC, Method mA) {
        Class<?> c = mC.getDeclaringClass();
        Class<?> a = mA.getDeclaringClass();
        if (c == a || !a.isAssignableFrom(c) || !sameNameAndDescriptor(mC, mA)) {
            return false;
        }
        int mc = mC.getModifiers();
        int ma = mA.getModifiers();
        if (Modifier.isStatic(mc) || Modifier.isPrivate(mc) || Modifier.isStatic(ma) || Modifier.isPrivate(ma)) {
            return false;
        }
        if (Modifier.isPublic(ma) || Modifier.isProtected(ma)) {
            return true;
        }
        if (sameRuntimePackage(c, a)) {
            return true;
        }
        for (Class<?> b = c.getSuperclass(); b != null && b != a; b = b.getSuperclass()) {
            for (Method mB : b.getDeclaredMethods()) {
                if (sameNameAndDescriptor(mB, mA) && canOverride(mC, mB) && canOverride(mB, mA)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean sameRuntimePackage(Class<?> x, Class<?> y) {
        return x.getPackageName().equals(y.getPackageName()) && x.getClassLoader() == y.getClassLoader();
    }

    private static boolean sameNameAndDescriptor(Method x, Method y) {
        return x.getName().equals(y.getName()) && x.getReturnType() == y.getReturnType() && java.util.Arrays.equals(x.getParameterTypes(), y.getParameterTypes());
    }

    /**
     * E_K: the {@code java.lang.String} instance bodies (non-private, bridges included) a non-flat kind runs with
     * itself as {@code this} — admitted by its whitelist and inherited (not overridden). As {@code name+descriptor}.
     */
    static Set<String> entryBodies(String kind) {
        return ENTRY_BODIES.computeIfAbsent(kind, TerminalBodyKinds::computeEntryBodies);
    }

    private static final java.util.Map<String, Set<String>> ENTRY_BODIES = new java.util.concurrent.ConcurrentHashMap<>();

    private static Set<String> computeEntryBodies(String kind) {
        Whitelist w = whitelistOf(kind);
        Class<?> rep = InlineCacheRegistry.getRepClass(kind);
        if (w == null || rep == null) {
            throw new IllegalArgumentException("entryBodies of a flat or unknown kind " + kind);
        }
        Set<String> out = new TreeSet<>();
        for (Method m : String.class.getDeclaredMethods()) {
            if (Modifier.isStatic(m.getModifiers()) || Modifier.isPrivate(m.getModifiers())) {
                continue;
            }
            if (w.admits(m.getName(), "java.lang.String", usageSignature(m)) && implementingClass(rep, m) == String.class) {
                out.add(nameAndDescriptor(m));
            }
        }
        return java.util.Collections.unmodifiableSet(out);
    }

    /**
     * The argument-deflection bodies: the targets whose argument slot is a terminal (equals, the bridge
     * {@code compareTo(Object)}) and the EQUALS_MATRIX REDIRECT targets {@code maybeCustomStringEquals(Object)} and
     * {@code maybeCustomStringCompareTo(String)}: they run with an admitted rep as the argument without the walk
     * entering them. The stock {@code compareTo(String)} is not one (a rep argument reaches it only through
     * {@code maybeCustomStringCompareTo}, which deflects it first).
     */
    static boolean isDeflectionBody(String declaringClass, String name, String descriptor) {
        return StringAtoms.isStringEquals(false, declaringClass, name, descriptor) ||
                        (StringAtoms.isStringCompareTo(false, declaringClass, name, descriptor) && "(Ljava/lang/Object;)I".equals(descriptor)) ||
                        ("java.lang.String".equals(declaringClass) && "maybeCustomStringEquals".equals(name) && "(Ljava/lang/Object;)Z".equals(descriptor)) ||
                        ("java.lang.String".equals(declaringClass) && "maybeCustomStringCompareTo".equals(name) && "(Ljava/lang/String;)I".equals(descriptor));
    }

    /** Does a String/CharSequence instance body run with a value of kind K as {@code this}? (non-flat K). */
    static boolean runsAsThis(String kind, String declaringClass, String nameAndDescriptor) {
        if ("java.lang.String".equals(declaringClass)) {
            return entryBodies(kind).contains(nameAndDescriptor);
        }
        if ("java.lang.CharSequence".equals(declaringClass)) {
            // a CharSequence default body runs for a K receiver only if no class from K up overrides it (JVM selection)
            for (Method m : CharSequence.class.getDeclaredMethods()) {
                if (nameAndDescriptor(m).equals(nameAndDescriptor) && !Modifier.isStatic(m.getModifiers())) {
                    Class<?> rep = InlineCacheRegistry.getRepClass(kind);
                    return rep == null || selectedDeclaration(rep, m) == null;
                }
            }
            return true; // unknown body: conservative
        }
        return true;
    }

    /**
     * The kind-level rep set of an IC site in a terminal body: {@code key} is the profile key
     * {@code class#name(desc)ret@bci}; {@code admitted} the image's admitted rep kinds; {@code svConcatOperand} whether
     * an admitted SV has a non-copying concat-operand usage. Returns null if the site is not in a covered group.
     */
    static Set<String> kindSet(String key, Collection<String> admitted, boolean svConcatOperand) {
        return kindSet(key, admitted, svConcatOperand ? Set.of("SV") : Set.of());
    }

    /**
     * Nested concat: {@code concatOperandKinds} = the non-flat kinds an admitted decision of which is a
     * non-copying concat operand (SV; a lazy rep under {@code lc.lazyoperand},
     * {@code LazyConcatHeuristic.isLazyOperandOk}): exactly those are listed in the concat group.
     */
    static Set<String> kindSet(String key, Collection<String> admitted, Set<String> concatOperandKinds) {
        int hash = key.indexOf('#');
        int at = key.lastIndexOf('@');
        if (hash < 0 || at < hash) {
            return null;
        }
        String cls = key.substring(0, hash);
        Group g = group(cls);
        if (g == Group.NONE) {
            return null;
        }
        String nd = key.substring(hash + 1, at);
        int paren = nd.indexOf('(');
        String name = paren < 0 ? nd : nd.substring(0, paren);
        String descriptor = paren < 0 ? "" : nd.substring(paren);
        Set<String> out = new TreeSet<>();
        for (String k : admitted) {
            if (!isKnownKind(k)) {
                out.add(k); // an unknown rep name: list it (the parent then declines the site)
                continue;
            }
            if (isFlat(k)) {
                out.add(k);
                continue;
            }
            if (g == Group.CONCAT) {
                if (concatOperandKinds.contains(k)) {
                    out.add(k);
                }
                continue;
            }
            if (isDeflectionBody(cls, name, descriptor) || runsAsThis(k, cls, nd)) {
                out.add(k);
            }
        }
        return out;
    }

    /** The marked variant: the walked variant's reps united with the kind set. */
    static String markedVariant(String walkedVariant, Set<String> walkedCustomReps, Set<String> kinds) {
        Set<String> reps = new LinkedHashSet<>(walkedCustomReps);
        reps.addAll(kinds);
        if (reps.isEmpty()) {
            return KT_PREFIX + walkedVariant;
        }
        return KT_PREFIX + "EXACT," + String.join(",", reps);
    }

    /** The parent's reading: the unmarked variant, or null if {@code variant} carries no marker. */
    static String stripMarker(String variant) {
        return variant != null && variant.startsWith(KT_PREFIX) ? variant.substring(KT_PREFIX.length()) : null;
    }

    private TerminalBodyKinds() {
    }
}
