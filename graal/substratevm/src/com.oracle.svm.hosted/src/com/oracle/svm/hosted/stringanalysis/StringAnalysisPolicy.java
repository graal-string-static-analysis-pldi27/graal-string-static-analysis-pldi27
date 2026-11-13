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

import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.vm.ci.meta.ResolvedJavaMethod;

public final class StringAnalysisPolicy {

    private static final Set<String> INTERNAL_METHOD_NAMES = Set.of("<init>", "<clinit>");

    private static final Set<String> INTERNAL_CLASS_PREFIXES = Set.of(
                    "java.",
                    "javax.",
                    "jdk.",
                    "sun.",
                    "com.sun.",
                    "org.ietf.",
                    "org.w3c.",
                    "org.xml.",
                    "org.graalvm.",
                    "com.oracle.graal.",
                    "com.oracle.svm.",
                    "com.oracle.truffle.",
                    "com.oracle.javac.");

    /**
     * The always-virt rule. The parent-side plugins that claim trivial String-method invoke sites
     * ({@link InlineCacheTrivialMethodNodePlugin}: the direct {@code String.<m>} emission, the equals lowering, the rep
     * chains; {@link StringLengthNodePlugin}: the length form) make no claim at a site whose enclosing method is a
     * terminal body ({@link #isTerminalBodyClass}, the scope described at {@link #TERMINAL_BODY_CLASSES}; {@code b.getMethod()},
     * the outer body for an inline copy, as in {@code SiteKeys.profileKey}): the site rides the stock pipeline.
     * That is rep-safe for the receiver dispatch: a rep in the sound cone suppresses single-callee devirt, and the
     * virtual call dispatches to the rep's own override. User-code sites are unaffected.
     * <p>
     * {@link EqualsMatrixNodePlugin}'s REDIRECT replacement is deliberately outside the rule's scope: it is a correctness
     * mechanism, not a performance claim. The stock virtual {@code equals} at a clean receiver cone devirtualizes into
     * Graal's unguarded {@code StringEqualsInvocationPlugin} field-read intrinsic, which NPEs on a value-null rep
     * argument, so removing it would be unsound exactly at the REDIRECT sites. At a REDIRECT site in a terminal body
     * the rule removes only the equals-table lowering; the site falls to that plugin's virtual
     * {@code maybeCustomStringEquals} residual.
     * <p>
     * The rule could be dropped once the analysis delivers complete arrivals for the concat machinery's operand-provenance
     * tagging and the {@code String.valueOf} model's {@code result ir} arrival propagation (then the wrong
     * {@code UNKNOWN} entries are gone).
     */
    static boolean alwaysVirtJdkTrivialApplies(GraphBuilderContext b) {
        ResolvedJavaMethod enclosing = b.getMethod();
        if (enclosing == null) {
            return false;
        }
        String encl = enclosing.getDeclaringClass().toJavaName();
        return isTerminalBodyClass(encl);
    }

    /**
     * The always-virt scope: the rule keeps only the terminal bodies on the stock pipeline -- the bodies that run with an admitted rep while the walk treats the crossing as terminal, the only places
     * where an INLINE_CACHE entry can miss a rep that is really there: {@link #TERMINAL_BODY_CLASSES} (String's own
     * bodies: the receiver-slot terminal of every String instance method, the equals/mCSE/compareTo argument deflects, the
     * inherited bodies; the concat machinery, {@link #isConcatMachineryClass}; the rep classes' own bodies). Every other
     * JDK-internal site is walked like user code (the IR walk, or a model's call-effect site whose tag is complete by the
     * model premise), so its entry is as complete as a user-code entry.
     * <p>
     * Premise: a terminal body hands a non-flat (value-null) rep to code outside the terminal-body classes only by a
     * virtual call on the rep itself, which dispatches into the rep's own override, a terminal body
     * ({@code KindTerminalPremiseTest}, {@code TerminalBodyPremiseTest}). A flat (value-carrying) rep
     * ({@code InlineCacheRegistry.isValueCarryingFlatRep}) has no admission whitelist and may run any inherited String body;
     * the bodies that hand {@code this} to walked code or return it in a container (the flat hand-offs,
     * {@code StringTerminalHandList.FLAT_HANDOFF_NAMES}: {@code transform}, {@code formatted}, {@code describeConstable},
     * {@code split}, the {@code Matcher}-based and case-mapping bodies, ...) are entered by the walk for an atom that may
     * become one ({@code RecursiveTracking.flatHandOffEntries}), so the downstream sites carry
     * the flat kind like any other rep, or the walk refuses. The undelivered residue relies on content equivalence
     * ({@code FlatRepPremiseTest}): an atom also seeded for SV/LC is not entered at a hand-off that kind whitelists
     * ({@code RecursiveTracking.flatHandOffGate}), so the sites downstream would see the flat rep untagged (counted,
     * {@code # FLAT_HANDOFF_UNDELIVERED}). That residue is empty: the members SV/LC whitelist (the case mappings,
     * {@code offsetByCodePoints}) are declared by SingleByteString with a body that never hands {@code this} on, and a
     * member the SB rep declares is no hand-off for it ({@code RecursiveTracking.sbsDeclares},
     * {@code SingleByteHandOffClosureTest}).
     */
    static final Set<String> TERMINAL_BODY_CLASSES = Set.of(
                    "java.lang.String",
                    "java.lang.CharSequence",
                    "java.lang.StringConcatHelper");

    static final Set<String> TERMINAL_BODY_PREFIXES = Set.of(
                    "java.lang.String$",
                    "java.lang.StringConcatHelper$",
                    "com.oracle.svm.core.stringrep.");

    /**
     * The concat machinery, the code a concat operand runs in after the walk's CONCAT_OPERAND terminal:
     * {@code StringConcatHelper}, {@code java.lang.invoke.StringConcatFactory} (with nested classes) and the generated
     * {@code java.lang.String$$StringConcat} classes. The rest of {@code java.lang.invoke} is not a terminal body: a rep
     * reaches it only through an argument slot the walk enters, so it is walked like other JDK code. Shared by
     * {@link #isTerminalBodyClass} and {@link TerminalBodyKinds#group}.
     */
    static boolean isConcatMachineryClass(String qualifiedName) {
        return qualifiedName != null && (qualifiedName.equals("java.lang.StringConcatHelper") || qualifiedName.startsWith("java.lang.StringConcatHelper$") ||
                        qualifiedName.equals("java.lang.invoke.StringConcatFactory") || qualifiedName.startsWith("java.lang.invoke.StringConcatFactory$") ||
                        qualifiedName.startsWith("java.lang.String$$StringConcat"));
    }

    static boolean isTerminalBodyClass(String qualifiedName) {
        if (qualifiedName == null) {
            return false;
        }
        if (TERMINAL_BODY_CLASSES.contains(qualifiedName) || isConcatMachineryClass(qualifiedName)) {
            return true;
        }
        for (String prefix : TERMINAL_BODY_PREFIXES) {
            if (qualifiedName.startsWith(prefix)) {
                return true;
            }
        }
        return false;
    }

    private StringAnalysisPolicy() {
    }

    static boolean isInternalCall(SugVertex v) {
        if (v.getNodeType() != SugNodeType.STRING_METHOD_CALL && v.getNodeType() != SugNodeType.JDK_LIBRARY_CALL) {
            return false;
        }
        if (v.getMethodName() == null) {
            return false;
        }
        if (INTERNAL_METHOD_NAMES.contains(v.getMethodName())) {
            return true;
        }
        return false;
    }

    static boolean isUserCodeClass(String qualifiedName) {
        if (qualifiedName == null) {
            return false;
        }
        return !isInternalClass(qualifiedName);
    }

    static boolean isInternalClass(String qualifiedName) {
        if (qualifiedName == null) {
            return false;
        }
        for (String prefix : INTERNAL_CLASS_PREFIXES) {
            if (qualifiedName.startsWith(prefix)) {
                return true;
            }
        }
        return false;
    }

    static String enclosingClassName(SugVertex v) {
        return v.getEnclosingClassName();
    }
}
