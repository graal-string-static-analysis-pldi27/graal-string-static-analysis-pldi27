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

import com.oracle.graal.pointsto.meta.AnalysisMethod;

/**
 * The transfer data model shared by the string-analysis engine and the verdict layer
 * (incomplete-fact/usage-fact records, the safe-sink set, the deterministic method
 * key orders and the structural fact bound).
 */
final class TransferFacts {

    /** The structural fact bound per summary/family component (connected-load bound and pseudo-fan cap). */
    static final int MAX_FACTS_PER_COMPONENT = 32;

    /** Primary deterministic method order key: qualified name + bci-position key. */
    static String methodFlowKey(AnalysisMethod method) {
        return method != null ? method.format("%H.%n@%p") : "";
    }

    /** Tie-break: the JVM method descriptor — qualified, return-type inclusive. */
    static String methodDescriptorKey(AnalysisMethod method) {
        return method != null ? method.getSignature().toMethodDescriptor() : "";
    }

    /** Whether the vertex is a usage-adjudicable call site (the emit/usage-source predicate). */
    static boolean isUsageSite(SugVertex vertex) {
        return vertex.getNodeType() == SugNodeType.STRING_METHOD_CALL ||
                        vertex.getNodeType() == SugNodeType.JDK_LIBRARY_CALL ||
                        vertex.getNodeType() == SugNodeType.CONCAT_EXPRESSION;
    }

    /** Whether the vertex type can originate a tracked string value (potential origin). */
    static boolean isPotentialOrigin(SugVertex vertex) {
        return switch (vertex.getNodeType()) {
            case STRING_LITERAL, CONCAT_EXPRESSION, STRING_METHOD_CALL, VARIABLE, NEW_STRING,
                            NEW_ACCUMULATOR, FLOW_NODE -> true;
            default -> false;
        };
    }

    /**
     * The safe-sink set: I/O sink methods whose String-argument paths are proven safe for String View (they call only
     * whitelisted, String View-overridden methods on the String and never read {@code value()}). A candidate flowing
     * to one as a String argument has the sink's internal incompleteness masked. The mask hides only incompleteness,
     * never usages (the whitelist gates usages independently in StringViewHeuristic.validateUsages). Keyed by
     * {@code declaringClass#name(paramDescriptor)}.
     */
    private static final Set<String> SAFE_SINKS = Set.of(
                    "java.io.PrintStream#println(Ljava/lang/String;)",
                    "java.io.PrintStream#print(Ljava/lang/String;)",
                    "java.io.PrintStream#write(Ljava/lang/String;)",
                    "java.lang.String#valueOf(Ljava/lang/Object;)");

    enum IncompleteReason {
        UNKNOWN_TARGET,
        MISSING_IR,
        UNKNOWN_EFFECT,
        INCOMPLETE_TRAVERSAL,
        UNMAPPED_ORIGIN,
        UNMAPPED_USAGE,
        RESOURCE_LIMIT,
        /**
         * The container's identity is untrackable at a connection the tracker cannot resolve (a compose-time
         * unresolvable STORE receiver with no resolvable connector; the deferred-dispatch keep-all fallback when the
         * actual-argument identity is unresolvable). Reflection/native/function-pointer/no-IR boundaries mint
         * UNKNOWN_TARGET / INCOMPLETE_TRAVERSAL / MISSING_IR instead. Conservative REJECT-direction evidence, never
         * cleared.
         */
        UNTRACKABLE_CONTAINER
    }

    /**
     * One incomplete-fact record: the reason class, the site's method, and the site's bci (the candidate-facts line's
     * grain). Equality/hashCode are exactly the record semantics over (reason, method, bci).
     */
    static final class IncompleteFact {
        final IncompleteReason reason;
        final AnalysisMethod method;
        final int bci;

        IncompleteFact(IncompleteReason reason, AnalysisMethod method, int bci) {
            this.reason = reason;
            this.method = method;
            this.bci = bci;
        }

        IncompleteReason reason() {
            return reason;
        }

        AnalysisMethod method() {
            return method;
        }

        int bci() {
            return bci;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!(obj instanceof IncompleteFact other)) {
                return false;
            }
            return bci == other.bci && reason == other.reason && method == other.method;
        }

        @Override
        public int hashCode() {
            int result = reason.hashCode();
            result = 31 * result + (method != null ? method.hashCode() : 0);
            result = 31 * result + bci;
            return result;
        }

        @Override
        public String toString() {
            return "IncompleteFact[reason=" + reason + ", method=" + method + ", bci=" + bci + "]";
        }
    }

    /**
     * One recorded usage. {@code dispatchOwner}: for a RECEIVER usage of a tracked
     * accumulator atom, the declaring class of the method the JVM selects on the accumulator's exact class
     * ({@link AccumulatorWhitelist#dispatchedOwner}); the accumulator tables classify the usage by it instead of the
     * site's declared owner. Null for every other usage (the site's own declaring class applies).
     */
    record UsageFact(SugVertex usageSite, UsageRole role, int argumentIndex, String dispatchOwner) {
        UsageFact(SugVertex usageSite, UsageRole role, int argumentIndex) {
            this(usageSite, role, argumentIndex, null);
        }
    }

    /**
     * Whether this usage is safe for String View candidacy, mirroring {@link StringViewHeuristic#validateUsages}. A
     * usage blocks only when the candidate is the receiver of a content-reading operation not in
     * {@link StringViewWhitelist}. A parameter usage is safe: the candidate is the payload being accumulated,
     * concatenated or stringified, and no such operation reads its {@code value()} as the receiver (the
     * {@code role == PARAMETER -> continue} skip of {@code validateUsages}).
     */
    static boolean correctedUsageSafe(UsageFact uf) {
        if (uf.role() != UsageRole.RECEIVER) {
            // PARAMETER and NONE roles are not content operations on the candidate.
            return true;
        }
        SugVertex site = uf.usageSite();
        if (site == null) {
            // Cannot verify the whitelist: conservatively unsafe.
            return false;
        }
        return StringViewWhitelist.isWhitelisted(site.getMethodName(), site.getDeclaringClass(), site.getMethodSignature());
    }

    /**
     * Whether the usage-site vertex is a {@link #SAFE_SINKS} method. The one reader of the sink set is
     * {@code AdmissionProof}, which evaluates safe-sink evidence on the emitted usage tags (there is no emit-side
     * mask).
     */
    static boolean isSafeSinkMethod(SugVertex site) {
        String decl = site.getDeclaringClass();
        String name = site.getMethodName();
        String sig = site.getMethodSignature();
        if (decl == null || name == null || sig == null) {
            return false;
        }
        if (SAFE_SINKS.contains(decl + "#" + name + "(" + sig + ")")) {
            return true;
        }
        // the JMH Blackhole's Object sinks (the walk never enters them).
        // The site's signature is the parameter list only; the sinks are void with one Object parameter.
        return StringAtoms.JMH_BLACKHOLE_SINK && (StringAtoms.isJmhBlackholeSink(false, decl, name, "(" + sig + ")V") || StringAtoms.isJmhBlackholeSink(true, decl, name, "(" + sig + ")V"));
    }
}
