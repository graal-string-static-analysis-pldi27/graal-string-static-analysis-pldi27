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
import java.util.BitSet;
import java.util.Collection;
import java.util.Comparator;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.oracle.graal.pointsto.flow.InvokeTypeFlow;
import com.oracle.graal.pointsto.flow.TypeFlow;

public final class LazyConcatHeuristic implements Heuristic {

    private final List<String> rejections = new ArrayList<>();
    private final List<String> warnings = new ArrayList<>();
    private int candidateCount;
    private int concatExpressionTotal;
    /** The no-usage warning of the candidate being validated (recorded only once it is admitted). */
    private String pendingWarning;

    @Override
    public List<InstrumentationDecision> apply(StringUtilizationGraph graph) {
        UsageSourceBuilder.ensureBuilt(graph);
        rejections.clear();
        warnings.clear();
        candidateCount = 0;
        RAW_FLOW_SITES.set(0);
        concatExpressionTotal = 0;
        List<InstrumentationDecision> decisions = new ArrayList<>();
        for (SugVertex v : graph.getVertices()) {
            // A join source call (LazyConcatMint's source table) is a candidate of this heuristic too
            boolean join = LazyConcatMint.isJoinSource(v);
            if (v.getNodeType() != SugNodeType.CONCAT_EXPRESSION && !join) {
                continue;
            }
            if (!join) {
                concatExpressionTotal++;
            }
            String kind = join ? "join" : "concat";
            String enc = StringAnalysisPolicy.enclosingClassName(v);
            if (enc == null || !StringAnalysisPolicy.isUserCodeClass(enc)) {
                continue;
            }
            candidateCount++;
            // The variant is computed first — the whitelist is per variant. A usage rejection
            // is reported before "too few dynamic operands".
            String variant = computeVariant(v);
            pendingWarning = null;
            String rejection = validateReachable(graph, v, builtRepresentation(v, variant), kind);
            if (rejection != null) {
                rejections.add("REJECT V" + v.getId() + " (" + kind + " @ " + v.getSourceLocation() + "): " + rejection);
                continue;
            }
            if (variant == null) {
                rejections.add("REJECT V" + v.getId() + " (" + kind + " @ " + v.getSourceLocation() + "): too few dynamic operands for any lazy variant");
                continue;
            }
            if (pendingWarning != null) {
                warnings.add(pendingWarning);
            }
            if (LazyConcatMint.MINT_LOG) {
                System.out.println("[lc-mintlog] child " + v.getSourceLocation() + " variant=" + variant + " dyn=" + v.getDynamicOperandCount() +
                                " minted=" + LazyConcatMint.mintedRep(v, variant));
            }
            decisions.add(new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, variant));
        }
        System.out.println("[string-analysis] lazy-concat: raw-flow-only lazy-operand sites " + RAW_FLOW_SITES.get());
        return decisions;
    }

    public List<String> getRejections() {
        return rejections;
    }

    /** The no-usage warnings of admitted candidates. */
    public List<String> getWarnings() {
        return warnings;
    }

    public int getCandidateCount() {
        return candidateCount;
    }

    public int getConcatExpressionTotal() {
        return concatExpressionTotal;
    }

    /**
     * The usage check of a StringJoiner extraction (rep {@code InterleavedStringArray.ofJoiner}): the join-source check
     * with variant INTERLEAVED. Null = admit.
     */
    String validateJoinerExtraction(StringUtilizationGraph graph, SugVertex x) {
        pendingWarning = null;
        String why = validateReachable(graph, x, LazyConcatMint.INTERLEAVED, "joiner");
        if (why == null && pendingWarning != null) {
            warnings.add(pendingWarning);
        }
        return why;
    }

    private String validateReachable(StringUtilizationGraph graph, SugVertex candidate, String variant, String kind) {
        if (candidate.isIncompleteTrace()) {
            return "incomplete downstream trace — conservatively rejected";
        }
        com.oracle.graal.pointsto.meta.AnalysisMethod candidateMethod = candidate.getEnclosingMethod();
        String rejection = validateUsages(graph, candidate, candidate, candidateMethod, new HashSet<>(), variant);
        if (rejection != null) {
            return rejection;
        }
        String rawRejection = validateReachableRawFlow(graph, candidate, variant);
        if (rawRejection != null) {
            return rawRejection;
        }
        if (AdmissionProof.hasNoUsage(candidate)) {
            // The no-usage detector: the warning is recorded once the candidate is admitted
            pendingWarning = AdmissionProof.noUsageWarning(candidate, kind);
        }
        return null; // no usage is no rejection reason (see AdmissionProof)
    }

    private String validateUsages(StringUtilizationGraph graph, SugVertex candidate, SugVertex creationSite, com.oracle.graal.pointsto.meta.AnalysisMethod candidateMethod,
                    Set<SugVertex> visited, String variant) {
        if (!visited.add(creationSite)) {
            return null;
        }
        String rejection = null;
        BitSet tags = creationSite.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            if (tag.role() == UsageRole.PARAMETER) {
                continue;
            }
            SugVertex usage = tag.usageSite();
            if (isInsideWhitelistedMethod(usage, candidateMethod, variant)) {
                continue;
            }
            if (usage.getNodeType() == SugNodeType.STRING_METHOD_CALL) {
                if (StringAnalysisPolicy.isInternalCall(usage)) {
                    rejection = minRejection(rejection, validateUsages(graph, candidate, usage, candidateMethod, visited, variant));
                    continue;
                }
                if (!LazyConcatWhitelist.isWhitelisted(usage.getMethodName(), usage.getDeclaringClass(), usage.getMethodSignature(), variant)) {
                    rejection = minRejection(rejection, "non-whitelisted call " + usage.getDeclaringClass() + "." + usage.getMethodName() +
                                    "(" + usage.getMethodSignature() + ") @ " + usage.getSourceLocation() +
                                    " (V" + usage.getId() + ")");
                }
                continue;
            }
            if (usage.getNodeType() == SugNodeType.JDK_LIBRARY_CALL) {
                if (StringAnalysisPolicy.isInternalCall(usage)) {
                    rejection = minRejection(rejection, validateUsages(graph, candidate, usage, candidateMethod, visited, variant));
                    continue;
                }
                if (!LazyConcatWhitelist.isWhitelisted(usage.getMethodName(), usage.getDeclaringClass(), usage.getMethodSignature(), variant)) {
                    rejection = minRejection(rejection, "non-whitelisted JDK library call " + usage.getDeclaringClass() + "." + usage.getMethodName() +
                                    "(" + usage.getMethodSignature() + ") @ " + usage.getSourceLocation() +
                                    " (V" + usage.getId() + ")");
                }
                continue;
            }
            if (usage.getNodeType() == SugNodeType.CONCAT_EXPRESSION) {
                if (isLazyOperandOk(usage, variant)) {
                    // Nested concat (isLazyOperandOk): the outer site is recorded on the candidate (the readers' key),
                    // also when reached through an internal call, for the nested-concat pass and LazyOperandPairing
                    candidate.addLazyOperandSite(usage.getSourceLocation());
                    continue;
                }
                rejection = minRejection(rejection, "concat expression @ " + usage.getSourceLocation() + " (V" + usage.getId() + ")");
            }
        }
        return rejection;
    }

    private static String minRejection(String a, String b) {
        if (a == null) {
            return b;
        }
        if (b == null) {
            return a;
        }
        return a.compareTo(b) <= 0 ? a : b;
    }

    private static boolean isInsideWhitelistedMethod(SugVertex v, com.oracle.graal.pointsto.meta.AnalysisMethod candidateMethod, String variant) {
        com.oracle.graal.pointsto.meta.AnalysisMethod enc = v.getEnclosingMethod();
        if (enc == null || enc == candidateMethod) {
            return false;
        }
        return LazyConcatWhitelist.isWhitelistedMethod(enc, variant);
    }

    /** Lazy-operand sites recorded by the raw-flow BFS only (child log; expected 0 when the SUG is complete). */
    static final java.util.concurrent.atomic.AtomicInteger RAW_FLOW_SITES = new java.util.concurrent.atomic.AtomicInteger();

    private String validateReachableRawFlow(StringUtilizationGraph graph, SugVertex candidate, String variant) {
        TypeFlow<?> sourceFlow = candidate.getSourceFlow();
        if (!(sourceFlow instanceof InvokeTypeFlow inv)) {
            return null;
        }
        TypeFlow<?> returnFlow = inv.getActualReturn();
        if (returnFlow == null) {
            return null;
        }
        com.oracle.graal.pointsto.meta.AnalysisMethod candidateMethod = sourceFlow.method();
        Set<TypeFlow<?>> visited = new HashSet<>();
        Deque<TypeFlow<?>> queue = new ArrayDeque<>();
        queue.add(returnFlow);
        visited.add(returnFlow);
        while (!queue.isEmpty()) {
            TypeFlow<?> f = queue.pollFirst();
            Collection<TypeFlow<?>> uses = f.getUses();
            if (uses == null) {
                continue;
            }
            for (TypeFlow<?> use : uses) {
                SugVertex useVertex = graph.getVertex(use);
                if (useVertex != null && useVertex != candidate) {
                    if (useVertex.getNodeType() == SugNodeType.STRING_METHOD_CALL) {
                        if (!StringAnalysisPolicy.isInternalCall(useVertex) &&
                                        !LazyConcatWhitelist.isWhitelisted(useVertex.getMethodName(), useVertex.getDeclaringClass(), useVertex.getMethodSignature(), variant)) {
                            return "non-whitelisted call (raw-flow BFS) " + useVertex.getDeclaringClass() + "." + useVertex.getMethodName() +
                                            "(" + useVertex.getMethodSignature() + ") @ " + useVertex.getSourceLocation() +
                                            " (V" + useVertex.getId() + ")";
                        }
                    }
                    if (useVertex.getNodeType() == SugNodeType.JDK_LIBRARY_CALL) {
                        if (!StringAnalysisPolicy.isInternalCall(useVertex) &&
                                        !LazyConcatWhitelist.isWhitelisted(useVertex.getMethodName(), useVertex.getDeclaringClass(), useVertex.getMethodSignature(), variant)) {
                            return "non-whitelisted JDK library call (raw-flow BFS) " + useVertex.getDeclaringClass() + "." + useVertex.getMethodName() +
                                            "(" + useVertex.getMethodSignature() + ") @ " + useVertex.getSourceLocation() +
                                            " (V" + useVertex.getId() + ")";
                        }
                    }
                    if (useVertex.getNodeType() == SugNodeType.CONCAT_EXPRESSION && !candidate.getLazyOperandSites().contains(useVertex.getSourceLocation())) {
                        // A concat the raw flow reaches but the usage tags did not record. LazyOperandPairing reads the
                        // recorded sites as the complete set of the candidate's outers: record it as validateUsages
                        // would, otherwise reject.
                        if (!isLazyOperandOk(useVertex, variant)) {
                            return "concat expression (raw-flow BFS) @ " + useVertex.getSourceLocation() + " (V" + useVertex.getId() + ")";
                        }
                        candidate.addLazyOperandSite(useVertex.getSourceLocation());
                        RAW_FLOW_SITES.incrementAndGet();
                    }
                }
                if (isWhitelistedLeaf(use, candidateMethod, variant)) {
                    continue;
                }
                if (visited.add(use)) {
                    queue.add(use);
                }
            }
        }
        return null;
    }

    private static boolean isWhitelistedLeaf(TypeFlow<?> flow, com.oracle.graal.pointsto.meta.AnalysisMethod candidateMethod, String variant) {
        com.oracle.graal.pointsto.meta.AnalysisMethod useMethod = flow.method();
        if (useMethod == null || useMethod == candidateMethod) {
            return false;
        }
        return LazyConcatWhitelist.isWhitelistedMethod(useMethod, variant);
    }

    /**
     * The representation the replacement plugin really builds for this site; the whitelist is keyed on it, not on the
     * variant label. Computed by {@link LazyConcatMint#mintedRep}, the function the replacement lowers by (a separate
     * copy could disagree). A site the replacement does not replace keeps its label.
     */
    private static String builtRepresentation(SugVertex concat, String variant) {
        if (variant == null) {
            return variant;
        }
        String minted = LazyConcatMint.mintedRep(concat, variant);
        return minted != null ? minted : variant;
    }

    /** The default of {@code lc.lazyoperand}; a constant variable, so readers do not initialize this class. */
    static final int DEFAULT_LAZY_OPERAND_MODE = 2;

    /**
     * Nested concat: the knob {@code -Dsvm.stringanalysis.lc.lazyoperand} (default
     * {@link #DEFAULT_LAZY_OPERAND_MODE} = 2).
     * <ul>
     * <li>0 = every concat operand usage rejects a lazy candidate.</li>
     * <li>1 = a lazy candidate may be an operand of a non-copying indy concat ({@link #isLazyOperandOk}), whether that
     * outer is stock or itself an admitted LS site.</li>
     * <li>2 (default) = as 1, but no LS value may be an operand of another LS site: the inner is refused
     * ({@link #LS_NESTED_INNER}, {@code HeuristicOrchestrator.applyNestedLsRule}).</li>
     * <li>3 = as 2, but the outer LS site is refused instead ({@link #LS_NESTED_OUTER}).</li>
     * </ul>
     * An LS value as an operand of an ordinary (stock) concat stays admitted under 1, 2 and 3.
     */
    static final int LAZY_OPERAND_MODE = lazyOperandMode(Integer.getInteger("svm.stringanalysis.lc.lazyoperand", DEFAULT_LAZY_OPERAND_MODE));

    static final boolean LAZY_OPERAND = LAZY_OPERAND_MODE != 0;

    /** lazyoperand=2, the refusal of an LS candidate that is an operand of another kept LS site. */
    static final String LS_NESTED_INNER = "LS_NESTED_INNER";
    /** lazyoperand=3, the refusal of an LS site that has a kept LS candidate as an operand. */
    static final String LS_NESTED_OUTER = "LS_NESTED_OUTER";

    static int lazyOperandMode(int v) {
        if (v < 0 || v > 3) {
            throw new IllegalArgumentException("svm.stringanalysis.lc.lazyoperand must be 0, 1, 2 or 3: " + v);
        }
        return v;
    }

    /**
     * Nested concat: a lazy candidate as an operand of the indy concat {@code usage} is supported when (1) the
     * site's stock {@code StringConcatFactory} strategy never copies an operand ({@code SugVertex#isScfNoCopy}, the
     * rule {@code StringAtoms.scfCopiesOperand}: it reads the operand through {@code length()}, {@code coder()},
     * {@code getBytes(byte[],int,byte)} and {@code toString()} only) and (2) the built rep overrides the protected
     * {@code getBytes(byte[],int,byte)} (every lazy rep, RopeString included). Both lowerings of the outer site are
     * then sound: the stock strategy reads only overridden or field-exact methods, and an admitted outer lazy concat
     * reads the candidate part through {@code length}/{@code charAt}/{@code getChars}/{@code coder}/{@code hashCode}
     * and value-null-total {@code childEquals} (every lazy rep overrides those).
     */
    static boolean isLazyOperandOk(SugVertex usage, String builtRep) {
        return LAZY_OPERAND && usage.isScfNoCopy() && builtRep != null &&
                        LazyConcatWhitelist.isWhitelisted("getBytes", "java.lang.String", LazyConcatWhitelist.PROTECTED_GETBYTES_SIG, builtRep);
    }

    private String computeVariant(SugVertex concat) {
        if (LazyConcatMint.isJoinSource(concat)) {
            return LazyConcatMint.INTERLEAVED; // a join: the result is an interleaved string (parts + delimiter)
        }
        List<SugVertex> operands = collectOperands(concat);
        int dynCount = concat.getDynamicOperandCount();
        boolean recordedShape = concat.getConcatRecipe() != null || "makeConcat".equals(concat.getMethodName());
        if (dynCount >= 1 && recordedShape && !concat.isStringConcatCall()) {
            // An indy site with a recorded shape is named by its TOTAL parts, the rep the replacement
            // mints (LazyConcatMint.shapeVariant). The empty-constant reject (a "" \2 constant) is kept.
            if (dynCount < 2 && hasEmptyConstantOperand(operands)) {
                return null;
            }
            return LazyConcatMint.shapeVariant(dynCount, concat.getConcatRecipe());
        }
        if (dynCount < 0) {
            dynCount = operands.size();
        }
        // One dynamic operand plus recipe constants (e.g. "const"+x): the total operand count is >= 2, so the site
        // is named by its total count. Only here does the total count override the dynamic count.
        if (dynCount < 2) {
            int totalCount = operands.size();
            if (totalCount < 2) {
                return null;
            }
            if (hasEmptyConstantOperand(operands)) {
                return null;
            }
            // By the total operand count, as the runtime plugin lowers by `totalParts`
            return switch (totalCount) {
                case 2 -> "ROPE";
                case 3 -> "THREE_WAY";
                case 4 -> "FIXED4";
                default -> isInterleavedRegular(operands) ? "INTERLEAVED" : "ARRAY_LAZY";
            };
        }
        return switch (dynCount) {
            case 2 -> "ROPE";
            case 3 -> "THREE_WAY";
            case 4 -> "FIXED4";
            default -> isInterleavedRegular(operands) ? "INTERLEAVED" : "ARRAY_LAZY";
        };
    }

    /**
     * Whether a constant operand is the empty literal (e.g. {@code ""+x} with {@code ""} a recipe constant): such a
     * candidate is rejected to avoid a slow empty-child ROPE. Dynamic operands that happen to be empty are left alone.
     */
    private static boolean hasEmptyConstantOperand(List<SugVertex> operands) {
        for (SugVertex op : operands) {
            if (op != null && op.getNodeType() == SugNodeType.STRING_LITERAL) {
                String text = op.getLiteralText();
                if (text != null && text.isEmpty()) {
                    return true;
                }
            }
        }
        return false;
    }

    private List<SugVertex> collectOperands(SugVertex concat) {
        List<SugEdge> concatEdges = new ArrayList<>();
        for (SugEdge e : concat.getInEdges()) {
            if (e.getEdgeType() == SugEdgeType.CONCAT_LEFT || e.getEdgeType() == SugEdgeType.CONCAT_RIGHT) {
                concatEdges.add(e);
            }
        }
        if (!concatEdges.isEmpty()) {
            concatEdges.sort(Comparator.comparingInt(SugEdge::getParamIndex));
            List<SugVertex> ops = new ArrayList<>(concatEdges.size());
            for (SugEdge e : concatEdges) {
                ops.add(e.getFrom());
            }
            return ops;
        }
        List<SugEdge> paramEdges = new ArrayList<>();
        for (SugEdge e : concat.getInEdges()) {
            if (e.getEdgeType() == SugEdgeType.PARAMETER) {
                paramEdges.add(e);
            }
        }
        paramEdges.sort(Comparator.comparingInt(SugEdge::getParamIndex));
        List<SugVertex> ops = new ArrayList<>(paramEdges.size());
        for (SugEdge e : paramEdges) {
            ops.add(e.getFrom());
        }
        return ops;
    }

    private static boolean isInterleavedRegular(List<SugVertex> operands) {
        int n = operands.size();
        if (n < 5 || (n & 1) == 0) {
            return false;
        }
        String separator = null;
        for (int i = 0; i < n; i++) {
            SugVertex op = operands.get(i);
            boolean constant = op != null && op.getNodeType() == SugNodeType.STRING_LITERAL && op.getLiteralText() != null;
            if ((i & 1) == 0) {
                if (constant) {
                    return false;
                }
            } else {
                if (!constant) {
                    return false;
                }
                String text = op.getLiteralText();
                if (separator == null) {
                    separator = text;
                } else if (!separator.equals(text)) {
                    return false;
                }
            }
        }
        return true;
    }
}