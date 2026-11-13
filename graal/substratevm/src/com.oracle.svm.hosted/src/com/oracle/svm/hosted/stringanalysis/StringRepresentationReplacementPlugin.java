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

import java.lang.invoke.MethodType;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ConcurrentHashMap;

import org.graalvm.collections.Pair;

import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.svm.common.meta.MultiMethod;
import com.oracle.svm.core.SubstrateOptions;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.RepConcat;
import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.core.stringrep.ThreeWayString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.hosted.code.SubstrateCompilationDirectives;
import com.oracle.svm.hosted.meta.HostedMethod;

import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.extended.NullCheckNode;
import jdk.graal.compiler.nodes.java.NewArrayNode;
import jdk.graal.compiler.nodes.java.StoreIndexedNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.core.common.type.ObjectStamp;
import jdk.graal.compiler.core.common.type.Stamp;
import jdk.vm.ci.meta.ConstantPool.BootstrapMethodInvocation;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * A {@link NodePlugin} for the {@link com.oracle.svm.core.ParsingReason#PointsToAnalysis} parse that replaces string
 * operations at profiled source locations ({@link RepresentationProfileHolder}):
 * (1) {@code convertInvokeDynamic}: a {@code makeConcat}/{@code makeConcatWithConstants} at a {@code LAZY_CONCAT} site
 * (any dynamic operand types) becomes a {@link LazyConcatFactory} call; each dynamic operand is converted at the site by
 * its static type (a typed {@code LazyConcatFactory.str} converter, no box). The rep is {@link LazyConcatMint#mintedRep}
 * by total parts (dynamic + recipe constants): 2 → {@link LazyConcatFactory#ropeInlinePrologue}, 3 → {@link LazyConcatFactory#threeWay}, 4 → {@link LazyConcatFactory#fixed4},
 * &ge;5 → {@link LazyConcatFactory#arrayLazy} or {@link LazyConcatFactory#interleaved} (a fresh {@code String[]}, handed
 * over). Recipe constants become {@link ConstantNode} parts.
 * (2) {@code handleInvoke}: {@code String.substring(int,int)}/{@code subSequence(int,int)}/{@code substring(int)} at a
 * {@code STRING_VIEW} site become {@link StringView#create(String, int, int)} / {@link StringView#create(String, int)},
 * at a {@code SINGLE_BYTE} site {@link SingleByteString#createFromSubstring(String, int)} (the admit proves a length-1
 * result); {@code String.valueOf(char)} at a {@code SINGLE_BYTE} site becomes
 * {@link SingleByteString#createFromChar(char)}; an accumulator {@code toString()} (any declared owner) at a
 * {@code STRING_VIEW ACCUMULATOR_VIEW} site becomes {@code StringView.create(<the entry's exact class>)} behind the
 * zero-cost exact filter.
 * (3) {@code handleLoadConstant}: a length-1 String {@code ldc} at a {@code SINGLE_BYTE} site becomes
 * {@link SingleByteString#create(byte)}.
 *
 * The replacement must happen in the {@code PointsToAnalysis} parse: AOT compilation decodes the encoded analysis graph
 * ({@code CompilationInfo.createGraph} + {@code GraphDecoder}) instead of re-parsing bytecode. Sites are keyed by
 * {@code "file:line"} from {@code b.getMethod().asStackTraceElement(b.bci())}, as in the capture plugin; sites without a
 * matching {@link ProfileEntry} are untouched.
 */
public final class StringRepresentationReplacementPlugin implements NodePlugin {

    private static final String STRING_CONCAT_FACTORY = "java.lang.invoke.StringConcatFactory";
    private static final String STRING_CLASS = "java.lang.String";

    private static final char RECIPE_DYNAMIC_TAG = '\u0001';
    private static final char RECIPE_CONSTANT_TAG = '\u0002';

    private volatile ResolvedJavaMethod ropeCreateMethod;
    private volatile ResolvedJavaMethod threeWayCreateMethod;
    private volatile ResolvedJavaMethod fixedConcat4CreateMethod;
    private volatile ResolvedJavaMethod arrayLazyCreateMethod;
    private volatile ResolvedJavaMethod interleavedCreateMethod;
    private volatile ResolvedJavaMethod stringViewCreateMethod;
    private volatile ResolvedJavaMethod stringViewCreate1Method;
    private volatile ResolvedJavaMethod stringViewCreateViewMethod;
    private volatile ResolvedJavaMethod stringViewCreateView1Method;
    private volatile ResolvedJavaMethod singleByteCreateMethod;
    private volatile ResolvedJavaMethod singleByteCreateFromSubstringMethod;
    private volatile ResolvedJavaMethod singleByteCreateFromCharMethod;
    /** The LazyConcatFactory method per minted rep name (LazyConcatMint.factoryMethod), resolved once. */
    private final ConcurrentHashMap<String, ResolvedJavaMethod> lazyFactoryByRep = new ConcurrentHashMap<>();
    /** The LazyConcatFactory.str converter per operand type name (LazyConcatMint.converterMethod). */
    private final ConcurrentHashMap<String, ResolvedJavaMethod> converterByType = new ConcurrentHashMap<>();
    /** The join factory per join source parameter signature. */
    private final ConcurrentHashMap<String, ResolvedJavaMethod> joinFactoryBySig = new ConcurrentHashMap<>();

    @Override
    public Pair<ResolvedJavaMethod, ValueNode[]> convertInvokeDynamic(GraphBuilderContext b, BootstrapMethodInvocation m) {
        try {
            ResolvedJavaMethod boot = m.getMethod();
            String decl = boot.getDeclaringClass().toJavaName();
            String name = boot.getName();
            if (!decl.equals(STRING_CONCAT_FACTORY)) {
                return null;
            }
            boolean isMakeConcat = name.equals("makeConcat");
            boolean isMakeConcatWithConstants = name.equals("makeConcatWithConstants");
            if (!isMakeConcat && !isMakeConcatWithConstants) {
                return null;
            }
            if (!hasDecisionSource() && isForkedChild()) {
                // The child keeps the indy lowering, so the concat terminal sees the designed form
                return null;
            }
            if (!hasDecisionSource()) {
                return null;
            }
            String loc = sourceLocation(b);
            String copyShape = RepresentationProfileHolder.getInstance().getConcatCopyShape(loc);
            if (copyShape != null) {
                // A copying site an admitted view reaches: RepConcat, or the build fails (never stock here)
                return lowerCopyIndy(b, m, loc, copyShape);
            }
            ProfileEntry entry = lookupEntry(loc, OptimizationType.LAZY_CONCAT);
            if (entry == null || StringAnalysisSingleByteOnly()) {
                return null;
            }
            // KT precision, pairing contract (1): an inner is lowered only when every outer it is paired with is
            Pair<ResolvedJavaMethod, ValueNode[]> lowered = lazyPairOutersLowered(loc) ? lowerLazyIndy(b, m, loc, entry) : null;
            if (lowered == null && isPairedLazyOuter(loc)) {
                // Pairing contract (2): an inner's lazy lowering relies on this site being lowered lazily (the child left
                // its kind out of the concat group); a stock lowering here would hand it to the stock concat machinery
                throw new PairingViolation("[string-analysis] paired lazy outer declined at " + loc + " (variant " + entry.getVariant() +
                                "): the profile's LAZY_PAIR inners rely on its lazy lowering; rebuild with -J-Dsvm.stringanalysis.ic.ktprecise=0");
            }
            return lowered;
        } catch (PostPopFailure | PairingViolation | ConcatCopyFailure e) {
            throw e;
        } catch (Throwable t) {
            return null;
        }
    }

    /**
     * Lowers a {@code CONCAT_COPY} site (a copying indy concat that an admitted String View reaches) to one static call of
     * {@code RepConcat.concat1/concat2}, the overload chosen by the indy's declared parameter types. The shape is
     * re-derived from the bootstrap ({@link StringAtoms#scfCopyShape}); a mismatch, unreadable site or resolve failure
     * fails the build (declining would run the stock copying strategy on the view). No converter invokes, so no
     * intermediate frame state and no deopt-target decline.
     */
    private static Pair<ResolvedJavaMethod, ValueNode[]> lowerCopyIndy(GraphBuilderContext b, BootstrapMethodInvocation m, String loc, String copyShape) {
        try {
            return lowerCopyIndy0(b, m, loc, copyShape);
        } catch (Throwable t) {
            throw asConcatCopyFailure(loc, t);
        }
    }

    /**
     * Pinned by JUnit: any failure inside {@link #lowerCopyIndy} fails the build, never the stock fallback of
     * {@code convertInvokeDynamic}'s generic catch.
     */
    static RuntimeException asConcatCopyFailure(String loc, Throwable t) {
        if (t instanceof ConcatCopyFailure c) {
            return c;
        }
        return new ConcatCopyFailure("[string-analysis] CONCAT_COPY " + loc + ": lowering failed: " + t, t);
    }

    private static Pair<ResolvedJavaMethod, ValueNode[]> lowerCopyIndy0(GraphBuilderContext b, BootstrapMethodInvocation m, String loc, String copyShape) {
        MethodType methodType = resolveMethodType(b, m);
        if (methodType == null) {
            throw new ConcatCopyFailure("[string-analysis] CONCAT_COPY " + loc + ": the indy's MethodType is unreadable");
        }
        int n = methodType.parameterCount();
        boolean[] prim = new boolean[n];
        Class<?>[] params = new Class<?>[n];
        for (int i = 0; i < n; i++) {
            params[i] = methodType.parameterType(i);
            prim[i] = params[i].isPrimitive();
        }
        String bootName = m.getMethod().getName();
        String recipe = "makeConcatWithConstants".equals(bootName) ? readRecipe(b, m) : null;
        StringAtoms.CopyShape derived = StringAtoms.scfCopyShape(bootName, recipe, prim);
        if (!derived.name().equals(copyShape)) {
            throw new ConcatCopyFailure("[string-analysis] CONCAT_COPY " + loc + ": the profile says " + copyShape + ", the site's bootstrap is " + derived);
        }
        Method factory;
        try {
            factory = repConcatFactory(params);
        } catch (NoSuchMethodException e) {
            throw new ConcatCopyFailure("[string-analysis] CONCAT_COPY " + loc + ": no RepConcat factory for " + methodType, e);
        }
        ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(factory);
        concatCopyLowered.incrementAndGet();
        return Pair.create(resolved, b.popArguments(n));
    }

    /** The RepConcat factory of a UNARY/BINARY site's reference parameter types (pure; pinned by JUnit). */
    static Method repConcatFactory(Class<?>[] params) throws NoSuchMethodException {
        Class<?>[] sig = new Class<?>[params.length];
        for (int i = 0; i < params.length; i++) {
            if (params[i].isPrimitive()) {
                throw new NoSuchMethodException("primitive operand " + params[i]);
            }
            sig[i] = params[i] == String.class ? String.class : Object.class;
        }
        if (sig.length == 1) {
            return RepConcat.class.getDeclaredMethod("concat1", sig);
        }
        if (sig.length == 2) {
            return RepConcat.class.getDeclaredMethod("concat2", sig);
        }
        throw new NoSuchMethodException("arity " + sig.length);
    }

    /** The number of indy sites lowered with RepConcat (parses, print-only). */
    static final java.util.concurrent.atomic.AtomicInteger concatCopyLowered = new java.util.concurrent.atomic.AtomicInteger();

    /** A CONCAT_COPY site that cannot be lowered: fails the build (never the stock copying strategy). */
    static final class ConcatCopyFailure extends RuntimeException {
        private static final long serialVersionUID = 1L;

        ConcatCopyFailure(String message) {
            super(message);
        }

        ConcatCopyFailure(String message, Throwable cause) {
            super(message, cause);
        }
    }

    /** The lazy lowering of the indy concat at {@code loc} with the LAZY_CONCAT profile {@code entry}; null = stock. */
    private Pair<ResolvedJavaMethod, ValueNode[]> lowerLazyIndy(GraphBuilderContext b, BootstrapMethodInvocation m, String loc, ProfileEntry entry) {
        try {
            String variant = entry.getVariant();
            if (!LazyConcatMint.isLazyVariant(variant)) {
                return null;
            }

            if (canBeDeoptTarget(b)) {
                // The converter invokes' stateAfter (next bci, a converted operand on the stack) is not a state a deopt
                // may resume in: decline where a deopt can happen.
                return null;
            }

            MethodType methodType = resolveMethodType(b, m);
            if (methodType == null) {
                return null;
            }
            int dynamicCount = methodType.parameterCount();
            if (dynamicCount < 1) {
                return null;
            }

            String recipe = null;
            if (m.getMethod().getName().equals("makeConcatWithConstants")) {
                recipe = readRecipe(b, m);
            }

            // Decide the shape before popping the operands: every early null return leaves the stack untouched for the
            // default indy lowering. LazyConcatMint.mintedRep is the one function the child also names its reps with, so
            // the profile names exactly the class built here. ROPE/THREE_WAY/FIXED4 need 2/3/4 total parts, ArrayLazy is
            // the catch-all, INTERLEAVED needs a single-delimiter recipe; null = not replaced.
            String minted = LazyConcatMint.mintedRep(variant, dynamicCount, recipe);
            if (minted == null) {
                return null;
            }
            ResolvedJavaMethod factory = resolveLazyFactory(b, minted);
            if (factory == null) {
                return null;
            }
            // Resolve the recipe parts and run every declining check before the pop: a \2 constant that is not a String,
            // a \1 count other than the operand count, or a part count that does not fit the rep's arity declines with the
            // stack untouched (a null return after the pop would pop the indy's operands twice).
            List<Object> pieces = null;
            if (!LazyConcatMint.INTERLEAVED.equals(minted)) {
                pieces = recipePieces(b, m, recipe, dynamicCount);
                if (pieces == null) {
                    return null;
                }
                int arity = fixedArity(minted);
                if (arity > 0 && pieces.size() != arity) {
                    return null;
                }
            }

            if (LazyConcatMint.MINT_LOG) {
                System.out.println("[lc-mintlog] parent " + loc + " variant=" + variant + " dyn=" + dynamicCount + " totalParts=" +
                                LazyConcatMint.totalParts(recipe, dynamicCount) + " minted=" + minted + " factory=" + factory.getName());
            }

            Class<?>[] paramTypes = new Class<?>[dynamicCount];
            for (int i = 0; i < dynamicCount; i++) {
                paramTypes[i] = methodType.parameterType(i);
            }

            // The converters are resolved before the pop too (a failure declines the site)
            ResolvedJavaMethod[] converters = new ResolvedJavaMethod[dynamicCount];
            for (int i = 0; i < dynamicCount; i++) {
                converters[i] = resolveConverter(b, paramTypes[i]);
                if (converters[i] == null) {
                    return null;
                }
            }

            ValueNode[] operands = b.popArguments(dynamicCount);
            try {
                // Convert each dynamic operand in order by its static type (JLS 5.1.11, no box): a primitive by its typed
                // converter, a String by s == null ? "null" : s (inlined: keeps the operand's type state, no toString()),
                // any other reference by the JDK's stringOf(Object) (a null toString() -> "null"). Each converter call is
                // appended at the indy's bci on the post-pop stack (the state an exception of the concat sees); its
                // stateAfter is valid only because the method cannot deopt (canBeDeoptTarget).
                ValueNode[] strOperands = new ValueNode[dynamicCount];
                for (int i = 0; i < dynamicCount; i++) {
                    boolean inline = paramTypes[i] == String.class || paramTypes[i] == boolean.class;
                    b.handleReplacedInvoke(InvokeKind.Static, converters[i], new ValueNode[]{operands[i]}, inline);
                    strOperands[i] = b.pop(JavaKind.Object);
                }

                if (LazyConcatMint.INTERLEAVED.equals(minted)) {
                    String delimiter = LazyConcatMint.interleavedDelimiter(recipe, dynamicCount);
                    ValueNode arrayNode = createStringArray(b, strOperands);
                    ValueNode delimNode = b.add(ConstantNode.forConstant(
                                    b.getSnippetReflection().forObject(delimiter), b.getMetaAccess()));
                    return Pair.create(factory, new ValueNode[]{arrayNode, delimNode});
                }

                List<ValueNode> parts = new ArrayList<>(pieces.size());
                for (Object piece : pieces) {
                    if (piece instanceof Integer dynamicIndex) {
                        parts.add(strOperands[dynamicIndex]);
                    } else if (piece instanceof JavaConstant constant) {
                        parts.add(b.add(ConstantNode.forConstant(constant, b.getMetaAccess())));
                    } else {
                        parts.add(b.add(ConstantNode.forConstant(
                                        b.getSnippetReflection().forObject((String) piece), b.getMetaAccess())));
                    }
                }

                switch (minted) {
                    case LazyConcatMint.ROPE:
                        return Pair.create(factory, new ValueNode[]{parts.get(0), parts.get(1)});
                    case LazyConcatMint.THREE_WAY:
                        return Pair.create(factory, new ValueNode[]{parts.get(0), parts.get(1), parts.get(2)});
                    case LazyConcatMint.FIXED4:
                        return Pair.create(factory, new ValueNode[]{parts.get(0), parts.get(1), parts.get(2), parts.get(3)});
                    default:
                        ValueNode arrayNode = createStringArray(b, parts.toArray(new ValueNode[0]));
                        return Pair.create(factory, new ValueNode[]{arrayNode});
                }
            } catch (Throwable t) {
                // The operands are popped: declining now would pop them again in the stock lowering. Fail the build.
                throw new PostPopFailure("[string-analysis] lazy-concat replacement failed after popping the operands at " + loc, t);
            }
        } catch (PostPopFailure e) {
            throw e;
        } catch (Throwable t) {
            return null;
        }
    }

    /**
     * Whether the parsed method (or its inlining root) can be deoptimized into: a non-original multi-method or a method
     * registered for deopt testing (the criterion of {@code AnalysisGraphBuilderPhase}'s exception-state pruning). A
     * plain AOT image answers false for every method.
     */
    private static boolean canBeDeoptTarget(GraphBuilderContext b) {
        ResolvedJavaMethod[] methods = {b.getMethod(), b.getGraph().method()};
        for (ResolvedJavaMethod method : methods) {
            if (method instanceof MultiMethod multiMethod) {
                if (!multiMethod.isOriginalMethod()) {
                    return true;
                }
                if ((method instanceof AnalysisMethod || method instanceof HostedMethod) &&
                                SubstrateCompilationDirectives.singleton().isRegisteredForDeoptTesting(method)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** KT precision: a paired lazy outer ({@link RepresentationProfile#isPairedOuter}) that would be lowered stock. */
    private static final class PairingViolation extends RuntimeException {
        private static final long serialVersionUID = 1L;

        PairingViolation(String message) {
            super(message);
        }
    }

    /** KT precision, pairing contract (1): {@link RepresentationProfile#pairedOutersLowered}. */
    private static boolean lazyPairOutersLowered(String loc) {
        return !RepresentationProfileHolder.hasProfile() || RepresentationProfileHolder.getInstance().pairedOutersLowered(loc);
    }

    /** KT precision, pairing contract (2): {@link RepresentationProfile#isPairedOuter}. */
    private static boolean isPairedLazyOuter(String loc) {
        return RepresentationProfileHolder.hasProfile() && RepresentationProfileHolder.getInstance().isPairedOuter(loc);
    }

    /** A failure after the indy's operands were popped: it must fail the build, never fall back to the stock lowering. */
    private static final class PostPopFailure extends RuntimeException {
        private static final long serialVersionUID = 1L;

        PostPopFailure(String message, Throwable cause) {
            super(message, cause);
        }
    }

    /** The fixed part count of a minted lazy rep's factory, or -1 for the array-based reps. */
    private static int fixedArity(String minted) {
        return switch (minted) {
            case LazyConcatMint.ROPE -> 2;
            case LazyConcatMint.THREE_WAY -> 3;
            case LazyConcatMint.FIXED4 -> 4;
            default -> -1;
        };
    }

    /**
     * The parts of a concat recipe in order: a {@code String} per maximal literal run, an {@code Integer} (the dynamic
     * operand index) per {@code \1}, the {@code JavaConstant} per {@code \2} constant. {@code recipe == null}
     * ({@code makeConcat}): every part dynamic. {@code null} = the site must not be replaced (a {@code \2} constant that
     * is missing or not a non-null String, or a {@code \1} count other than {@code dynamicCount}).
     */
    private static List<Object> recipePieces(GraphBuilderContext b, BootstrapMethodInvocation m, String recipe, int dynamicCount) {
        List<Object> pieces = new ArrayList<>();
        if (recipe == null) {
            for (int i = 0; i < dynamicCount; i++) {
                pieces.add(i);
            }
            return pieces;
        }
        List<JavaConstant> staticArgs = m.getStaticArguments();
        int dynamicIndex = 0;
        int constantIndex = 1; // static argument 0 is the recipe itself
        StringBuilder literal = new StringBuilder();
        for (int i = 0; i < recipe.length(); i++) {
            char c = recipe.charAt(i);
            if (c != RECIPE_DYNAMIC_TAG && c != RECIPE_CONSTANT_TAG) {
                literal.append(c);
                continue;
            }
            if (literal.length() > 0) {
                pieces.add(literal.toString());
                literal.setLength(0);
            }
            if (c == RECIPE_DYNAMIC_TAG) {
                if (dynamicIndex >= dynamicCount) {
                    return null;
                }
                pieces.add(dynamicIndex++);
            } else {
                if (staticArgs == null || constantIndex >= staticArgs.size()) {
                    return null;
                }
                JavaConstant sc = staticArgs.get(constantIndex++);
                if (sc == null || sc.getJavaKind() != JavaKind.Object || sc.isNull() ||
                                b.getSnippetReflection().asObject(String.class, sc) == null) {
                    return null;
                }
                pieces.add(sc);
            }
        }
        if (literal.length() > 0) {
            pieces.add(literal.toString());
        }
        return dynamicIndex == dynamicCount ? pieces : null;
    }

    private static boolean isForkedChild() {
        try {
            return SubstrateOptions.StringAnalysisFork.getValue();
        } catch (Throwable t) {
            return false;
        }
    }

    @Override
    public boolean handleInvoke(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (InlineCacheTrivialMethodNodePlugin.isFlatReentry(b, method)) {
            return false; // the IC's flat call re-parsed on the stock path
        }
        if (!hasDecisionSource()) {
            return false;
        }
        if (ZeroAdmitStock.active()) {
            return false; // a zero-admit profile compiles String as OFF does
        }
        try {
            String decl = method.getDeclaringClass().toJavaName();
            String name = method.getName();

            // Unified accumulator lowering: every accumulator toString extraction, whatever the declared owner, goes
            // through lowerAccumulatorExtraction (exact class from the profile entry, exact filter, snapshot factory).
            if (name.equals("toString") && args.length == 1 && !method.isStatic() && method.getSignature().getParameterCount(false) == 0) {
                ProfileEntry entry = lookupEntry(sourceLocation(b), OptimizationType.STRING_VIEW);
                if (entry != null && isAccumulatorVariant(entry.getVariant())) { // either accumulator variant
                    // An ACCUMULATOR_VIEW toString site ends here, lowered or declined; no later branch
                    // handles a non-String toString, so a declined site must not fall through to them
                    return !StringAnalysisSingleByteOnly() && lowerAccumulatorExtraction(b, method, args[0], entry);
                }
                // An admitted StringJoiner extraction ('<key> LAZY_CONCAT INTERLEAVED java.util.StringJoiner')
                ProfileEntry joinerEntry = lookupEntry(sourceLocation(b), OptimizationType.LAZY_CONCAT);
                if (joinerEntry != null && AccumulatorWhitelist.JOINER.equals(joinerEntry.getAccumulatorClass())) {
                    return !StringAnalysisSingleByteOnly() && lowerJoinerExtraction(b, method, args[0], joinerEntry);
                }
            }

            // An admitted element-source call (ElementSources' table; '<key> STRING_VIEW ELEMENT_VIEW[_STORED]');
            // the cheap row-name filter first (no signature string per parsed invoke)
            if (ElementSources.isRowName(name) && ElementSources.isSource(decl, name, joinParameterSignature(method))) {
                ProfileEntry elemEntry = lookupEntry(sourceLocation(b), OptimizationType.STRING_VIEW);
                if (elemEntry != null && ElementSources.isElementVariant(elemEntry.getVariant())) {
                    return !StringAnalysisSingleByteOnly() && lowerElementSource(b, method, args, elemEntry);
                }
            }

            if (!decl.equals(STRING_CLASS)) {
                return false;
            }

            if (name.equals(LazyConcatMint.JOIN_NAME) && method.isStatic() && args.length == 2) {
                return lowerJoin(b, method, args);
            }

            boolean isStringConcat = name.equals("concat") && args.length == 2;
            boolean isSubstring = isSubstringMethod(name) && args.length == 3;
            boolean isSubstring1 = name.equals("substring") && args.length == 2; // substring(I); there is no 1-arg subSequence
            boolean isValueOf = name.equals("valueOf") && args.length == 1 &&
                            (args[0].getStackKind() == JavaKind.Int || args[0].getStackKind() == JavaKind.Char) &&
                            method.getSignature().getParameterCount(false) == 1 &&
                            method.getSignature().getParameterType(0, null).getJavaKind() == JavaKind.Char;
            if (!isSubstring && !isSubstring1 && !isValueOf && !isStringConcat) {
                return false;
            }

            String loc = sourceLocation(b);

            if (isStringConcat) {
                if (StringAnalysisSingleByteOnly()) {
                    return false;
                }
                ProfileEntry lazyEntry = lookupEntry(loc, OptimizationType.LAZY_CONCAT);
                // The String.concat mint rule lives in LazyConcatMint too (the child names the same rep)
                if (lazyEntry == null || !LazyConcatMint.ROPE.equals(LazyConcatMint.mintedRepForStringConcat(lazyEntry.getVariant())) ||
                                !lazyPairOutersLowered(loc)) {
                    return false;
                }
                ResolvedJavaMethod factory = resolveStringConcatFactory(b);
                if (factory == null) {
                    return false;
                }
                // Preserve String.concat's NPE semantics (a null receiver NPEs on dispatch, the body NPE-checks the arg):
                // emit null checks before the ROPE factory, which would otherwise stringify nulls via String.valueOf.
                if (LazyConcatMint.MINT_LOG) {
                    System.out.println("[lc-mintlog] parent " + loc + " variant=" + lazyEntry.getVariant() + " dyn=2 totalParts=2 minted=ROPE factory=" + factory.getName());
                }
                b.add(new NullCheckNode(args[0]));
                b.add(new NullCheckNode(args[1]));
                b.handleReplacedInvoke(InvokeKind.Static, factory, new ValueNode[]{args[0], args[1]}, false);
                return true;
            }

            ProfileEntry entry = lookupEntry(loc, OptimizationType.STRING_VIEW);
            ProfileEntry singleByteEntry = lookupEntry(loc, OptimizationType.SINGLE_BYTE);
            if (entry == null && singleByteEntry == null) {
                return false;
            }

            if (isSubstring) {
                ValueNode receiver = args[0];
                if (isRepSubclassExact(receiver, b)) {
                    if (entry != null && !StringAnalysisSingleByteOnly()) {
                        ResolvedJavaType type = receiverTypeExact(receiver, b);
                        ResolvedJavaType stringViewType = b.getMetaAccess().lookupJavaType(StringView.class);
                        if (type != null && type.equals(stringViewType)) {
                            ResolvedJavaMethod factory = isStoredVariant(entry) ? resolveStoredFactory(b, "createViewStored", StringView.class, int.class, int.class)
                                            : resolveStringViewCreateView(b);
                            if (factory == null) {
                                return false;
                            }
                            b.handleReplacedInvoke(InvokeKind.Static, factory, args, false);
                            return true;
                        }
                    }
                    return false;
                }
                if (entry != null && !StringAnalysisSingleByteOnly()) {
                    ResolvedJavaMethod factory = isStoredVariant(entry) ? resolveStoredFactory(b, "createStored", String.class, int.class, int.class)
                                    : resolveStringViewCreate(b);
                    if (factory == null) {
                        return false;
                    }
                    b.handleReplacedInvoke(InvokeKind.Static, factory, args, false);
                    return true;
                }
                if (singleByteEntry != null) {
                    ResolvedJavaMethod factory = resolveSingleByteCreateFromSubstring(b);
                    if (factory == null) {
                        return false;
                    }
                    ValueNode[] factoryArgs = new ValueNode[]{args[0], args[1]};
                    b.handleReplacedInvoke(InvokeKind.Static, factory, factoryArgs, false);
                    return true;
                }
                return false;
            }

            if (isSubstring1) {
                // String.substring(I): as the 2-arg form. An exact-StringView receiver nests through
                // createView(StringView,int); any other receiver gets StringView.create(String,int) (end = the receiver's
                // virtual length(); a null receiver NPEs there, as virtual dispatch would); a SINGLE_BYTE site maps to
                // createFromSubstring(String,int) (the admit proves the result is the parent's last char). No other
                // exact rep receiver is replaced.
                ValueNode receiver = args[0];
                if (isRepSubclassExact(receiver, b)) {
                    if (entry != null && !StringAnalysisSingleByteOnly()) {
                        ResolvedJavaType type = receiverTypeExact(receiver, b);
                        ResolvedJavaType stringViewType = b.getMetaAccess().lookupJavaType(StringView.class);
                        if (type != null && type.equals(stringViewType)) {
                            ResolvedJavaMethod factory = isStoredVariant(entry) ? resolveStoredFactory(b, "createViewStored", StringView.class, int.class)
                                            : resolveStringViewCreateView1(b);
                            if (factory == null) {
                                return false;
                            }
                            b.handleReplacedInvoke(InvokeKind.Static, factory, new ValueNode[]{args[0], args[1]}, false);
                            return true;
                        }
                    }
                    return false;
                }
                if (entry != null && !StringAnalysisSingleByteOnly()) {
                    ResolvedJavaMethod factory = isStoredVariant(entry) ? resolveStoredFactory(b, "createStored", String.class, int.class)
                                    : resolveStringViewCreate1(b);
                    if (factory == null) {
                        return false;
                    }
                    b.handleReplacedInvoke(InvokeKind.Static, factory, new ValueNode[]{args[0], args[1]}, false);
                    return true;
                }
                if (singleByteEntry != null) {
                    ResolvedJavaMethod factory = resolveSingleByteCreateFromSubstring(b);
                    if (factory == null) {
                        return false;
                    }
                    ValueNode[] factoryArgs = new ValueNode[]{args[0], args[1]};
                    b.handleReplacedInvoke(InvokeKind.Static, factory, factoryArgs, false);
                    return true;
                }
                return false;
            }

            if (isValueOf) {
                if (singleByteEntry == null) {
                    return false;
                }
                ResolvedJavaMethod factory = resolveSingleByteCreateFromChar(b);
                if (factory == null) {
                    return false;
                }
                ValueNode[] factoryArgs = new ValueNode[]{args[0]};
                b.handleReplacedInvoke(InvokeKind.Static, factory, factoryArgs, false);
                return true;
            }

            return false;
        } catch (Throwable t) {
            return false;
        }
    }

    private static boolean StringAnalysisSingleByteOnly() {
        try {
            return SubstrateOptions.StringAnalysisSingleByteOnly.getValue();
        } catch (Throwable t) {
            return false;
        }
    }

    private static boolean isRepSubclassExact(ValueNode node, GraphBuilderContext b) {
        return receiverTypeExact(node, b) != null;
    }

    private static ResolvedJavaType receiverTypeExact(ValueNode node, GraphBuilderContext b) {
        try {
            Stamp stamp = node.stamp(NodeView.DEFAULT);
            if (!(stamp instanceof ObjectStamp os) || os.type() == null || !os.isExactType()) {
                return null;
            }
            ResolvedJavaType t = os.type();
            if (t.equals(b.getMetaAccess().lookupJavaType(StringView.class)) ||
                            t.equals(b.getMetaAccess().lookupJavaType(RopeString.class)) ||
                            t.equals(b.getMetaAccess().lookupJavaType(ThreeWayString.class)) ||
                            t.equals(b.getMetaAccess().lookupJavaType(FixedConcat4.class)) ||
                            t.equals(b.getMetaAccess().lookupJavaType(ArrayLazyString.class)) ||
                            t.equals(b.getMetaAccess().lookupJavaType(InterleavedStringArray.class)) ||
                            t.equals(b.getMetaAccess().lookupJavaType(SingleByteString.class))) {
                return t;
            }
            return null;
        } catch (Throwable ignored) {
            return null;
        }
    }

    @Override
    public boolean handleLoadConstant(GraphBuilderContext b, JavaConstant constant) {
        if (!hasDecisionSource()) {
            return false;
        }
        if (ZeroAdmitStock.active()) {
            return false; // a zero-admit profile compiles String as OFF does
        }
        try {
            if (constant.getJavaKind() != JavaKind.Object) {
                return false;
            }
            String strValue = b.getSnippetReflection().asObject(String.class, constant);
            if (strValue == null || strValue.length() != 1) {
                return false;
            }
            char c = strValue.charAt(0);
            if (c > 0xFF) {
                return false;
            }
            String loc = sourceLocation(b);
            ProfileEntry entry = lookupEntry(loc, OptimizationType.SINGLE_BYTE);
            if (entry == null) {
                return false;
            }
            ResolvedJavaMethod factory = resolveSingleByteCreate(b);
            if (factory == null) {
                return false;
            }
            byte byteValue = (byte) strValue.charAt(0);
            ValueNode byteArg = b.add(ConstantNode.forInt(byteValue));
            b.handleReplacedInvoke(InvokeKind.Static, factory, new ValueNode[]{byteArg}, false);
            return true;
        } catch (Throwable t) {
            return false;
        }
    }

    private static boolean hasDecisionSource() {
        return RepresentationProfileHolder.hasProfile();
    }

    private static ProfileEntry lookupEntry(String sourceLocation, OptimizationType type) {
        if (RepresentationProfileHolder.hasProfile()) {
            return RepresentationProfileHolder.getInstance().getEntry(sourceLocation, type);
        }
        return null;
    }

    private static String sourceLocation(GraphBuilderContext b) {
        return SiteKeys.profileKey(b.getMethod(), b.bci());
    }

    private static boolean isSubstringMethod(String name) {
        return name.equals("substring") || name.equals("subSequence");
    }

    private static MethodType resolveMethodType(GraphBuilderContext b, BootstrapMethodInvocation m) {
        try {
            JavaConstant typeConstant = m.getType();
            if (typeConstant != null) {
                return b.getSnippetReflection().asObject(MethodType.class, typeConstant);
            }
        } catch (Throwable t) {
            return null;
        }
        return null;
    }

    private static String readRecipe(GraphBuilderContext b, BootstrapMethodInvocation m) {
        try {
            java.util.List<JavaConstant> staticArgs = m.getStaticArguments();
            if (staticArgs == null || staticArgs.isEmpty()) {
                return null;
            }
            return b.getSnippetReflection().asObject(String.class, staticArgs.get(0));
        } catch (Throwable t) {
            return null;
        }
    }

    private ResolvedJavaMethod resolveRopeCreate(GraphBuilderContext b) {
        ResolvedJavaMethod cached = ropeCreateMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = RopeString.class.getDeclaredMethod("create", String.class, String.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            ropeCreateMethod = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    private ResolvedJavaMethod resolveThreeWayCreate(GraphBuilderContext b) {
        ResolvedJavaMethod cached = threeWayCreateMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = ThreeWayString.class.getDeclaredMethod("create", String.class, String.class, String.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            threeWayCreateMethod = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    private ResolvedJavaMethod resolveFixedConcat4Create(GraphBuilderContext b) {
        ResolvedJavaMethod cached = fixedConcat4CreateMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = FixedConcat4.class.getDeclaredMethod("create", String.class, String.class, String.class, String.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            fixedConcat4CreateMethod = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    private ResolvedJavaMethod resolveArrayLazyCreate(GraphBuilderContext b) {
        ResolvedJavaMethod cached = arrayLazyCreateMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = ArrayLazyString.class.getDeclaredMethod("create", String[].class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            arrayLazyCreateMethod = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    private ResolvedJavaMethod resolveInterleavedCreate(GraphBuilderContext b) {
        ResolvedJavaMethod cached = interleavedCreateMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = InterleavedStringArray.class.getDeclaredMethod("create", String[].class, String.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            interleavedCreateMethod = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    /** The fresh {@code String[]} of the converted parts, handed to the rep's owning factory. */
    private static ValueNode createStringArray(GraphBuilderContext b, ValueNode[] parts) {
        ResolvedJavaType stringType = b.getMetaAccess().lookupJavaType(String.class);
        ValueNode lengthNode = b.add(ConstantNode.forInt(parts.length));
        ValueNode array = b.add(new NewArrayNode(stringType, lengthNode, true));
        for (int i = 0; i < parts.length; i++) {
            b.add(new StoreIndexedNode(array, b.add(ConstantNode.forInt(i)), null, null, JavaKind.Object, parts[i]));
        }
        return array;
    }

    /** The converter of a dynamic operand of static type {@code type} (LazyConcatMint.converterMethod). */
    private ResolvedJavaMethod resolveConverter(GraphBuilderContext b, Class<?> type) {
        String key = type.isPrimitive() || type == String.class ? type.getName() : "java.lang.Object";
        ResolvedJavaMethod cached = converterByType.get(key);
        if (cached != null) {
            return cached;
        }
        try {
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(LazyConcatMint.converterMethod(type));
            converterByType.put(key, resolved);
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    /**
     * A join source call ({@code String.join(CharSequence, CharSequence...)} / {@code (CharSequence, Iterable)}) at a
     * LAZY_CONCAT site minting {@code INTERLEAVED}: replaced by the {@link LazyConcatFactory} join of the same parameters
     * (the JDK body, an interleaved result). The child decided the site; the parent only lowers.
     */
    private boolean lowerJoin(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (StringAnalysisSingleByteOnly()) {
            return false;
        }
        String sig = joinParameterSignature(method);
        if (!LazyConcatMint.isJoinSource(method.getDeclaringClass().toJavaName(), method.getName(), sig)) {
            return false;
        }
        String loc = sourceLocation(b);
        ProfileEntry lazyEntry = lookupEntry(loc, OptimizationType.LAZY_CONCAT);
        if (lazyEntry == null || !LazyConcatMint.INTERLEAVED.equals(LazyConcatMint.mintedRepForStringJoin(lazyEntry.getVariant())) ||
                        !lazyPairOutersLowered(loc)) {
            return false;
        }
        ResolvedJavaMethod factory = joinFactoryBySig.get(sig);
        if (factory == null) {
            try {
                Method reflection = LazyConcatMint.joinFactoryMethod(sig);
                if (reflection == null) {
                    return false;
                }
                factory = b.getMetaAccess().lookupJavaMethod(reflection);
                joinFactoryBySig.put(sig, factory);
            } catch (Throwable t) {
                return false;
            }
        }
        if (LazyConcatMint.MINT_LOG) {
            System.out.println("[lc-mintlog] parent " + loc + " variant=" + lazyEntry.getVariant() + " join minted=INTERLEAVED factory=" + factory.getName());
        }
        b.handleReplacedInvoke(InvokeKind.Static, factory, args, false);
        return true;
    }

    /** The element-source factory per row ({@code decl#name(sig)}). */
    private final ConcurrentHashMap<String, ResolvedJavaMethod> elementFactoryByRow = new ConcurrentHashMap<>();

    /**
     * An element-source call ({@link ElementSources}) at a {@code STRING_VIEW ELEMENT_VIEW[_STORED]} site: replaced by the
     * row's {@code ElementSourceFactory} method (the JDK algorithm, whose pieces of an exact-String input are views;
     * receiver first, then the arguments, then the constant {@code stored}). The parent only lowers.
     */
    private boolean lowerElementSource(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args, ProfileEntry entry) {
        String decl = method.getDeclaringClass().toJavaName();
        String sig = joinParameterSignature(method);
        String row = decl + "#" + method.getName() + "(" + sig + ")";
        ResolvedJavaMethod factory = elementFactoryByRow.get(row);
        if (factory == null) {
            try {
                Method reflection = ElementSources.factoryMethod(decl, method.getName(), sig);
                if (reflection == null) {
                    return false;
                }
                factory = b.getMetaAccess().lookupJavaMethod(reflection);
                elementFactoryByRow.put(row, factory);
            } catch (Throwable t) {
                System.out.println("[string-analysis] element source not lowered at " + entry.getSourceLocation() + ": " + t);
                return false;
            }
        }
        if (factory.getSignature().getParameterCount(false) != args.length + 1) {
            System.out.println("[string-analysis] element source not lowered at " + entry.getSourceLocation() + ": factory arity");
            return false;
        }
        boolean stored = ElementSources.ELEMENT_VIEW_STORED.equals(entry.getVariant());
        ValueNode[] fargs = java.util.Arrays.copyOf(args, args.length + 1);
        fargs[args.length] = b.add(ConstantNode.forBoolean(stored));
        if (LazyConcatMint.MINT_LOG) {
            System.out.println("[lc-mintlog] parent " + entry.getSourceLocation() + " element source " + row + " variant=" + entry.getVariant() + " factory=" + factory.getName());
        }
        b.handleReplacedInvoke(InvokeKind.Static, factory, fargs, false);
        return true;
    }

    /** The Phase-A parameter signature format ({@code SiteKeys.formatSignature}) of {@code method}. */
    private static String joinParameterSignature(ResolvedJavaMethod method) {
        StringBuilder sb = new StringBuilder();
        var sig = method.getSignature();
        int n = sig.getParameterCount(false);
        for (int i = 0; i < n; i++) {
            if (i > 0) {
                sb.append(",");
            }
            sb.append(sig.getParameterType(i, null).getName());
        }
        return sb.toString();
    }

    /** The factory of the minted rep {@code minted}: {@link LazyConcatMint#factoryMethod}, the pinned mapping. */
    private ResolvedJavaMethod resolveLazyFactory(GraphBuilderContext b, String minted) {
        ResolvedJavaMethod cached = lazyFactoryByRep.get(minted);
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = LazyConcatMint.factoryMethod(minted);
            if (reflection == null) {
                return null;
            }
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            lazyFactoryByRep.put(minted, resolved);
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    /** {@link LazyConcatFactory#stringConcat} (String.concat's empty-argument identity), resolved once. */
    private ResolvedJavaMethod resolveStringConcatFactory(GraphBuilderContext b) {
        ResolvedJavaMethod cached = lazyFactoryByRep.get("STRING_CONCAT");
        if (cached != null) {
            return cached;
        }
        try {
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(
                            LazyConcatFactory.class.getDeclaredMethod("stringConcat", String.class, String.class));
            lazyFactoryByRep.put("STRING_CONCAT", resolved);
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    /** A {@code STRING_VIEW STORED} substring site (the child saw the substring stored into the heap). */
    static boolean isStoredVariant(ProfileEntry entry) {
        return StringViewHeuristic.STORED.equals(entry.getVariant());
    }

    /** The stored-site factories ({@code StringView.createStored/createViewStored}); null when absent. */
    private static ResolvedJavaMethod resolveStoredFactory(GraphBuilderContext b, String name, Class<?>... params) {
        try {
            return b.getMetaAccess().lookupJavaMethod(StringView.class.getDeclaredMethod(name, params));
        } catch (Throwable t) {
            return null;
        }
    }

    private ResolvedJavaMethod resolveStringViewCreate(GraphBuilderContext b) {
        ResolvedJavaMethod cached = stringViewCreateMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = StringView.class.getDeclaredMethod("create", String.class, int.class, int.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            stringViewCreateMethod = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    /** The 1-arg substring(I) view factory (the end = the receiver's virtual length()). */
    private ResolvedJavaMethod resolveStringViewCreate1(GraphBuilderContext b) {
        ResolvedJavaMethod cached = stringViewCreate1Method;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = StringView.class.getDeclaredMethod("create", String.class, int.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            stringViewCreate1Method = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    private ResolvedJavaMethod resolveStringViewCreateView(GraphBuilderContext b) {
        ResolvedJavaMethod cached = stringViewCreateViewMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = StringView.class.getDeclaredMethod("createView", StringView.class, int.class, int.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            stringViewCreateViewMethod = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    /** The 1-arg substring(I) exact-StringView-receiver factory. */
    private ResolvedJavaMethod resolveStringViewCreateView1(GraphBuilderContext b) {
        ResolvedJavaMethod cached = stringViewCreateView1Method;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = StringView.class.getDeclaredMethod("createView", StringView.class, int.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            stringViewCreateView1Method = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    static final String ACCUMULATOR_VIEW = "ACCUMULATOR_VIEW";
    /** The stack-confined accumulator extraction (lowered to {@code StringView.createSkipCheck(<class>)}). */
    static final String ACCUMULATOR_VIEW_SHARED = "ACCUMULATOR_VIEW_SHARED";

    /** An accumulator-view profile variant (either word ends the toString site here). */
    static boolean isAccumulatorVariant(String variant) {
        return ACCUMULATOR_VIEW.equals(variant) || ACCUMULATOR_VIEW_SHARED.equals(variant);
    }

    /** The {@code StringView} factory name of an accumulator-view variant (pure; pinned by JUnit). */
    static String accumulatorFactoryName(String variant) {
        return ACCUMULATOR_VIEW_SHARED.equals(variant) ? "createSkipCheck" : "create";
    }

    /** Unified lowering: the accumulator classes and their snapshot factories ({@code StringView.create(<class>)}). */
    static final List<Class<?>> ACCUMULATOR_CLASSES = List.of(StringBuilder.class, StringBuffer.class, java.io.StringWriter.class);

    /**
     * Pinned by JUnit: the accumulator class whose snapshot factory lowers an {@code ACCUMULATOR_VIEW} {@code toString()}
     * declared by {@code declaredOwner}, given the entry's exact receiver class; null when the entry names no known
     * accumulator class or the declared owner is not a supertype of it (a profile/IR mismatch: the site is left as is).
     */
    static Class<?> accumulatorFactoryClass(String exactClass, java.util.function.Predicate<Class<?>> declaredOwnerHolds) {
        if (exactClass == null) {
            return null;
        }
        for (Class<?> c : ACCUMULATOR_CLASSES) {
            if (c.getName().equals(exactClass)) {
                return declaredOwnerHolds.test(c) ? c : null;
            }
        }
        return null;
    }

    private final ConcurrentHashMap<List<Object>, ResolvedJavaMethod> accumulatorFactories = new ConcurrentHashMap<>();

    /**
     * Lowers an admitted accumulator extraction {@code recv.toString()}: the exact class comes from the profile entry
     * (the child's receiver proof), the receiver goes through the zero-cost exact filter
     * ({@link InlineCacheTrivialMethodNodePlugin#trustedExactFilter}: analysis-only, nothing when the stamp already proves
     * the class), and the call becomes {@code StringView.create(<class>)}, the torn-snapshot-safe {@code ofBuilderSnapshot}
     * (for a StringWriter, over its {@code buf}); an {@code ACCUMULATOR_VIEW_SHARED} entry (stack-confined) becomes
     * {@code StringView.createSkipCheck(<class>)} (no occupancy check; the snapshot copy stays). No run-time class check
     * and no fallback: the runtime trusts the profile.
     */
    private boolean lowerAccumulatorExtraction(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode receiver, ProfileEntry entry) {
        ResolvedJavaType owner = method.getDeclaringClass();
        Class<?> acc = accumulatorFactoryClass(entry.getAccumulatorClass(), c -> owner.isAssignableFrom(b.getMetaAccess().lookupJavaType(c)));
        if (acc == null) {
            System.out.println("[string-analysis] accumulator view not lowered at " + entry.getSourceLocation() + ": declared " + owner.toJavaName(true) +
                            ", profile class " + entry.getAccumulatorClass());
            return false;
        }
        String factoryName = accumulatorFactoryName(entry.getVariant()); // SHARED -> createSkipCheck (no occupancy check)
        ResolvedJavaMethod factory = accumulatorFactories.computeIfAbsent(List.of(acc, factoryName), k -> {
            try {
                return b.getMetaAccess().lookupJavaMethod(StringView.class.getDeclaredMethod(factoryName, acc));
            } catch (NoSuchMethodException e) {
                throw new IllegalStateException(e);
            }
        });
        ValueNode narrowed = InlineCacheTrivialMethodNodePlugin.trustedExactFilter(b.getGraph(), b::add, receiver, b.getMetaAccess().lookupJavaType(acc));
        if (narrowed == null) {
            System.out.println("[string-analysis] accumulator view not lowered at " + entry.getSourceLocation() + ": the receiver stamp excludes " + acc.getName());
            return false;
        }
        b.handleReplacedInvoke(InvokeKind.Static, factory, new ValueNode[]{narrowed}, false);
        return true;
    }

    private volatile ResolvedJavaMethod joinerFactory;

    /**
     * Lowers an admitted StringJoiner extraction {@code recv.toString()}: the trusted exact filter on
     * {@code java.util.StringJoiner} (final, so the stamp is usually exact already), then
     * {@code InterleavedStringArray.ofJoiner(joiner)} (the JDK body for size 0 and short joins, else an interleaved string
     * over the joiner's array). A paired inner is lowered only when its lazy outers are.
     */
    private boolean lowerJoinerExtraction(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode receiver, ProfileEntry entry) {
        ResolvedJavaType joinerType = b.getMetaAccess().lookupJavaType(java.util.StringJoiner.class);
        if (!LazyConcatMint.INTERLEAVED.equals(entry.getVariant()) || !method.getDeclaringClass().isAssignableFrom(joinerType) ||
                        !lazyPairOutersLowered(entry.getSourceLocation())) {
            System.out.println("[string-analysis] joiner extraction not lowered at " + entry.getSourceLocation() + ": declared " +
                            method.getDeclaringClass().toJavaName(true) + ", variant " + entry.getVariant());
            return false;
        }
        ResolvedJavaMethod factory = joinerFactory;
        if (factory == null) {
            try {
                factory = b.getMetaAccess().lookupJavaMethod(InterleavedStringArray.class.getDeclaredMethod("ofJoiner", java.util.StringJoiner.class));
            } catch (NoSuchMethodException e) {
                throw new IllegalStateException(e);
            }
            joinerFactory = factory;
        }
        ValueNode narrowed = InlineCacheTrivialMethodNodePlugin.trustedExactFilter(b.getGraph(), b::add, receiver, joinerType);
        if (narrowed == null) {
            System.out.println("[string-analysis] joiner extraction not lowered at " + entry.getSourceLocation() + ": the receiver stamp excludes java.util.StringJoiner");
            return false;
        }
        if (LazyConcatMint.MINT_LOG) {
            System.out.println("[lc-mintlog] parent " + entry.getSourceLocation() + " joiner minted=INTERLEAVED factory=ofJoiner");
        }
        b.handleReplacedInvoke(InvokeKind.Static, factory, new ValueNode[]{narrowed}, false);
        return true;
    }

    private ResolvedJavaMethod resolveSingleByteCreate(GraphBuilderContext b) {
        ResolvedJavaMethod cached = singleByteCreateMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = SingleByteString.class.getDeclaredMethod("create", byte.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            singleByteCreateMethod = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    private ResolvedJavaMethod resolveSingleByteCreateFromSubstring(GraphBuilderContext b) {
        ResolvedJavaMethod cached = singleByteCreateFromSubstringMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = SingleByteString.class.getDeclaredMethod("createFromSubstring", String.class, int.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            singleByteCreateFromSubstringMethod = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }

    private ResolvedJavaMethod resolveSingleByteCreateFromChar(GraphBuilderContext b) {
        ResolvedJavaMethod cached = singleByteCreateFromCharMethod;
        if (cached != null) {
            return cached;
        }
        try {
            Method reflection = SingleByteString.class.getDeclaredMethod("createFromChar", char.class);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflection);
            singleByteCreateFromCharMethod = resolved;
            return resolved;
        } catch (Throwable t) {
            return null;
        }
    }
}