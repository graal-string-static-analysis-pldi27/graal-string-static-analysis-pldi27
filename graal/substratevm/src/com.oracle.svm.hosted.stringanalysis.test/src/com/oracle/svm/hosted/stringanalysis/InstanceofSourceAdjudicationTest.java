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

import java.lang.annotation.Annotation;
import java.lang.reflect.AnnotatedElement;
import java.util.Arrays;
import java.util.Comparator;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.graal.pointsto.api.HostVM;
import com.oracle.graal.pointsto.infrastructure.SubstitutionProcessor;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisFactory;
import com.oracle.graal.pointsto.typestate.DefaultAnalysisPolicy;

import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.NodeSourcePosition;
import jdk.graal.compiler.java.GraphBuilderPhase;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration;
import jdk.graal.compiler.nodes.graphbuilderconf.IntrinsicContext;
import jdk.graal.compiler.options.OptionValues;
import jdk.graal.compiler.phases.OptimisticOptimizations;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;
import jdk.vm.ci.runtime.JVMCIBackend;

import org.graalvm.collections.EconomicMap;
import org.graalvm.nativeimage.impl.AnnotationExtractor;

/**
 * Source-shape adjudication pins for exact instanceof folds. A fold is allowed (not a rejecting usage) iff its
 * position provably holds an {@code instanceof} bytecode (opcode 193, with the out-of-cone target gate) or a
 * {@code checkcast} bytecode (opcode 192, with no cone gate: a cast to String is a no-op assignment for String and
 * every rep, a cast to anything else is CCE-identical for both). Every other shape stays strict: the getClass-compare
 * fold (opcode 165/166, the silent-admit leak class incl. {@code getClass() == String.class}), synthetic positions
 * (bci&lt;0, generated reflection accessors), foreign methods, missing positions, and every in-cone instanceof target
 * (T == String: String passes, every rep fails; T == a rep: the symmetric corner). The families are disjoint by
 * position opcode.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi", "jdk.graal.compiler/jdk.graal.compiler.graph.iterators",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.bytecode",
                "org.graalvm.nativeimage/org.graalvm.nativeimage.impl"})
public class InstanceofSourceAdjudicationTest {

    /**
     * Real bytecode provenance: the bcis are located at test time by scanning the compiled Holder methods, as the
     * production predicate reads {@code method.getCode()}.
     */
    @SuppressWarnings("unused")
    private static final class Holder {
        static boolean instOfInt(Object v) {
            return v instanceof Integer;
        }

        static boolean instOfString(Object v) {
            return v instanceof String;
        }

        static Integer castInt(Object v) {
            return (Integer) v;
        }

        static String castString(Object v) {
            return (String) v;
        }

        static boolean getClassCmp(Object v) {
            return v.getClass() == Integer.class;
        }

        static boolean getClassCmpString(Object v) {
            return v.getClass() == String.class;
        }
    }

    /** The minimal JVMCI-backed universe. */
    private static final class UniverseFixture {
        final MetaAccessProvider metaAccess;
        final AnalysisUniverse universe;

        UniverseFixture() {
            JVMCIBackend backend = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend();
            this.metaAccess = backend.getMetaAccess();
            AnnotationExtractor annotations = new AnnotationExtractor() {
                @Override
                public boolean hasAnnotation(AnnotatedElement element, Class<? extends Annotation> annotationType) {
                    return element.isAnnotationPresent(annotationType);
                }

                @Override
                public <T extends Annotation> T extractAnnotation(AnnotatedElement element, Class<T> annotationType, boolean declaredOnly) {
                    return declaredOnly ? element.getDeclaredAnnotation(annotationType) : element.getAnnotation(annotationType);
                }

                @Override
                @SuppressWarnings("unchecked")
                public Class<? extends Annotation>[] getAnnotationTypes(AnnotatedElement element) {
                    return Arrays.stream(element.getAnnotations()).map(Annotation::annotationType).toArray(Class[]::new);
                }
            };
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), InstanceofSourceAdjudicationTest.class.getClassLoader()) {
                @Override
                public void onTypeReachable(com.oracle.graal.pointsto.BigBang bb, AnalysisType type) {
                    // no-op
                }

                @Override
                public boolean isInitialized(AnalysisType type) {
                    return true;
                }

                @Override
                public GraphBuilderPhase.Instance createGraphBuilderPhase(com.oracle.graal.pointsto.meta.HostedProviders providers,
                                GraphBuilderConfiguration config, OptimisticOptimizations optimizations, IntrinsicContext intrinsicContext) {
                    return null;
                }

                @Override
                public Comparator<? super ResolvedJavaType> getTypeComparator() {
                    return null;
                }
            };
            DefaultAnalysisPolicy policy = new DefaultAnalysisPolicy(new OptionValues(EconomicMap.create()));
            this.universe = new AnalysisUniverse(host, JavaKind.Object, policy, SubstitutionProcessor.IDENTITY,
                            metaAccess, new PointsToAnalysisFactory(), annotations);
            lookup(Object.class);
            lookup(Cloneable.class);
            lookup(String.class);
            lookup(Number.class);
            lookup(Integer.class);
        }

        AnalysisType lookup(Class<?> clazz) {
            return universe.lookup((ResolvedJavaType) metaAccess.lookupJavaType(clazz));
        }
    }

    private static ResolvedJavaMethod holderMethod(UniverseFixture f, String name) throws Exception {
        return (ResolvedJavaMethod) f.metaAccess.lookupJavaMethod(
                        Holder.class.getDeclaredMethod(name, Object.class));
    }

    /** The first bci in {@code method}'s code holding one of {@code opcodes}. */
    private static int bciOf(ResolvedJavaMethod method, int... opcodes) {
        byte[] code = method.getCode();
        Assert.assertNotNull("the Holder method must have code", code);
        for (int i = 0; i < code.length; i++) {
            int op = code[i] & 0xFF;
            for (int want : opcodes) {
                if (op == want) {
                    return i;
                }
            }
        }
        throw new AssertionError("opcode not found in " + method.getName());
    }

    /** A hand-built exact InstanceOfNode on a fresh param, carrying the given position. */
    private static InstanceOfNode exactIonAt(UniverseFixture f, Class<?> target,
                    ResolvedJavaMethod posMethod, int posBci) {
        OptionValues options = new OptionValues(EconomicMap.create());
        DebugContext debug = new DebugContext.Builder(options).build();
        StructuredGraph graph = new StructuredGraph.Builder(options, debug)
                        .name("InstanceofSourceAdjudicationTest").method(posMethod).build();
        Stamp objectStamp = StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(
                        (ResolvedJavaType) f.metaAccess.lookupJavaType(Object.class)));
        ParameterNode param = graph.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(objectStamp)));
        ResolvedJavaType target_type = (ResolvedJavaType) f.metaAccess.lookupJavaType(target);
        InstanceOfNode ion = (InstanceOfNode) graph.addOrUnique(InstanceOfNode.create(
                        TypeReference.createExactTrusted(target_type), param));
        if (posBci >= 0) {
            ion.setNodeSourcePosition(new NodeSourcePosition(null, posMethod, posBci));
        }
        return ion;
    }

    /** Pin 1 (the adjudication's allow side): instanceof-source + out-of-cone → allowed. */
    @Test
    public void instanceofSourceFoldOutOfConeIsAllowed() throws Exception {
        UniverseFixture f = new UniverseFixture();
        ResolvedJavaMethod m = holderMethod(f, "instOfInt");
        InstanceOfNode ion = exactIonAt(f, Integer.class, m, bciOf(m, Bytecodes.INSTANCEOF));
        Assert.assertTrue("an exact fold at a REAL instanceof bci with an out-of-cone " +
                        "target is NOT a rejecting usage",
                        LfgWalk.instanceofSourceFoldAllowed(ion, m, f.universe::lookup));
    }

    /**
     * Pin 2 (the leak side stays strict): the getClass-compare fold, whose position is the compare bytecode
     * (if_acmpne/eq), never an instanceof/checkcast, and the no-position corner. This leak class (incl.
     * {@code getClass()==String.class}) must keep rejecting: the cast arm must not admit a genuine getClass compare (the
     * opcode anchor separates them).
     */
    @Test
    public void getClassCompareFoldStaysStrict() throws Exception {
        UniverseFixture f = new UniverseFixture();
        ResolvedJavaMethod m = holderMethod(f, "getClassCmp");
        InstanceOfNode ion = exactIonAt(f, Integer.class, m,
                        bciOf(m, Bytecodes.IF_ACMPEQ, Bytecodes.IF_ACMPNE));
        Assert.assertFalse("a fold whose position resolves to the compare bytecode (the " +
                        "getClass-source fold) STAYS strict",
                        LfgWalk.instanceofSourceFoldAllowed(ion, m, f.universe::lookup));
        InstanceOfNode noPos = exactIonAt(f, Integer.class, m, -1);
        Assert.assertFalse("a fold with no source position stays strict (unprovable source)",
                        LfgWalk.instanceofSourceFoldAllowed(noPos, m, f.universe::lookup));
    }

    /**
     * Pin 2b (the class-mirror rule): the genuine {@code x.getClass() == String.class} compare, an exact-String fold at
     * the compare bytecode (opcode 165/166), stays strict, since a rep's exact class differs from String's. The compare
     * position carries no instanceof/checkcast opcode, so the discriminator rejects it regardless of the tested type.
     */
    @Test
    public void getClassCompareStringClassStaysStrict() throws Exception {
        UniverseFixture f = new UniverseFixture();
        ResolvedJavaMethod m = holderMethod(f, "getClassCmpString");
        InstanceOfNode ion = exactIonAt(f, String.class, m,
                        bciOf(m, Bytecodes.IF_ACMPEQ, Bytecodes.IF_ACMPNE));
        Assert.assertFalse("the genuine x.getClass() == String.class compare STAYS strict " +
                        "(the class-mirror rule: the exact class genuinely differs " +
                        "for a rep; the compare opcode is not 192/193)",
                        LfgWalk.instanceofSourceFoldAllowed(ion, m, f.universe::lookup));
    }

    /**
     * Pin 3 (the leak corner at instanceof source): even a real instanceof bci with the tested type in the String cone
     * (T == String: plain String passes, every rep fails) stays strict.
     */
    @Test
    public void stringConeTargetStaysStrictEvenAtInstanceOfSource() throws Exception {
        UniverseFixture f = new UniverseFixture();
        ResolvedJavaMethod m = holderMethod(f, "instOfString");
        InstanceOfNode ion = exactIonAt(f, String.class, m, bciOf(m, Bytecodes.INSTANCEOF));
        Assert.assertFalse("an instanceof-source fold with an IN-CONE target (the " +
                        "String-passes/rep-fails divergence) STAYS strict",
                        LfgWalk.instanceofSourceFoldAllowed(ion, m, f.universe::lookup));
    }

    /**
     * Pin 4: the checkcast-source fold (opcode 192) is allowed. The out-of-cone cast {@code (Integer) v} on a String
     * value throws CCE identically whether the value is String or any rep (reps live inside the String cone; the
     * hierarchy below Integer is untouched): transparent, no usage minted.
     */
    @Test
    public void checkcastSourceFoldIsAllowed() throws Exception {
        UniverseFixture f = new UniverseFixture();
        ResolvedJavaMethod m = holderMethod(f, "castInt");
        InstanceOfNode ion = exactIonAt(f, Integer.class, m, bciOf(m, Bytecodes.CHECKCAST));
        Assert.assertTrue("a fold at a checkcast bci is ALLOWED (the cast-fold ruling: " +
                        "the out-of-cone cast is CCE-identical for String and every rep)",
                        LfgWalk.instanceofSourceFoldAllowed(ion, m, f.universe::lookup));
    }

    /**
     * Pin 4b (the in-cone cast): even a checkcast whose checked type is in the String cone ({@code (String) v}) is
     * allowed: a rep is-a String, so {@code (String) x} succeeds for String and every rep. Unlike the instanceof arm's
     * cone gate (pin 3), a cast cannot diverge because user source never sees the rep classes.
     */
    @Test
    public void inConeStringCastFoldIsAllowed() throws Exception {
        UniverseFixture f = new UniverseFixture();
        ResolvedJavaMethod m = holderMethod(f, "castString");
        InstanceOfNode ion = exactIonAt(f, String.class, m, bciOf(m, Bytecodes.CHECKCAST));
        Assert.assertTrue("an in-cone (String) cast fold is ALLOWED (a rep IS-A String: " +
                        "exact-true for both, a no-op assignment — never a check)",
                        LfgWalk.instanceofSourceFoldAllowed(ion, m, f.universe::lookup));
    }

    /**
     * Pin 5: synthetic positions (bci&lt;0, generated reflection accessors) and positions of a foreign method stay
     * strict.
     */
    @Test
    public void syntheticAndForeignPositionsStayStrict() throws Exception {
        UniverseFixture f = new UniverseFixture();
        ResolvedJavaMethod m = holderMethod(f, "instOfInt");
        InstanceOfNode synthetic = exactIonAt(f, Integer.class, m, -6);
        Assert.assertFalse("a synthetic position stays strict",
                        LfgWalk.instanceofSourceFoldAllowed(synthetic, m, f.universe::lookup));
        ResolvedJavaMethod other = holderMethod(f, "castInt");
        InstanceOfNode foreign = exactIonAt(f, Integer.class, other, bciOf(other, Bytecodes.CHECKCAST));
        Assert.assertFalse("a position of a different method stays strict",
                        LfgWalk.instanceofSourceFoldAllowed(foreign, m, f.universe::lookup));
    }

    /**
     * The {@code Field.binaryValue} miniature (the shape of Lucene's {@code Field.binaryValue}):
     * <pre> {@code
     * if (fieldsData instanceof BytesRef) {   // instanceof @4  (opcode 193)
     *   return (BytesRef) fieldsData;          // checkcast  @14 (opcode 192)
     * } else {
     *   return null;
     * }}</pre>
     */
    @SuppressWarnings("unused")
    private static final class BinaryValueHolder {
        static Object binaryValue(Object fieldsData) {
            if (fieldsData instanceof Integer) {
                return (Integer) fieldsData;
            } else {
                return null;
            }
        }
    }

    /**
     * Pin 6 (the bci-14 anchor): the construct's two folds on the same value, the instanceof-source fold (@4) and the
     * checkcast-source fold (@14), both classify transparent: both observe only the hub against a final out-of-cone
     * type, which String and every rep answer identically.
     */
    @Test
    public void binaryValueInstanceofAndCheckcastFoldsClassifyIdentically() throws Exception {
        UniverseFixture f = new UniverseFixture();
        f.lookup(BinaryValueHolder.class);
        ResolvedJavaMethod m = (ResolvedJavaMethod) f.metaAccess.lookupJavaMethod(
                        BinaryValueHolder.class.getDeclaredMethod("binaryValue", Object.class));
        int instBci = bciOf(m, Bytecodes.INSTANCEOF);
        int castBci = bciOf(m, Bytecodes.CHECKCAST);
        InstanceOfNode instFold = exactIonAt(f, Integer.class, m, instBci);
        InstanceOfNode castFold = exactIonAt(f, Integer.class, m, castBci);
        boolean instAllowed = LfgWalk.instanceofSourceFoldAllowed(instFold, m, f.universe::lookup);
        boolean castAllowed = LfgWalk.instanceofSourceFoldAllowed(castFold, m, f.universe::lookup);
        Assert.assertTrue("the @4 instanceof-source fold is allowed",
                        instAllowed);
        Assert.assertTrue("the @14 checkcast-source fold is allowed (the cast-fold ruling)",
                        castAllowed);
        Assert.assertEquals("the binaryValue pair classifies IDENTICALLY (the differential)",
                        instAllowed, castAllowed);
    }

    /**
     * The {@code RealLog.rawBytes} miniature (a sibling family):
     * an {@code instanceof String} chain whose final else arm holds a {@code (byte[])}
     * dead-arm cast on the traced value.
     */
    @SuppressWarnings("unused")
    private static final class RawBytesHolder {
        static int rawBytes(Object value, int index) {
            if (value instanceof String s) {
                return s.charAt(index);
            } else if (value instanceof char[] c) {
                return c[index];
            } else {
                return ((byte[]) value)[index]; // the dead-arm (byte[]) cast
            }
        }
    }

    /**
     * Pin 7 (the rawBytes@97 shape): the {@code instanceof String} chain's final dead-arm {@code (byte[])} cast fold on
     * the traced value classifies transparent: a String never reaches the cast (the @55 instanceof String arm is
     * taken), and even there String and every rep fail with the same CCE (byte[] is out of cone).
     */
    @Test
    public void rawBytesDeadArmByteArrayCastFoldIsAllowed() throws Exception {
        UniverseFixture f = new UniverseFixture();
        f.lookup(RawBytesHolder.class);
        ResolvedJavaMethod m = (ResolvedJavaMethod) f.metaAccess.lookupJavaMethod(
                        RawBytesHolder.class.getDeclaredMethod("rawBytes", Object.class, int.class));
        byte[] code = m.getCode();
        Assert.assertNotNull(code);
        int castBci = -1;
        for (int i = 0; i < code.length; i++) {
            if ((code[i] & 0xFF) == Bytecodes.CHECKCAST) {
                castBci = i; // the last checkcast in the chain is the byte[] dead arm
            }
        }
        Assert.assertTrue("the rawBytes shape must contain a checkcast", castBci >= 0);
        // the cast arm needs no cone test; assert through the actual byte[]-typed fold at the cast bci
        InstanceOfNode ion = exactIonAt(f, byte[].class, m, castBci);
        Assert.assertTrue("the rawBytes dead-arm (byte[]) cast fold is ALLOWED (the cast " +
                        "arm is transparent — CCE-identical for String and every rep)",
                        LfgWalk.instanceofSourceFoldAllowed(ion, m, f.universe::lookup));
    }
}
