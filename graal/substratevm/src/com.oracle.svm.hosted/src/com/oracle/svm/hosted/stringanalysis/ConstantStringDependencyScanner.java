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

import java.util.HashSet;
import java.util.Set;

import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.meta.AnalysisMethod;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.vm.ci.code.BytecodePosition;
import jdk.vm.ci.meta.ConstantPool;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.JavaMethod;
import jdk.vm.ci.meta.JavaType;

/**
 * Computes the {@code ldc String} BCIs that flow into an invoke whose target is a build-time constant-String consumer
 * ({@link ConstantStringDependencyRegistry}). {@link SingleByteHeuristic} excludes these BCIs from SINGLE_BYTE candidacy
 * so that the replacement plugin can stay mechanical.
 *
 * The scan is intra-method with two rules, both conservative (over-exclusion, never under-exclusion):
 * (1) Immediate adjacency ({@code ldc String; invoke consumer}): a one-slot "top of stack holds a known ldc" tracker;
 *     {@code ldc String} sets it, a consumer {@code invoke} flags it, any other instruction (including branches and
 *     stores/loads) clears it.
 * (2) Store-then-load ({@code ldc String; astore N; ...; aload N; invoke consumer}): if the method contains any consumer
 *     invoke, every {@code ldc} of an Object-kind constant immediately followed by an {@code astore} is flagged, whether
 *     or not a load of that local reaches the consumer. A flagged constant is not replaced and stays a plain constant
 *     String the consumer can read, so no branch-conditional or aliasing store-then-load pattern can let a
 *     consumer-bound constant be replaced; the cost is at most a forgone micro-optimization.
 */
public final class ConstantStringDependencyScanner {

    private ConstantStringDependencyScanner() {
    }

    public static Set<String> computeDoNotSingleByteKeys(StringUtilizationGraph graph) {
        Set<String> excluded = new HashSet<>();
        Set<AnalysisMethod> scannedMethods = new HashSet<>();
        for (SugVertex v : graph.getVertices()) {
            if (v.getNodeType() != SugNodeType.STRING_LITERAL) {
                continue;
            }
            if (v.getLength() != 1) {
                continue;
            }
            TypeFlow<?> flow = v.getSourceFlow();
            if (flow == null || flow.getSource() == null) {
                continue;
            }
            BytecodePosition pos = (BytecodePosition) flow.getSource();
            if (!(pos.getMethod() instanceof AnalysisMethod am)) {
                continue;
            }
            if (scannedMethods.add(am)) {
                excluded.addAll(scanMethod(am));
            }
        }
        return excluded;
    }

    private static Set<String> scanMethod(AnalysisMethod method) {
        Set<String> result = new HashSet<>();
        byte[] code = method.getCode();
        if (code == null) {
            return result;
        }
        ConstantPool cp = method.getConstantPool();
        boolean methodHasConsumerInvoke = false;
        Set<Integer> storedLdcBcis = new HashSet<>();
        boolean stackHasLdc = false;
        int stackLdcBci = -1;
        BytecodeStream bs = new BytecodeStream(code);
        while (bs.currentBCI() < code.length) {
            int opcode = bs.currentBC();
            if (opcode == Bytecodes.END) {
                break;
            }
            int curBci = bs.currentBCI();
            if (opcode == Bytecodes.LDC || opcode == Bytecodes.LDC_W) {
                int cpi = bs.readCPI();
                if (isObjectKindConstant(cp, cpi)) {
                    stackHasLdc = true;
                    stackLdcBci = curBci;
                } else {
                    stackHasLdc = false;
                    stackLdcBci = -1;
                }
            } else if (isAstore(opcode)) {
                if (stackHasLdc && stackLdcBci >= 0) {
                    storedLdcBcis.add(stackLdcBci);
                }
                stackHasLdc = false;
                stackLdcBci = -1;
            } else if (Bytecodes.isInvoke(opcode)) {
                boolean consumer = invokeIsConsumer(bs, cp);
                if (consumer) {
                    methodHasConsumerInvoke = true;
                    if (stackHasLdc && stackLdcBci >= 0) {
                        result.add(SiteKeys.profileKey(method, stackLdcBci));
                    }
                }
                stackHasLdc = false;
                stackLdcBci = -1;
            } else {
                stackHasLdc = false;
                stackLdcBci = -1;
            }
            bs.next();
        }
        if (methodHasConsumerInvoke) {
            for (int bci : storedLdcBcis) {
                result.add(SiteKeys.profileKey(method, bci));
            }
        }
        return result;
    }

    private static boolean isObjectKindConstant(ConstantPool cp, int cpi) {
        try {
            Object constant = cp.lookupConstant(cpi);
            return constant instanceof JavaConstant jc && jc.getJavaKind() == JavaKind.Object && !jc.isNull();
        } catch (Throwable t) {
            return false;
        }
    }

    private static boolean invokeIsConsumer(BytecodeStream bs, ConstantPool cp) {
        int opcode = bs.currentBC();
        int cpi = bs.readCPI();
        JavaMethod target = safeLookupMethod(cp, cpi, opcode);
        if (target == null) {
            return false;
        }
        String key = methodKey(target);
        return ConstantStringDependencyRegistry.isConstantStringConsumer(key);
    }

    private static String methodKey(JavaMethod m) {
        JavaType decl = m.getDeclaringClass();
        String declName = decl != null ? decl.toJavaName() : "";
        String sig = m.getSignature() != null ? m.getSignature().toMethodDescriptor() : "";
        return declName + "#" + m.getName() + sig;
    }

    private static JavaMethod safeLookupMethod(ConstantPool cp, int cpi, int opcode) {
        try {
            return cp.lookupMethod(cpi, opcode);
        } catch (Throwable t) {
            return null;
        }
    }

    private static boolean isAstore(int opcode) {
        return opcode == Bytecodes.ASTORE || opcode == Bytecodes.ASTORE_0 ||
                        opcode == Bytecodes.ASTORE_1 || opcode == Bytecodes.ASTORE_2 ||
                        opcode == Bytecodes.ASTORE_3;
    }
}