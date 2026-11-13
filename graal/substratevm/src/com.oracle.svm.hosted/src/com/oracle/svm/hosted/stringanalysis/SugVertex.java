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
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.typestate.TypeState;

public final class SugVertex {

    public static final int UNKNOWN_LENGTH = -1;

    private final int id;
    private SugNodeType nodeType;
    private String sourceLocation;
    private AnalysisMethod enclosingMethod;
    private String enclosingClassName;
    private String sourceKey;
    private AnalysisType javaType;
    private String label;
    private String methodName;
    private String methodSignature;
    private String declaringClass;
    private int length = UNKNOWN_LENGTH;
    /** A substring/subSequence site's compile-time constant range length (CapturedSite constRange), else -1. */
    private int constRangeLength = UNKNOWN_LENGTH;
    private String literalText;
    private int dynamicOperandCount = -1;
    /** The bootstrap recipe of an indy concat vertex (null: bare makeConcat, or not an indy concat). */
    private String concatRecipe;
    /** One char per dynamic operand of an indy concat (ConcatSite#operandKinds), or null. */
    private String concatOperandKinds;
    private long constantValue;
    private TypeFlow<?> sourceFlow;
    private TypeState receiverTypeState;
    private TypeState argumentTypeState;

    private final List<SugEdge> outEdges = new ArrayList<>();
    private final List<SugEdge> inEdges = new ArrayList<>();
    private BitSet usageTags;
    private BitSet sourceTags;
    private boolean incompleteTrace;
    private boolean resourceLimitedTrace;
    private boolean wiredAnyLoad;
    private boolean virtualArgUsage;
    private boolean accumulatorOp;
    /** A CONCAT_EXPRESSION site whose StringConcatFactory strategy never copies an operand ({@code StringAtoms.scfCopiesOperand}). */
    private volatile boolean scfNoCopy;
    /** A CONCAT_EXPRESSION site whose stock strategy copies an operand with a lowerable shape (UNARY/BINARY), else null. */
    private volatile StringAtoms.CopyShape scfCopyShape;
    /** Nested concat: the outer concat sites this lazy candidate was admitted as an operand of. */
    private final Set<String> lazyOperandSites = ConcurrentHashMap.newKeySet();
    private List<String> operandSourceLocations = Collections.emptyList();

    SugVertex(int id) {
        this.id = id;
    }

    public int getId() {
        return id;
    }

    public SugNodeType getNodeType() {
        return nodeType;
    }

    public void setNodeType(SugNodeType nodeType) {
        this.nodeType = nodeType;
    }

    public String getSourceLocation() {
        return sourceLocation;
    }

    public void setSourceLocation(String sourceLocation) {
        this.sourceLocation = sourceLocation;
    }

    public AnalysisMethod getEnclosingMethod() {
        return enclosingMethod;
    }

    public void setEnclosingMethod(AnalysisMethod enclosingMethod) {
        this.enclosingMethod = enclosingMethod;
        if (enclosingMethod != null) {
            this.enclosingClassName = enclosingMethod.getDeclaringClass().toJavaName(true);
        }
    }

    public String getEnclosingClassName() {
        return enclosingClassName;
    }

    public void setEnclosingClassName(String enclosingClassName) {
        this.enclosingClassName = enclosingClassName;
    }

    public String getSourceKey() {
        return sourceKey;
    }

    public void setSourceKey(String sourceKey) {
        this.sourceKey = sourceKey;
    }

    public AnalysisType getJavaType() {
        return javaType;
    }

    public void setJavaType(AnalysisType javaType) {
        this.javaType = javaType;
    }

    public String getLabel() {
        return label;
    }

    public void setLabel(String label) {
        this.label = label;
    }

    public String getMethodName() {
        return methodName;
    }

    public void setMethodName(String methodName) {
        this.methodName = methodName;
    }

    public String getMethodSignature() {
        return methodSignature;
    }

    public void setMethodSignature(String methodSignature) {
        this.methodSignature = methodSignature;
    }

    public String getDeclaringClass() {
        return declaringClass;
    }

    public void setDeclaringClass(String declaringClass) {
        this.declaringClass = declaringClass;
    }

    public int getLength() {
        return length;
    }

    public void setLength(int length) {
        this.length = length;
    }

    public int getConstRangeLength() {
        return constRangeLength;
    }

    public void setConstRangeLength(int constRangeLength) {
        this.constRangeLength = constRangeLength;
    }

    public String getLiteralText() {
        return literalText;
    }

    public void setLiteralText(String literalText) {
        this.literalText = literalText;
    }

    public boolean isScfNoCopy() {
        return scfNoCopy;
    }

    public void addLazyOperandSite(String loc) {
        if (loc != null) {
            lazyOperandSites.add(loc);
        }
    }

    public Set<String> getLazyOperandSites() {
        return lazyOperandSites;
    }

    public void markScfNoCopy() {
        this.scfNoCopy = true;
    }

    /** The copying shape of this concat site (UNARY/BINARY), or null (non-copying, UNKNOWN or not a concat). */
    StringAtoms.CopyShape getScfCopyShape() {
        return scfCopyShape;
    }

    void markScfCopyShape(StringAtoms.CopyShape shape) {
        this.scfCopyShape = shape;
    }

    public int getDynamicOperandCount() {
        return dynamicOperandCount;
    }

    public void setDynamicOperandCount(int dynamicOperandCount) {
        this.dynamicOperandCount = dynamicOperandCount;
    }

    /** The recipe the parent's replacement lowers by (see {@link LazyConcatMint#mintedRep}). */
    public String getConcatRecipe() {
        return concatRecipe;
    }

    public void setConcatRecipe(String concatRecipe) {
        this.concatRecipe = concatRecipe;
    }

    /** The dynamic operands' static kinds: S String, P primitive, B final box type, O other reference. */
    public String getConcatOperandKinds() {
        return concatOperandKinds;
    }

    public void setConcatOperandKinds(String concatOperandKinds) {
        this.concatOperandKinds = concatOperandKinds;
    }

    /** A {@code String.concat(String)} call vertex (the parent mints a 2-operand rope there, never by recipe). */
    public boolean isStringConcatCall() {
        return nodeType == SugNodeType.CONCAT_EXPRESSION && "concat".equals(methodName);
    }

    public long getConstantValue() {
        return constantValue;
    }

    public void setConstantValue(long constantValue) {
        this.constantValue = constantValue;
    }

    public TypeFlow<?> getSourceFlow() {
        return sourceFlow;
    }

    public void setSourceFlow(TypeFlow<?> sourceFlow) {
        this.sourceFlow = sourceFlow;
    }

    public TypeState getReceiverTypeState() {
        return receiverTypeState;
    }

    public void setReceiverTypeState(TypeState receiverTypeState) {
        this.receiverTypeState = receiverTypeState;
    }

    public TypeState getArgumentTypeState() {
        return argumentTypeState;
    }

    public void setArgumentTypeState(TypeState argumentTypeState) {
        this.argumentTypeState = argumentTypeState;
    }

    public List<SugEdge> getOutEdges() {
        return Collections.unmodifiableList(outEdges);
    }

    public List<SugEdge> getInEdges() {
        return Collections.unmodifiableList(inEdges);
    }

    public void addOutEdge(SugEdge edge) {
        outEdges.add(edge);
    }

    public void addInEdge(SugEdge edge) {
        inEdges.add(edge);
    }

    public void removeOutEdge(SugEdge edge) {
        outEdges.remove(edge);
    }

    public void removeInEdge(SugEdge edge) {
        inEdges.remove(edge);
    }

    public BitSet getUsageTags() {
        if (usageTags == null) {
            usageTags = new BitSet();
        }
        return usageTags;
    }

    /** Overwrites {@code usageTags} with the engine's per-origin tag set ({@code ForwardFixpoint.emit}, the sole source). */
    public void setUsageTags(BitSet tags) {
        this.usageTags = tags;
    }

    public BitSet getSourceTags() {
        if (sourceTags == null) {
            sourceTags = new BitSet();
        }
        return sourceTags;
    }

    public void clearEdges() {
        outEdges.clear();
        inEdges.clear();
    }

    public boolean isIncompleteTrace() {
        return incompleteTrace;
    }

    public void markIncompleteTrace() {
        this.incompleteTrace = true;
    }

    /**
     * Clears {@code incompleteTrace}: {@code ForwardFixpoint.emit}'s explicit complete verdict (e.g. via the safe-sink
     * mask) for aggregates whose summaries carry no incompleteness.
     */
    public void clearIncompleteTrace() {
        this.incompleteTrace = false;
    }

    public boolean isResourceLimitedTrace() {
        return resourceLimitedTrace;
    }

    public void markResourceLimitedTrace() {
        resourceLimitedTrace = true;
    }

    /**
     * True when one of this vertex's origins had a transfer STORE endpoint whose composeHeap wired a non-empty load set
     * (directly, or attributed to the callee PARAM_ENTRY origin and carried over the bridge). The PDP(c) bit of
     * {@code AdmissionProof.hasPositiveDownstreamProof}: evidence, never a clearance (ADMIT also requires validateUsages
     * and a complete trace).
     */
    public boolean isWiredAnyLoad() {
        return wiredAnyLoad;
    }

    public void markWiredAnyLoad() {
        this.wiredAnyLoad = true;
    }

    public void clearWiredAnyLoad() {
        this.wiredAnyLoad = false;
    }

    /**
     * ID-DEP: some string atom of this vertex reads a delivery of the object-return rule ({@code fwd.rtrack.objret=1}).
     * Read only by {@code HeuristicOrchestrator}'s cross-candidate precedence; always false at objret=0.
     */
    private boolean idDep;

    public boolean isIdDep() {
        return idDep;
    }

    public void markIdDep() {
        this.idDep = true;
    }

    public void clearIdDep() {
        this.idDep = false;
    }

    /**
     * Some string atom of this vertex had a heap-escape event ({@code RecursiveTracking.RAtom.strStored}: a field,
     * static, array-element, container-model, commit or thread-local store). Read only by the accumulator view's variant
     * choice: an admitted extraction that is not stored is stack-confined ({@code ACCUMULATOR_VIEW_SHARED}).
     */
    private boolean stored;

    public boolean isStored() {
        return stored;
    }

    public void markStored() {
        this.stored = true;
    }

    public void clearResourceLimitedTrace() {
        resourceLimitedTrace = false;
    }

    /** The budget-class refusal names of this candidate (null = none); when set the REJECT line reports them. */
    private String budgetRefusal;

    /**
     * Print/guard only: {@code ForwardFixpoint.emit} wrote this vertex's usage list from a string atom's aggregate. A
     * potential origin without it was never seeded; its {@code incompleteTrace} is the blanket non-seeded mark.
     */
    private boolean emittedAtom;

    public boolean isEmittedAtom() {
        return emittedAtom;
    }

    public void markEmittedAtom() {
        emittedAtom = true;
    }

    public void clearEmittedAtom() {
        emittedAtom = false;
    }

    public String getBudgetRefusal() {
        return budgetRefusal;
    }

    public void setBudgetRefusal(String names) {
        this.budgetRefusal = names;
    }

    public boolean isVirtualArgUsage() {
        return virtualArgUsage;
    }

    public void markVirtualArgUsage() {
        this.virtualArgUsage = true;
    }

    public boolean isAccumulatorOp() {
        return accumulatorOp;
    }

    public void markAccumulatorOp() {
        this.accumulatorOp = true;
    }

    public List<String> getOperandSourceLocations() {
        return operandSourceLocations;
    }

    public void setOperandSourceLocations(List<String> operandSourceLocations) {
        this.operandSourceLocations = operandSourceLocations;
    }

    public String describe() {
        StringBuilder sb = new StringBuilder();
        sb.append("V").append(id).append(" ").append(nodeType);
        if (declaringClass != null && methodName != null) {
            sb.append(" ").append(declaringClass).append(".").append(methodName).append("(").append(methodSignature == null ? "" : methodSignature).append(")");
        }
        if (label != null) {
            sb.append(" label=\"").append(escape(label)).append("\"");
        }
        if (literalText != null) {
            sb.append(" text=\"").append(escape(literalText)).append("\" len=").append(literalText.length());
        }
        if (length != UNKNOWN_LENGTH) {
            sb.append(" length=").append(length);
        }
        if (constantValue != 0 || nodeType == SugNodeType.CONSTANT_ARG) {
            sb.append(" const=").append(constantValue);
        }
        if (javaType != null) {
            sb.append(" type=").append(javaType.toJavaName(true));
        }
        sb.append(" @ ").append(sourceLocation == null ? "?" : sourceLocation);
        if (virtualArgUsage) {
            sb.append(" [virtual-arg-usage]");
        }
        if (accumulatorOp) {
            sb.append(" [accumulator-op]");
        }
        return sb.toString();
    }

    private static String escape(String s) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '\\' -> sb.append("\\\\");
                case '"' -> sb.append("\\\"");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                default -> {
                    if (c < 0x20) {
                        sb.append(String.format("\\u%04x", (int) c));
                    } else {
                        sb.append(c);
                    }
                }
            }
        }
        return sb.toString();
    }

    @Override
    public String toString() {
        return describe();
    }
}
