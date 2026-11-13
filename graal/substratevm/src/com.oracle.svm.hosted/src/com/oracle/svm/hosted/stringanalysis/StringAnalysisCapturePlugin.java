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

import java.lang.reflect.Field;
import java.lang.invoke.MethodType;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;

import org.graalvm.collections.Pair;

import com.oracle.graal.pointsto.meta.AnalysisMethod;

import jdk.graal.compiler.java.BytecodeParser;
import jdk.graal.compiler.java.FrameStateBuilder;
import jdk.graal.compiler.nodes.FrameState;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.FixedNode;
import jdk.graal.compiler.nodes.FixedWithNextNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.AddNode;
import jdk.graal.compiler.nodes.calc.SubNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.memory.MemoryKill;
import jdk.vm.ci.code.BytecodePosition;
import jdk.vm.ci.meta.ConstantPool.BootstrapMethodInvocation;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.ResolvedJavaMethod;

public final class StringAnalysisCapturePlugin implements NodePlugin {

    private static final String STRING_CONCAT_FACTORY = "java.lang.invoke.StringConcatFactory";

    private static final Field FRAME_STATE_STACK_FIELD = resolveStackField();

    private static Field resolveStackField() {
        try {
            Field f = FrameStateBuilder.class.getDeclaredField("stack");
            f.setAccessible(true);
            return f;
        } catch (Throwable t) {
            System.err.println("[string-analysis-capture] could not access FrameStateBuilder.stack: " + t);
            return null;
        }
    }

    @Override
    public boolean handleInvoke(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (InlineCacheTrivialMethodNodePlugin.isFlatReentry(b, method)) {
            return false; // the IC's flat call re-parsed on the stock path
        }
        try {
            AnalysisMethod enclosing = (AnalysisMethod) b.getMethod();
            String name = method.getName();
            String decl = method.getDeclaringClass().toJavaName();
            int bci = b.bci();

            if (isAccumulatorOp(decl, name)) {
                String loc = sourceLocation(enclosing, bci);
                ValueNode recvNode = (args.length > 0) ? args[0] : null;
                String recvLoc = valueSourceLocation(recvNode);
                String recvKey = receiverSourceKey(recvNode);
                StringAnalysisFeature.CAPTURED.computeIfAbsent(enclosing, k -> new CopyOnWriteArrayList<>())
                                .add(new AccumulatorOpSite(bci, decl + "." + name, loc, args.length - 1, recvLoc, recvKey));
            }

            if (isSubstring(decl, name) && args.length == 3) {
                boolean unitRange = isUnitRange(args[1], args[2], isInitializer(enclosing));
                int constRange = constRangeLength(args[1], args[2], isInitializer(enclosing));
                String loc = sourceLocation(enclosing, bci);
                StringAnalysisFeature.CAPTURED.computeIfAbsent(enclosing, k -> new CopyOnWriteArrayList<>())
                                .add(new SubstringArithSite(bci, name, loc, unitRange, constRange));
            }

            if (isStringConcat(decl, name, args.length)) {
                String loc = sourceLocation(enclosing, bci);
                List<OperandRef> operands = List.of(toOperandRef(args[0]), toOperandRef(args[1]));
                StringAnalysisFeature.CAPTURED.computeIfAbsent(enclosing, k -> new CopyOnWriteArrayList<>())
                                .add(new ConcatMethodSite(bci, loc, operands));
            }
        } catch (Throwable t) {
            System.err.println("[string-analysis-capture] handleInvoke failed: " + t);
        }
        return false;
    }

    @Override
    public Pair<ResolvedJavaMethod, ValueNode[]> convertInvokeDynamic(GraphBuilderContext b, BootstrapMethodInvocation m) {
        try {
            ResolvedJavaMethod boot = m.getMethod();
            String decl = boot.getDeclaringClass().toJavaName();
            String name = boot.getName();
            if (decl.equals(STRING_CONCAT_FACTORY) &&
                            (name.equals("makeConcat") || name.equals("makeConcatWithConstants"))) {
                AnalysisMethod enclosing = (AnalysisMethod) b.getMethod();
                int bci = b.bci();
                String loc = sourceLocation(enclosing, bci);
                String recipe = readRecipe(b, m, name);
                int dynamicCount = countDynamicOperands(b, m, recipe);
                int constantCount = countConstantOperands(recipe, name);
                int totalOperandCount = dynamicCount + constantCount;
                List<OperandRef> operands = captureOperands(b, dynamicCount);
                List<String> constantOperands = extractConstantOperands(recipe, name, m);
                StringAnalysisFeature.CAPTURED.computeIfAbsent(enclosing, k -> new CopyOnWriteArrayList<>())
                                .add(new ConcatSite(bci, name, loc, dynamicCount, totalOperandCount, operands, constantOperands, recipe, operandKinds(b, m)));
            }
        } catch (Throwable t) {
            System.err.println("[string-analysis-capture] convertInvokeDynamic failed: " + t);
        }
        return null;
    }

    /** The operand kinds of an indy concat (ConcatSite#operandKinds) from its MethodType, or null. */
    private static String operandKinds(GraphBuilderContext b, BootstrapMethodInvocation m) {
        try {
            JavaConstant typeConstant = m.getType();
            MethodType mt = typeConstant != null ? b.getSnippetReflection().asObject(MethodType.class, typeConstant) : null;
            if (mt == null) {
                return null;
            }
            StringBuilder sb = new StringBuilder(mt.parameterCount());
            for (int i = 0; i < mt.parameterCount(); i++) {
                Class<?> t = mt.parameterType(i);
                if (t == String.class) {
                    sb.append('S');
                } else if (t.isPrimitive()) {
                    sb.append('P');
                } else if (t == Integer.class || t == Long.class || t == Boolean.class || t == Character.class || t == Byte.class || t == Short.class ||
                                t == Float.class || t == Double.class) {
                    sb.append('B');
                } else {
                    sb.append('O');
                }
            }
            return sb.toString();
        } catch (Throwable t) {
            return null;
        }
    }

    private static final char RECIPE_DYNAMIC_TAG = '\u0001';
    private static final char RECIPE_CONSTANT_TAG = '\u0002';

    private static String readRecipe(GraphBuilderContext b, BootstrapMethodInvocation m, String name) {
        if (!name.equals("makeConcatWithConstants")) {
            return null;
        }
        try {
            List<JavaConstant> staticArgs = m.getStaticArguments();
            if (staticArgs == null || staticArgs.isEmpty()) {
                return null;
            }
            String recipe = b.getSnippetReflection().asObject(String.class, staticArgs.get(0));
            return recipe != null ? recipe : null;
        } catch (Throwable t) {
            System.err.println("[string-analysis-capture] readRecipe failed: " + t);
            return null;
        }
    }

    private static int countDynamicOperands(GraphBuilderContext b, BootstrapMethodInvocation m, String recipe) {
        if (recipe != null) {
            int count = 0;
            for (int i = 0; i < recipe.length(); i++) {
                if (recipe.charAt(i) == RECIPE_DYNAMIC_TAG) {
                    count++;
                }
            }
            if (count > 0) {
                return count;
            }
        }
        try {
            JavaConstant typeConstant = m.getType();
            if (typeConstant != null) {
                MethodType methodType = b.getSnippetReflection().asObject(MethodType.class, typeConstant);
                if (methodType != null) {
                    return methodType.parameterCount();
                }
            }
        } catch (Throwable t) {
            System.err.println("[string-analysis-capture] countDynamicOperands via MethodType failed: " + t);
        }
        List<JavaConstant> staticArgs = m.getStaticArguments();
        return staticArgs != null ? Math.max(0, staticArgs.size()) : 0;
    }

    private static int countConstantOperands(String recipe, String name) {
        if (recipe == null || !name.equals("makeConcatWithConstants")) {
            return 0;
        }
        int constants = 0;
        int literalLen = 0;
        for (int i = 0; i < recipe.length(); i++) {
            char c = recipe.charAt(i);
            if (c == RECIPE_DYNAMIC_TAG || c == RECIPE_CONSTANT_TAG) {
                if (literalLen > 0) {
                    constants++;
                    literalLen = 0;
                }
                if (c == RECIPE_CONSTANT_TAG) {
                    constants++;
                }
            } else {
                literalLen++;
            }
        }
        if (literalLen > 0) {
            constants++;
        }
        return constants;
    }

    private static List<String> extractConstantOperands(String recipe, String name, BootstrapMethodInvocation m) {
        if (recipe == null || !name.equals("makeConcatWithConstants")) {
            return Collections.emptyList();
        }
        List<JavaConstant> staticArgs = m.getStaticArguments();
        int constantArgIndex = 1;
        List<String> result = new ArrayList<>();
        StringBuilder literal = new StringBuilder();
        for (int i = 0; i < recipe.length(); i++) {
            char c = recipe.charAt(i);
            if (c == RECIPE_DYNAMIC_TAG || c == RECIPE_CONSTANT_TAG) {
                if (!literal.isEmpty()) {
                    result.add(literal.toString());
                    literal.setLength(0);
                }
                if (c == RECIPE_CONSTANT_TAG && staticArgs != null && constantArgIndex < staticArgs.size()) {
                    JavaConstant sc = staticArgs.get(constantArgIndex);
                    constantArgIndex++;
                    if (sc != null) {
                        String s = stringifyConstant(sc);
                        if (s != null) {
                            result.add(s);
                        }
                    }
                }
            } else {
                literal.append(c);
            }
        }
        if (!literal.isEmpty()) {
            result.add(literal.toString());
        }
        return result;
    }

    private static String stringifyConstant(JavaConstant c) {
        if (c == null || c.isNull()) {
            return null;
        }
        if (c.getJavaKind() == jdk.vm.ci.meta.JavaKind.Object) {
            return null;
        }
        if (c.getJavaKind() == jdk.vm.ci.meta.JavaKind.Int) {
            return String.valueOf(c.asInt());
        }
        if (c.getJavaKind() == jdk.vm.ci.meta.JavaKind.Long) {
            return String.valueOf(c.asLong());
        }
        if (c.getJavaKind() == jdk.vm.ci.meta.JavaKind.Boolean) {
            return String.valueOf(c.asInt() != 0);
        }
        if (c.getJavaKind() == jdk.vm.ci.meta.JavaKind.Char) {
            return String.valueOf((char) c.asInt());
        }
        return String.valueOf(c);
    }

    private static List<OperandRef> captureOperands(GraphBuilderContext b, int dynamicCount) {
        if (dynamicCount <= 0 || !(b instanceof BytecodeParser parser)) {
            return Collections.nCopies(dynamicCount, new OperandRef(null, -1));
        }
        FrameStateBuilder fsb = parser.getFrameStateBuilder();
        if (fsb == null || FRAME_STATE_STACK_FIELD == null) {
            return Collections.nCopies(dynamicCount, new OperandRef(null, -1));
        }
        ValueNode[] stack;
        try {
            stack = (ValueNode[]) FRAME_STATE_STACK_FIELD.get(fsb);
        } catch (Throwable t) {
            System.err.println("[string-analysis-capture] frame-state stack peek failed: " + t);
            return Collections.nCopies(dynamicCount, new OperandRef(null, -1));
        }
        int stackSize = fsb.stackSize();
        List<ValueNode> top = new ArrayList<>(dynamicCount);
        for (int idx = stackSize - 1; idx >= 0 && top.size() < dynamicCount; idx--) {
            ValueNode v = stack[idx];
            if (v == FrameState.TWO_SLOT_MARKER) {
                continue;
            }
            top.add(v);
        }
        Collections.reverse(top);
        List<OperandRef> refs = new ArrayList<>(dynamicCount);
        for (int i = 0; i < dynamicCount; i++) {
            if (i < top.size()) {
                refs.add(toOperandRef(top.get(i)));
            } else {
                refs.add(new OperandRef(null, -1));
            }
        }
        return refs;
    }

    private static OperandRef toOperandRef(ValueNode node) {
        if (node == null) {
            return new OperandRef(null, -1);
        }
        BytecodePosition pos = node.getNodeSourcePosition();
        if (pos == null) {
            return new OperandRef(null, -1);
        }
        if (pos.getMethod() instanceof AnalysisMethod am) {
            return new OperandRef(SiteKeys.profileKey(am, pos.getBCI()), pos.getBCI());
        }
        return new OperandRef(null, -1);
    }

    private static String sourceLocation(AnalysisMethod enclosing, int bci) {
        return SiteKeys.profileKey(enclosing, bci);
    }

    private static String valueSourceLocation(ValueNode node) {
        if (node == null) {
            return null;
        }
        BytecodePosition pos = node.getNodeSourcePosition();
        if (pos == null) {
            return null;
        }
        if (pos.getMethod() instanceof AnalysisMethod am) {
            return SiteKeys.profileKey(am, pos.getBCI());
        }
        return null;
    }

    private static String receiverSourceKey(ValueNode node) {
        if (node == null) {
            return null;
        }
        return SiteKeys.sourceKey(node.getNodeSourcePosition());
    }

    private static boolean isAccumulatorOp(String decl, String name) {
        boolean accumulatorType = decl.equals("java.lang.StringBuilder") ||
                        decl.equals("java.lang.StringBuffer") ||
                        decl.contains("AbstractStringBuilder");
        if (!accumulatorType) {
            return false;
        }
        return name.equals("append") || name.equals("insert") || name.equals("delete") || name.equals("replace");
    }

    /**
     * The "unit range" proof {@code end == start + 1} (or {@code start == end - 1}) for the 2-arg {@code substring}. The
     * parent replaces an admitted SINGLE_BYTE substring by {@code SingleByteString.createFromSubstring(s, start)}, which
     * drops {@code end}: the proof must be exact, so "the same operand" must mean the same run-time value at the call.
     */
    static boolean isUnitRange(ValueNode start, ValueNode end, boolean inInitializer) {
        if (end instanceof AddNode add) {
            return (sameValue(start, add.getX(), inInitializer) && isOne(add.getY())) ||
                            (sameValue(start, add.getY(), inInitializer) && isOne(add.getX()));
        }
        if (start instanceof SubNode sub) {
            return sameValue(end, sub.getX(), inInitializer) && isOne(sub.getY());
        }
        return false;
    }

    /**
     * The constant length {@code c} of a 2-arg {@code substring}/{@code subSequence} range, or -1: {@code end == start + c}
     * (or {@code start == end - c}) on the same run-time value ({@link #sameValue}), or both bounds int constants. Read
     * only by the String View rule {@code SV_CONST_SHORT_RANGE} ({@link StringViewHeuristic#refusesConstShortRange}).
     */
    static int constRangeLength(ValueNode start, ValueNode end, boolean inInitializer) {
        Long s = intConstant(start);
        Long e = intConstant(end);
        if (s != null && e != null) {
            return lengthOrUnknown(e - s);
        }
        if (end instanceof AddNode add) {
            Long y = intConstant(add.getY());
            if (y != null && sameValue(start, add.getX(), inInitializer)) {
                return lengthOrUnknown(y);
            }
            Long x = intConstant(add.getX());
            if (x != null && sameValue(start, add.getY(), inInitializer)) {
                return lengthOrUnknown(x);
            }
        }
        if (start instanceof SubNode sub) {
            Long y = intConstant(sub.getY());
            if (y != null && sameValue(end, sub.getX(), inInitializer)) {
                return lengthOrUnknown(y);
            }
        }
        /*
         * Parsing canonicalises "end - c" to "end + (-c)" (SubNode.canonical), so begin = end - c arrives as
         * start = AddNode(end, -c); the length is then -k for the negative constant operand k.
         */
        if (start instanceof AddNode add) {
            Long y = intConstant(add.getY());
            if (y != null && y < 0 && sameValue(end, add.getX(), inInitializer)) {
                return lengthOrUnknown(-y);
            }
            Long x = intConstant(add.getX());
            if (x != null && x < 0 && sameValue(end, add.getY(), inInitializer)) {
                return lengthOrUnknown(-x);
            }
        }
        return -1;
    }

    private static int lengthOrUnknown(long c) {
        return c >= 0 && c <= Integer.MAX_VALUE ? (int) c : -1;
    }

    private static Long intConstant(ValueNode n) {
        if (!(n instanceof ConstantNode c)) {
            return null;
        }
        JavaConstant jc = c.asJavaConstant();
        return jc != null && jc.getJavaKind().isNumericInteger() ? jc.asLong() : null;
    }

    private static boolean isInitializer(ResolvedJavaMethod m) {
        return m != null && (m.isConstructor() || m.isClassInitializer());
    }

    private static boolean sameValue(ValueNode a, ValueNode b, boolean inInitializer) {
        return sameValue(a, b, inInitializer, 0);
    }

    /**
     * Two values are the same only when they are
     * <ul>
     * <li>the same node; or</li>
     * <li>two loads of one non-volatile field of the same receiver value with no memory kill between them on one straight
     * fixed-node chain ({@link MemoryKill#isMemoryKill}: stores, invokes, macro nodes, monitors, volatile accesses, array
     * copies, membars; any control split or merge also ends the chain). Allocations need not be kills: an allocation
     * writes only the new object's default values, and its constructor is an invoke. The second load reads what the first
     * read: the redundant-read elimination the JMM permits for a non-volatile field (as Graal's read elimination does),
     * so an execution in which both reads return the same value is a legal Java execution; or</li>
     * <li>two loads of one static final field outside an initializer: {@code putstatic} of a final field outside its
     * {@code <clinit>} is illegal (class files v53+), {@code Field.set} refuses static finals, and the declaring class's
     * {@code <clinit>} cannot run between the two reads. Inside any initializer only the first two rules apply.</li>
     * </ul>
     * Instance finals get no rule of their own: {@code Field.set} after {@code setAccessible}, {@code Unsafe} and
     * deserialization can write one between two loads, and neither HotSpot nor Graal trusts ordinary instance finals. Two
     * loads of a mutable field separated by a write (e.g. {@code s.substring(pos++, pos + 1)}: length 2) are two values. A
     * non-final {@code @Stable} field counts as mutable.
     */
    private static boolean sameValue(ValueNode a, ValueNode b, boolean inInitializer, int depth) {
        if (depth > 16) {
            return false;
        }
        if (a == b) {
            return true;
        }
        if (a instanceof LoadFieldNode la && b instanceof LoadFieldNode lb) {
            if (!la.field().equals(lb.field()) || la.ordersMemoryAccesses() || lb.ordersMemoryAccesses()) {
                return false;
            }
            boolean oneRead = (la.field().isFinal() && la.field().isStatic() && !inInitializer) || noMemoryKillBetween(la, lb) || noMemoryKillBetween(lb, la);
            return oneRead && sameValue(la.object(), lb.object(), inInitializer, depth + 1);
        }
        return false;
    }

    private static final int MAX_KILL_SCAN = 256;

    /** {@code first} reaches {@code second} along {@code next()} links through fixed nodes none of which is a memory kill. */
    static boolean noMemoryKillBetween(FixedWithNextNode first, FixedNode second) {
        FixedNode cur = first.next();
        for (int i = 0; cur != null && i < MAX_KILL_SCAN; i++) {
            if (cur == second) {
                return true;
            }
            if (!(cur instanceof FixedWithNextNode fwn) || MemoryKill.isMemoryKill(cur)) {
                return false;
            }
            cur = fwn.next();
        }
        return false;
    }

    private static boolean isOne(ValueNode n) {
        if (!(n instanceof ConstantNode c)) {
            return false;
        }
        JavaConstant jc = c.asJavaConstant();
        return jc != null && jc.getJavaKind().isNumericInteger() && jc.asLong() == 1L;
    }

    private static boolean isSubstring(String decl, String name) {
        return decl.equals("java.lang.String") && (name.equals("substring") || name.equals("subSequence"));
    }

    private static boolean isStringConcat(String decl, String name, int argCount) {
        return decl.equals("java.lang.String") && name.equals("concat") && argCount == 2;
    }
}
