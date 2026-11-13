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

import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.CHA_CAP;

import java.util.List;

import jdk.graal.compiler.nodes.IndirectCallTargetNode;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;

import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.svm.hosted.phases.StringAnalysisChildInlining;
import com.oracle.svm.hosted.stringanalysis.ContainerAtoms.ContextElement;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Sink;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.CallPath;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.MethodContext;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.AtomKind;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtom;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.TargetCheck;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.TargetRule;

/**
 * The reflection bridge's crossings of {@link RecursiveTracking}: the VM function-pointer call nodes resolved through
 * {@link ReflectionBridge}.
 */
final class ReflectionBridgeCrossings {
    private final RecursiveTracking rt;

    ReflectionBridgeCrossings(RecursiveTracking rt) {
        this.rt = rt;
    }

    /** The bridged targets of an indirect invoke, or null (not a reflection edge: the caller refuses UNCLASSIFIED_ACCESS). */
    private List<AnalysisMethod> bridgedTargets(LocalFlowGraph frame, Invoke inv) {
        return inv != null ? rt.reflBridge().targetsOf(frame, inv) : null;
    }

    boolean bridgedInvokeUsage(RAtom atom, LocalFlowGraph frame, ValueNode n, IndirectCallTargetNode ict, CallPath path, MethodContext mctx) {
        Invoke inv = ict.invoke();
        List<AnalysisMethod> targets = bridgedTargets(frame, inv);
        if (targets == null) {
            return false;
        }
        if (!ict.arguments().contains(n)) {
            return false; // the walked object is not an argument (never the word address): not a crossing
        }
        if (targets == ReflectionBridge.UNPLACED) {
            rt.refuse(atom.table, RTrackRefusal.MISSING_IR); // an OUTER call the bridge build did not place
            return true;
        }
        ReflectionBridge rb = rt.reflBridge();
        if (rb.readFailures > 0 || rb.chaReadFailures > 0) {
            rt.e3Unresolved.incrementAndGet();
            rt.refuse(atom.table, RTrackRefusal.UNRESOLVED_VALUE); // an accessor whose hosted fields cannot be read
            return true;
        }
        if (targets.isEmpty()) {
            rt.refuse(atom.table, RTrackRefusal.NO_TARGET);
            return true;
        }
        if (targets.size() > CHA_CAP) {
            rt.e3ChaCap.incrementAndGet();
            rt.refuse(atom.table, RTrackRefusal.CHA_FAN_CAP);
            return true;
        }
        rt.e3Crossings.incrementAndGet();
        LocalFlowGraph.LocalVertex callVertex = rt.callVertexOf(frame, inv);
        CallPath pushed = CallPath.push(frame, callVertex, mctx, path);
        for (AnalysisMethod t : targets) {
            TargetCheck tc = rt.targetCheck(t); // the shared per-target rules
            if (tc.rule() == TargetRule.THREAD_LOCAL) {
                rt.threadLocal.tlUnmodelled(atom.table, "reflective-tl-op"); // a translated thread-local operation invoked reflectively
                continue;
            }
            if (tc.rule() == TargetRule.MODEL || tc.rule() == TargetRule.CLOSED) {
                // a modelled JDK method (or an unlisted one of a closed class) invoked reflectively: refused by name
                rt.models.unmodelled(atom.table, tc.rule() == TargetRule.MODEL ? tc.op().family() : tc.closed(), "reflective/" + t.format("%H.%n(%p)"));
                continue;
            }
            boolean monitorOp = tc.rule() == TargetRule.MONITOR;
            // A reflective call whose receiver is the string and whose target is stringy-declared is a
            // terminal usage as well (the INNER call's slot 0 is the target's receiver)
            boolean terminal = atom.kind == AtomKind.STRING && !ict.arguments().isEmpty() && ict.arguments().get(0) == n && StringAtoms.isTerminalTarget(t);
            if (terminal) {
                rt.stringTerminal(atom, frame, n, inv, callVertex, t, null, false, path, mctx);
                rt.cmpBridgeReceiver(atom, frame, inv.asNode(), n, t);
                boolean other = false;
                for (int slot = 1; slot < ict.arguments().size(); slot++) {
                    other |= ict.arguments().get(slot) == n;
                }
                if (!other) {
                    continue;
                }
            }
            LocalFlowGraph calleeFrame = rt.bridge.frameOf(t);
            StructuredGraph g = calleeFrame != null ? rt.graphOf(calleeFrame) : null;
            if (calleeFrame == null && rt.dropDeadTarget(t, "fwd-e3")) {
                continue;
            }
            if (calleeFrame == null || g == null) {
                rt.missingIr("fwd-e3-callee" + (calleeFrame == null ? "/noLfg/" : "/noGraph/"), t);
                rt.refuse(atom.table, RTrackRefusal.MISSING_IR);
                continue;
            }
            ContextPolicy.FoldPush fp = null; // recursion fold: as at the ordinary crossing
            boolean fpDone = false;
            for (int slot = 0; slot < ict.arguments().size(); slot++) {
                if (ict.arguments().get(slot) != n || terminal && slot == 0) {
                    continue;
                }
                if (monitorOp && slot == MonitorPrimitive.OBJECT_SLOT) {
                    rt.monitorObservations.incrementAndGet(); // the object slot of a monitor operation is observed
                    continue;
                }
                // The equals argument at a bridged String.equals target. A reflective call has
                // no Phase-A equals site (the stub calls String.equals directly), so the parent can never redirect the
                // argument: refused by name, never entered (hasPhaseASite = false).
                if (StringAtoms.equalsArgRow(atom.kind == AtomKind.STRING, slot, StringAtoms.isStringEquals(t), false) == StringAtoms.EqArgRow.NO_SITE) {
                    rt.eqArgNoSite.incrementAndGet();
                    rt.refuse(atom.table, RTrackRefusal.EQUALS_ARG_NO_SITE);
                    continue;
                }
                // The compareTo mirror: as the equals argument, a reflective compareTo(String) call has no Phase-A site
                if (rt.cmpArgument(atom, frame, inv.asNode(), n, t, atom.kind == AtomKind.STRING, slot, false)) {
                    continue;
                }
                // Builder-append mirror: a reflective call of an entry point has no mirrorable site either
                StringAtoms.MirrorArgRow mrow = StringAtoms.mirrorArgRow(AppendMirror.on(), atom.kind == AtomKind.STRING, slot, AppendMirror.stringSlot(t), false);
                if (mrow == StringAtoms.MirrorArgRow.NO_SITE) {
                    AppendMirror.recordNoSite(t);
                    rt.refuse(atom.table, RTrackRefusal.MIRROR_ARG_NO_SITE);
                    continue;
                }
                boolean receiverSlot = slot == 0 && !t.isStatic();
                ParameterNode param = receiverSlot ? null : g.getParameter(slot);
                if (!receiverSlot && param == null) {
                    continue; // slot-wise: the target never reads that argument
                }
                if (!fpDone) {
                    fp = rt.foldedPush(atom, frame, callVertex, mctx, path, calleeFrame);
                    fpDone = true;
                }
                CallPath tpushed = fp != null ? fp.path() : pushed;
                if (receiverSlot) {
                    rt.enterReceiver(atom, calleeFrame, g, tpushed, rt.enterMaybeFolded(fp, mctx, frame, inv, t, true, atom));
                    continue;
                }
                rt.enqueueWalk(atom, calleeFrame, param, tpushed, rt.enterMaybeFolded(fp, mctx, frame, inv, t, false, atom));
            }
        }
        return true;
    }

    /** Backward at the result of a bridged edge: the returns of every target (the invokeResultCase rule). */
    boolean bridgedResultCase(LocalFlowGraph frame, Invoke inv, MethodContext mctx, CallPath path, Sink sink) {
        List<AnalysisMethod> targets = bridgedTargets(frame, inv);
        if (targets == null) {
            return false;
        }
        rt.e3ResultCases.incrementAndGet();
        if (targets == ReflectionBridge.UNPLACED) {
            rt.refuse(sink, RTrackRefusal.MISSING_IR); // an OUTER call the bridge build did not place
            return true;
        }
        ReflectionBridge rb = rt.reflBridge();
        if (rb.readFailures > 0 || rb.chaReadFailures > 0) {
            rt.refuse(sink, RTrackRefusal.UNRESOLVED_VALUE);
            return true;
        }
        if (targets.isEmpty()) {
            rt.refuse(sink, RTrackRefusal.NO_TARGET);
            return true;
        }
        if (targets.size() > CHA_CAP) {
            rt.e3ChaCap.incrementAndGet();
            rt.refuse(sink, RTrackRefusal.CHA_FAN_CAP);
            return true;
        }
        LocalFlowGraph.LocalVertex callVertex = rt.callVertexOf(frame, inv);
        CallPath pushed = CallPath.pushBackward(frame, callVertex, mctx, path); // the backward path bound
        for (AnalysisMethod t : targets) {
            TargetCheck tc = rt.targetCheck(t); // the shared per-target rules
            if (tc.rule() == TargetRule.THREAD_LOCAL) {
                rt.threadLocal.tlUnmodelled(sink, "reflective-tl-op");
                continue;
            }
            if (tc.rule() == TargetRule.MODEL || tc.rule() == TargetRule.CLOSED) {
                rt.models.unmodelled(sink, tc.rule() == TargetRule.MODEL ? tc.op().family() : tc.closed(), "reflective/" + t.format("%H.%n(%p)"));
                continue;
            }
            LocalFlowGraph calleeFrame = rt.bridge.frameOf(t);
            StructuredGraph g = calleeFrame != null ? rt.graphOf(calleeFrame) : null;
            if (calleeFrame == null && rt.dropDeadTarget(t, "bwd-e3")) {
                continue;
            }
            if (g == null) {
                rt.missingIr("bwd-e3-callee" + (calleeFrame == null ? "/noLfg/" : "/noGraph/"), t);
                rt.refuse(sink, RTrackRefusal.MISSING_IR);
                continue;
            }
            MethodContext calleeMctx = t.isStatic()
                            ? MethodContext.staticCtx(new ContextElement(rt.bridge.methodOf(frame), StringAnalysisChildInlining.pointsToBci(inv)), mctx != null ? mctx : MethodContext.UNKNOWN)
                            : MethodContext.UNKNOWN;
            for (ReturnNode ret : g.getNodes(ReturnNode.TYPE)) {
                if (ret.result() != null) {
                    rt.backward(calleeFrame, ret.result(), calleeMctx, pushed, sink);
                }
            }
        }
        return true;
    }
}
