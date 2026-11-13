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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Collections;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.Phaser;
import java.util.concurrent.RecursiveAction;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.LongAdder;

import com.oracle.graal.pointsto.flow.FormalParamTypeFlow;
import com.oracle.graal.pointsto.flow.FormalReturnTypeFlow;
import com.oracle.graal.pointsto.flow.TypeFlow;

enum UsageRole {
    RECEIVER,
    PARAMETER,
    NONE
}

/** {@code dispatchOwner}: the emitted {@code TransferFacts.UsageFact#dispatchOwner} (the dispatch-owner rule; null = the site's owner). */
record UsageTag(SugVertex usageSite, UsageRole role, int paramIndex, String dispatchOwner) {
    UsageTag(SugVertex usageSite, UsageRole role, int paramIndex) {
        this(usageSite, role, paramIndex, null);
    }
}

record SourceTag(SugVertex creationSite, UsageRole role, int paramIndex) {
}

public final class UsageSourceBuilder {

    private static final int MAX_FIXPOINT_PASSES = 32;

    private UsageSourceBuilder() {
    }

    public static void build(StringUtilizationGraph graph) {
        build(graph, false);
    }

    /** Builds the usage sources of {@code graph} unless they are built already (each heuristic calls this first). */
    static void ensureBuilt(StringUtilizationGraph graph) {
        if (!graph.isUsageSourceBuilt()) {
            build(graph);
        }
    }

    public static void build(StringUtilizationGraph graph, boolean parallelUsb) {
        long totalStart = System.nanoTime();
        List<SugVertex> vertices = graph.getVertices();
        int numVertices = vertices.size();
        int maxId = -1;
        for (SugVertex v : vertices) {
            if (v.getId() > maxId) {
                maxId = v.getId();
            }
        }
        int arrSize = maxId + 1;

        long t0 = System.nanoTime();
        Map<UsageTag, Integer> tagIndex = new HashMap<>();
        List<UsageTag> tagList = new ArrayList<>();
        Map<SourceTag, Integer> sourceTagIndex = new HashMap<>();
        List<SourceTag> sourceTagList = new ArrayList<>();
        BitSet[] tagMap = new BitSet[arrSize];
        Set<SugVertex> seeds = new HashSet<>(numVertices);

        for (SugVertex usageSite : vertices) {
            if (!isUsageSite(usageSite)) {
                continue;
            }
            for (SugEdge edge : usageSite.getInEdges()) {
                UsageRole role;
                int paramIndex;
                switch (edge.getEdgeType()) {
                    case QUALIFIER -> {
                        role = UsageRole.RECEIVER;
                        paramIndex = -1;
                    }
                    case PARAMETER -> {
                        role = UsageRole.PARAMETER;
                        paramIndex = edge.getParamIndex();
                    }
                    case CONCAT_LEFT, CONCAT_RIGHT -> {
                        role = UsageRole.NONE;
                        paramIndex = -1;
                    }
                    case DATAFLOW, JDK -> {
                        role = switch (edge.getFlowRole()) {
                            case RECEIVER -> UsageRole.RECEIVER;
                            case ARG -> UsageRole.PARAMETER;
                            case NONE -> UsageRole.NONE;
                        };
                        paramIndex = -1;
                    }
                    default -> {
                        continue;
                    }
                }
                SugVertex from = edge.getFrom();
                UsageTag tag = new UsageTag(usageSite, role, paramIndex);
                Integer idx = tagIndex.get(tag);
                if (idx == null) {
                    idx = tagList.size();
                    tagIndex.put(tag, idx);
                    tagList.add(tag);
                }
                BitSet fromTags = tagMap[from.getId()];
                if (fromTags == null) {
                    fromTags = new BitSet(tagList.size());
                    tagMap[from.getId()] = fromTags;
                }
                fromTags.set(idx);
                seeds.add(from);
            }
        }
        System.out.println("[sug-perf] UsageSourceBuilder seed pass: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (seeds=" + seeds.size() + ", tags=" + tagList.size() + ", vertices=" +
                        numVertices + ")");

        if (parallelUsb) {
            buildParallel(graph, arrSize, tagList, sourceTagIndex, sourceTagList, tagMap, seeds, totalStart);
            return;
        }

        long totalBfsBudget = 0L;
        long totalRecordedPairs = 0L;
        long[] totalCreationTime = {0L};
        long[] totalPassthroughTime = {0L};
        long[] totalRecordPairTime = {0L};
        long[] totalBitsetOrTime = {0L};
        boolean[] visited = new boolean[arrSize];
        BitSet[] lastSnapshot = new BitSet[arrSize];
        boolean[] inNextWork = new boolean[arrSize];
        Deque<SugVertex> nextWork = new ArrayDeque<>(seeds.size());
        for (SugVertex s : seeds) {
            int sid = s.getId();
            if (isCreationSite(s) || isPassthrough(s)) {
                if (!inNextWork[sid]) {
                    inNextWork[sid] = true;
                    nextWork.add(s);
                }
            }
        }
        int pass = 0;
        long newPairsThisPass;
        do {
            long passStart = System.nanoTime();
            Deque<SugVertex> work = nextWork;
            nextWork = new ArrayDeque<>();
            Arrays.fill(inNextWork, false);
            Arrays.fill(visited, false);
            for (SugVertex s : work) {
                visited[s.getId()] = true;
            }

            long visitedCount = 0;
            long passthroughCount = 0;
            long creationHitCount = 0;
            newPairsThisPass = 0;
            long skippedInEdgesThis = 0L;
            long creationTimeThis = 0L;
            long passthroughTimeThis = 0L;
            long recordPairTimeThis = 0L;
            long bitsetOrTimeThis = 0L;
            while (!work.isEmpty()) {
                SugVertex current = work.removeFirst();
                visitedCount++;
                int cid = current.getId();
                BitSet tags = tagMap[cid];
                if (tags == null || tags.isEmpty()) {
                    lastSnapshot[cid] = tags == null ? null : (BitSet) tags.clone();
                    continue;
                }
                BitSet snapshot = lastSnapshot[cid];
                if (snapshot != null && snapshot.equals(tags)) {
                    skippedInEdgesThis += current.getInEdges().size();
                    continue;
                }
                BitSet delta;
                if (snapshot == null) {
                    delta = (BitSet) tags.clone();
                } else {
                    delta = (BitSet) tags.clone();
                    delta.andNot(snapshot);
                }
                if (delta.isEmpty()) {
                    skippedInEdgesThis += current.getInEdges().size();
                    lastSnapshot[cid] = (BitSet) tags.clone();
                    continue;
                }

                if (isCreationSite(current)) {
                    creationHitCount++;
                    long cStart = System.nanoTime();
                    BitSet rec = current.getUsageTags();
                    for (int i = delta.nextSetBit(0); i >= 0; i = delta.nextSetBit(i + 1)) {
                        if (rec.get(i)) {
                            continue;
                        }
                        rec.set(i);
                        newPairsThisPass++;
                        totalRecordedPairs++;
                        UsageTag tag = tagList.get(i);
                        long rpStart = System.nanoTime();
                        SugVertex usageSite = tag.usageSite();
                        SourceTag sourceTag = new SourceTag(current, tag.role(), tag.paramIndex());
                        Integer j = sourceTagIndex.get(sourceTag);
                        if (j == null) {
                            j = sourceTagList.size();
                            sourceTagIndex.put(sourceTag, j);
                            sourceTagList.add(sourceTag);
                        }
                        usageSite.getSourceTags().set(j);
                        recordPairTimeThis += System.nanoTime() - rpStart;
                    }
                    creationTimeThis += System.nanoTime() - cStart;
                }
                if (isPassthrough(current)) {
                    passthroughCount++;
                    long pStart = System.nanoTime();
                    BitSet recvSubset = roleSubset(delta, tagList, UsageRole.RECEIVER);
                    BitSet argSubset = roleSubset(delta, tagList, UsageRole.PARAMETER);
                    for (SugEdge edge : current.getInEdges()) {
                        SugVertex from = edge.getFrom();
                        int fid = from.getId();
                        BitSet fromTags = tagMap[fid];
                        if (fromTags == null) {
                            fromTags = new BitSet(tagList.size());
                            tagMap[fid] = fromTags;
                        }
                        long orStart = System.nanoTime();
                        fromTags.or(roleSubsetForEdge(delta, recvSubset, argSubset, edge));
                        bitsetOrTimeThis += System.nanoTime() - orStart;
                        if (isCreationSite(from) || isPassthrough(from)) {
                            if (!visited[fid]) {
                                visited[fid] = true;
                                work.add(from);
                            }
                            if (!inNextWork[fid]) {
                                inNextWork[fid] = true;
                                nextWork.add(from);
                            }
                        }
                    }
                    passthroughTimeThis += System.nanoTime() - pStart;
                }
                lastSnapshot[cid] = (BitSet) tags.clone();
            }
            long passMs = (System.nanoTime() - passStart) / 1_000_000;
            totalBfsBudget += passMs;
            totalCreationTime[0] += creationTimeThis;
            totalPassthroughTime[0] += passthroughTimeThis;
            totalRecordPairTime[0] += recordPairTimeThis;
            totalBitsetOrTime[0] += bitsetOrTimeThis;
            System.out.println("[sug-perf] UsageSourceBuilder pass " + pass + ": " + passMs + "ms (visited=" + visitedCount + ", passthrough=" + passthroughCount + ", creationHit=" +
                            creationHitCount + ", newPairs=" + newPairsThisPass + ", skippedInEdges=" + skippedInEdgesThis + ")");
            System.out.println("[sug-perf] UsageSourceBuilder pass " + pass + " split: creation=" + (creationTimeThis / 1_000_000) + "ms, passthrough=" + (passthroughTimeThis / 1_000_000) +
                            "ms, recordPair=" + (recordPairTimeThis / 1_000_000) + "ms, bitsetOr=" + (bitsetOrTimeThis / 1_000_000) + "ms");
            pass++;
            if (newPairsThisPass > 0 && pass >= MAX_FIXPOINT_PASSES) {
                System.out.println("[sug-perf] UsageSourceBuilder: reached max passes (" + MAX_FIXPOINT_PASSES + ") without fixpoint; last pass recorded " + newPairsThisPass +
                                " new pairs (precision may be incomplete)");
                break;
            }
        } while (newPairsThisPass > 0);
        if (newPairsThisPass == 0) {
            System.out.println("[sug-perf] UsageSourceBuilder fixpoint reached at pass " + pass + " (0 new pairs on the final pass)");
        }
        System.out.println("[sug-perf] UsageSourceBuilder total BFS: " + totalBfsBudget + "ms, total recorded pairs: " + totalRecordedPairs);
        System.out.println("[sug-perf] UsageSourceBuilder totals: creation=" + (totalCreationTime[0] / 1_000_000) + "ms, passthrough=" + (totalPassthroughTime[0] / 1_000_000) + "ms, recordPair=" +
                        (totalRecordPairTime[0] / 1_000_000) + "ms, bitsetOr=" + (totalBitsetOrTime[0] / 1_000_000) + "ms");
        graph.setUsageTags(tagList);
        graph.setSourceTags(sourceTagList);
        graph.setUsageSourceBuilt();
        System.out.println("[sug-perf] UsageSourceBuilder total: " + ((System.nanoTime() - totalStart) / 1_000_000) + "ms");
    }

    private static final int STRIPES = 1 << 13;

    private static void buildParallel(StringUtilizationGraph graph, int arrSize,
                    List<UsageTag> tagList,
                    Map<SourceTag, Integer> sourceTagIndex, List<SourceTag> sourceTagList,
                    BitSet[] tagMap, Set<SugVertex> seeds, long totalStart) {
        ConcurrentHashMap<SourceTag, Integer> concurrentSourceTagIndex;
        if (sourceTagIndex instanceof ConcurrentHashMap) {
            concurrentSourceTagIndex = (ConcurrentHashMap<SourceTag, Integer>) sourceTagIndex;
        } else {
            concurrentSourceTagIndex = new ConcurrentHashMap<>(sourceTagIndex);
        }
        List<SourceTag> concurrentSourceTagList = Collections.synchronizedList(sourceTagList);
        long totalBfsBudget = 0L;
        long totalRecordedPairs = 0L;
        Object[] stripes = new Object[STRIPES];
        for (int i = 0; i < STRIPES; i++) {
            stripes[i] = new Object();
        }
        BitSet[] lastSnapshot = new BitSet[arrSize];
        AtomicBoolean[] inNextWork = new AtomicBoolean[arrSize];
        for (int i = 0; i < arrSize; i++) {
            inNextWork[i] = new AtomicBoolean();
        }
        ConcurrentLinkedQueue<SugVertex> nextWork = new ConcurrentLinkedQueue<>();
        for (SugVertex s : seeds) {
            int sid = s.getId();
            if (isCreationSite(s) || isPassthrough(s)) {
                if (inNextWork[sid].compareAndSet(false, true)) {
                    nextWork.add(s);
                }
            }
        }
        ForkJoinPool pool = new ForkJoinPool(Runtime.getRuntime().availableProcessors());
        try {
            int pass = 0;
            long newPairsThisPass;
            do {
                long passStart = System.nanoTime();
                ConcurrentLinkedQueue<SugVertex> work = nextWork;
                nextWork = new ConcurrentLinkedQueue<>();
                for (int i = 0; i < arrSize; i++) {
                    inNextWork[i].set(false);
                }
                AtomicBoolean[] visited = new AtomicBoolean[arrSize];
                for (int i = 0; i < arrSize; i++) {
                    visited[i] = new AtomicBoolean();
                }
                LongAdder newPairsCounter = new LongAdder();
                LongAdder totalRecordedPairsCounter = new LongAdder();
                totalRecordedPairsCounter.add(totalRecordedPairs);
                LongAdder visitedCount = new LongAdder();
                List<SugVertex> initialWork = new ArrayList<>();
                while (!work.isEmpty()) {
                    SugVertex s = work.poll();
                    visited[s.getId()].set(true);
                    initialWork.add(s);
                }
                Phaser phaser = new Phaser(1);
                for (SugVertex seed : initialWork) {
                    phaser.register();
                    pool.execute(new UsbTask(seed, tagMap, lastSnapshot, visited, inNextWork, nextWork,
                                    tagList, concurrentSourceTagIndex, concurrentSourceTagList, stripes,
                                    newPairsCounter, totalRecordedPairsCounter, visitedCount, phaser));
                }
                phaser.arriveAndAwaitAdvance();
                newPairsThisPass = newPairsCounter.sum();
                totalRecordedPairs = totalRecordedPairsCounter.sum();
                long passMs = (System.nanoTime() - passStart) / 1_000_000;
                totalBfsBudget += passMs;
                System.out.println("[sug-perf] UsageSourceBuilder pass " + pass + ": " + passMs + "ms (visited=" + visitedCount.sum() + ", newPairs=" + newPairsThisPass + ")");
                pass++;
                if (newPairsThisPass > 0 && pass >= MAX_FIXPOINT_PASSES) {
                    System.out.println("[sug-perf] UsageSourceBuilder: reached max passes (" + MAX_FIXPOINT_PASSES + ") without fixpoint; last pass recorded " + newPairsThisPass +
                                    " new pairs (precision may be incomplete)");
                    break;
                }
            } while (newPairsThisPass > 0);
            if (newPairsThisPass == 0) {
                System.out.println("[sug-perf] UsageSourceBuilder fixpoint reached at pass " + pass + " (0 new pairs on the final pass)");
            }
        } finally {
            pool.shutdown();
        }
        sourceTagIndex.clear();
        sourceTagIndex.putAll(concurrentSourceTagIndex);
        System.out.println("[sug-perf] UsageSourceBuilder total BFS: " + totalBfsBudget + "ms, total recorded pairs: " + totalRecordedPairs);
        graph.setUsageTags(tagList);
        graph.setSourceTags(sourceTagList);
        graph.setUsageSourceBuilt();
        System.out.println("[sug-perf] UsageSourceBuilder total: " + ((System.nanoTime() - totalStart) / 1_000_000) + "ms");
    }

    private static final class UsbTask extends RecursiveAction {
        private static final long serialVersionUID = 1L;
        private final SugVertex current;
        private final BitSet[] tagMap;
        private final BitSet[] lastSnapshot;
        private final AtomicBoolean[] visited;
        private final AtomicBoolean[] inNextWork;
        private final ConcurrentLinkedQueue<SugVertex> nextWork;
        private final List<UsageTag> tagList;
        private final ConcurrentHashMap<SourceTag, Integer> sourceTagIndex;
        private final List<SourceTag> sourceTagList;
        private final Object[] stripes;
        private final LongAdder newPairsCounter;
        private final LongAdder totalRecordedPairsCounter;
        private final LongAdder visitedCount;
        private final Phaser phaser;

        UsbTask(SugVertex current, BitSet[] tagMap, BitSet[] lastSnapshot, AtomicBoolean[] visited,
                        AtomicBoolean[] inNextWork, ConcurrentLinkedQueue<SugVertex> nextWork,
                        List<UsageTag> tagList, ConcurrentHashMap<SourceTag, Integer> sourceTagIndex,
                        List<SourceTag> sourceTagList, Object[] stripes, LongAdder newPairsCounter,
                        LongAdder totalRecordedPairsCounter, LongAdder visitedCount, Phaser phaser) {
            this.current = current;
            this.tagMap = tagMap;
            this.lastSnapshot = lastSnapshot;
            this.visited = visited;
            this.inNextWork = inNextWork;
            this.nextWork = nextWork;
            this.tagList = tagList;
            this.sourceTagIndex = sourceTagIndex;
            this.sourceTagList = sourceTagList;
            this.stripes = stripes;
            this.newPairsCounter = newPairsCounter;
            this.totalRecordedPairsCounter = totalRecordedPairsCounter;
            this.visitedCount = visitedCount;
            this.phaser = phaser;
        }

        @Override
        protected void compute() {
            try {
                processVertex(current);
            } finally {
                phaser.arrive();
            }
        }

        private void processVertex(SugVertex cur) {
            int cid = cur.getId();
            visitedCount.increment();
            Object cidLock = stripes[cid & (STRIPES - 1)];
            BitSet delta;
            BitSet recvSubset;
            BitSet argSubset;
            synchronized (cidLock) {
                BitSet tags = tagMap[cid];
                if (tags == null || tags.isEmpty()) {
                    lastSnapshot[cid] = tags == null ? null : (BitSet) tags.clone();
                    return;
                }
                BitSet snapshot = lastSnapshot[cid];
                if (snapshot != null && snapshot.equals(tags)) {
                    return;
                }
                if (snapshot == null) {
                    delta = (BitSet) tags.clone();
                } else {
                    delta = (BitSet) tags.clone();
                    delta.andNot(snapshot);
                }
                lastSnapshot[cid] = (BitSet) tags.clone();
                recvSubset = roleSubset(delta, tagList, UsageRole.RECEIVER);
                argSubset = roleSubset(delta, tagList, UsageRole.PARAMETER);
            }
            if (delta.isEmpty()) {
                return;
            }
            if (isCreationSite(cur)) {
                BitSet rec = cur.getUsageTags();
                for (int i = delta.nextSetBit(0); i >= 0; i = delta.nextSetBit(i + 1)) {
                    if (rec.get(i)) {
                        continue;
                    }
                    rec.set(i);
                    newPairsCounter.increment();
                    totalRecordedPairsCounter.increment();
                    UsageTag tag = tagList.get(i);
                    SugVertex usageSite = tag.usageSite();
                    SourceTag sourceTag = new SourceTag(cur, tag.role(), tag.paramIndex());
                    Integer jx = sourceTagIndex.get(sourceTag);
                    int j;
                    if (jx == null) {
                        synchronized (sourceTagList) {
                            jx = sourceTagIndex.get(sourceTag);
                            if (jx == null) {
                                j = sourceTagList.size();
                                sourceTagList.add(sourceTag);
                                sourceTagIndex.put(sourceTag, j);
                            } else {
                                j = jx;
                            }
                        }
                    } else {
                        j = jx;
                    }
                    synchronized (stripes[usageSite.getId() & (STRIPES - 1)]) {
                        usageSite.getSourceTags().set(j);
                    }
                }
            }
            if (isPassthrough(cur)) {
                List<SugEdge> inEdges = cur.getInEdges();
                for (SugEdge edge : inEdges) {
                    SugVertex from = edge.getFrom();
                    int fid = from.getId();
                    Object fidLock = stripes[fid & (STRIPES - 1)];
                    synchronized (fidLock) {
                        BitSet fromTags = tagMap[fid];
                        if (fromTags == null) {
                            fromTags = new BitSet(tagList.size());
                            tagMap[fid] = fromTags;
                        }
                        fromTags.or(roleSubsetForEdge(delta, recvSubset, argSubset, edge));
                    }
                    if (isCreationSite(from) || isPassthrough(from)) {
                        if (inNextWork[fid].compareAndSet(false, true)) {
                            nextWork.add(from);
                        }
                        if (visited[fid].compareAndSet(false, true)) {
                            phaser.register();
                            new UsbTask(from, tagMap, lastSnapshot, visited, inNextWork, nextWork,
                                            tagList, sourceTagIndex, sourceTagList, stripes,
                                            newPairsCounter, totalRecordedPairsCounter, visitedCount, phaser).fork();
                        }
                    }
                }
            }
        }
    }

    /**
     * The subset of {@code delta} whose tags have the given {@code role} (partitions a passthrough vertex's delta once,
     * so same-role tags propagate only through same-role and NONE edges).
     */
    private static BitSet roleSubset(BitSet delta, List<UsageTag> tagList, UsageRole role) {
        if (delta.isEmpty()) {
            return new BitSet();
        }
        BitSet subset = new BitSet(delta.size());
        for (int i = delta.nextSetBit(0); i >= 0; i = delta.nextSetBit(i + 1)) {
            if (tagList.get(i).role() == role) {
                subset.set(i);
            }
        }
        return subset;
    }

    /**
     * The tag subset to OR into {@code from} via the given in-edge (same-role rule): RECEIVER tags flow through
     * RECEIVER and NONE edges, PARAMETER tags through ARG and NONE edges, NONE tags everywhere, and NONE-flow edges
     * receive everything.
     */
    private static BitSet roleSubsetForEdge(BitSet delta, BitSet recvSubset, BitSet argSubset, SugEdge edge) {
        return switch (edge.getFlowRole()) {
            case RECEIVER -> {
                BitSet toProp = (BitSet) recvSubset.clone();
                toProp.or(delta);
                toProp.andNot(argSubset);
                yield toProp;
            }
            case ARG -> {
                BitSet toProp = (BitSet) argSubset.clone();
                toProp.or(delta);
                toProp.andNot(recvSubset);
                yield toProp;
            }
            case NONE -> delta;
        };
    }

    private static boolean isUsageSite(SugVertex v) {
        SugNodeType t = v.getNodeType();
        return t == SugNodeType.STRING_METHOD_CALL ||
                        t == SugNodeType.JDK_LIBRARY_CALL ||
                        t == SugNodeType.CONCAT_EXPRESSION;
    }

    private static boolean isCreationSite(SugVertex v) {
        SugNodeType t = v.getNodeType();
        return t == SugNodeType.STRING_LITERAL ||
                        t == SugNodeType.NEW_STRING ||
                        t == SugNodeType.STRING_METHOD_CALL ||
                        t == SugNodeType.JDK_LIBRARY_CALL ||
                        t == SugNodeType.CONCAT_EXPRESSION ||
                        t == SugNodeType.NEW_ACCUMULATOR;
    }

    private static boolean isPassthrough(SugVertex v) {
        SugNodeType t = v.getNodeType();
        if (t == SugNodeType.RETURN) {
            // A RETURN vertex whose source flow is a saturated FormalReturnTypeFlow is not a passthrough: a saturated
            // formal return conflates all callers of the method, so backward usage-tag propagation through it would
            // leak a usage tag from one caller's downstream to every other caller's argument path, with no real
            // dataflow between them. Stopping propagation there avoids these false cross-caller associations, but
            // also cuts the caller's own argument -> return -> use association, so it is not sound on its own; it is
            // harmless only because ForwardFixpoint.emit is the sole source of usage tags under the defaults (it
            // overwrites these). Non-saturated returns remain passthrough.
            TypeFlow<?> src = v.getSourceFlow();
            if (src instanceof FormalReturnTypeFlow && src.isSaturated()) {
                return false;
            }
            return true;
        }
        if (t == SugNodeType.VARIABLE) {
            // Likewise a VARIABLE vertex whose source flow is a saturated FormalParamTypeFlow (e.g. the receiver
            // param of StringBuilder.append(Object), with in-edges from all callers' builders) is not a passthrough.
            // The same holds as for RETURN: the cut also drops the caller's own association (not sound on its own;
            // harmless only because ForwardFixpoint.emit is the sole usage-tag source under the defaults).
            // Non-saturated formal params remain passthrough.
            TypeFlow<?> src = v.getSourceFlow();
            if (src instanceof FormalParamTypeFlow && src.isSaturated()) {
                return false;
            }
            return true;
        }
        return t == SugNodeType.FLOW_NODE ||
                        v.isAccumulatorOp();
    }
}
