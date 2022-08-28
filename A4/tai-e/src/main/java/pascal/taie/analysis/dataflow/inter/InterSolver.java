/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    /**
     * 你需要在 initialize() 中初始化 ICFG 节点的 IN/OUT fact，
     *      2. 在初始化的过程中，过程间求解器需要初始化程序中所有的 IN/OUT fact，
     *      也就是 ICFG 的全部节点。但你仅需要对 ICFG 的 entry 方法（比如 main 方法）的 entry 节点设置 boundary fact。
     *      这意味着其他方法的 entry 节点和非 entry 节点的初始 fact 是一样的。
     */

    private void initialize() {
        // TODO - finish me
        for (Node node: icfg) {
            System.out.println("*** NODE set in and out fact");
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }

        icfg.entryMethods().forEach(method -> {
            Node entry = icfg.getEntryOf(method);
            result.setInFact(entry, analysis.newBoundaryFact(entry));
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        });
    }

    /**
     * 过程间 worklist 求解器所使用的算法和你在第二次作业中实现的过程内worklist求解器的算法大体上是一样的。它们仅有两处不同：
     *
     *      1. 在第 3.1 节介绍过，在计算一个节点的 IN fact 时，
     *      过程间求解器需要对传入的 edge 和前驱们的 OUT facts 应用 edge transfer 函数（transferEdge）。
     *      2. 在初始化的过程中，过程间求解器需要初始化程序中所有的 IN/OUT fact，
     *      也就是 ICFG 的全部节点。但你仅需要对 ICFG 的 entry 方法（比如 main 方法）的 entry 节点设置 boundary fact。
     *      这意味着其他方法的 entry 节点和非 entry 节点的初始 fact 是一样的。
     */
    private void doSolve() {
        // TODO - finish me

        workList = new LinkedList<>();
        for (Node node: icfg) {
            workList.offer(node);
        }

        // 在过程间数据流分析中，为了计算一个节点的 IN fact，我们需要先对该节点的前驱的 OUT fact 应用 edge transfer，然后把得到结果 meet 进该节点的 IN fact。
        while (!workList.isEmpty()) {
            // Pick a basic block B from Worklist
            Node node = workList.poll();
            // IN[B] = ⊔P a predecessor of B OUT[P];
            for (ICFGEdge<Node> inEdge: icfg.getInEdgesOf(node)) {
                analysis.meetInto(
                        analysis.transferEdge(inEdge, result.getOutFact(inEdge.getSource())),
                        result.getInFact(node));
            }
            // OUT[B] = genB U (IN[B] - killB);
            boolean outChanged = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if (outChanged) {
                for (Node suc: icfg.getSuccsOf(node)) {
                    workList.offer(suc);
                }
            }
        }
    }
}
