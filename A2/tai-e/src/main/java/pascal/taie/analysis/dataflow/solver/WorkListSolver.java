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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.ir.exp.Var;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    /**
     * 算法的主体部分
     *
     * Worklist ← all basic blocks
     * while (Worklist is not empty)
     *     Pick a basic block B from Worklist
     *     old_OUT = OUT[B]
     *     IN[B] = ⊔P a predecessor of B OUT[P];  // meetInto
     *     OUT[B] = genB U (IN[B] - killB);       // transferNode
     *     if (old_OUT ≠ OUT[B])
     *         Add all successors of B to Worklist
     *
     * 讲义中的 worklist 算法通过比较 old_OUT 和 OUT[B] 来决定后继节点是否应当加入 worklist 中，这个做法比较低效。
     * Tai-e 中 DataflowAnalysis.transferNode() 会返回此次 transfer 是否改变了 OUT fact。
     * 利用好这一点可以避免多余的判断；
     *
     * @param cfg
     * @param result
     */
    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me

        // Worklist ← all basic blocks
        Queue<Node> workList =  new LinkedList<>();
        for (Node node: cfg) {
            workList.offer(node);
        }

        while (!workList.isEmpty()) {
            // Pick a basic block B from Worklist
            Node node = workList.poll();
            // IN[B] = ⊔P a predecessor of B OUT[P];
            for (Node pre: cfg.getPredsOf(node)) {
                analysis.meetInto(result.getOutFact(pre), result.getInFact(node));
            }
            // OUT[B] = genB U (IN[B] - killB);
            boolean outChanged = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if (outChanged) {
                for (Node suc: cfg.getSuccsOf(node)) {
                    workList.offer(suc);
                }
            }
        }

    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
