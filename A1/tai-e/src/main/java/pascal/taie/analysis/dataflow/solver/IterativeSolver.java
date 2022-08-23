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

import java.util.ArrayList;
import java.util.List;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        System.out.println("LUORONG: doSolveBackward");
        // 完成对应的 while 循环
        // meetinto: out
        // transfernode: in

        // 此处需要逆序处理
        List<Node> reverseNodes = new ArrayList<>();
        for (Node node : cfg) {
            reverseNodes.add(0, node);
        }

        boolean anyInHasChange = true;
        while (anyInHasChange) {
            anyInHasChange = false;
            for (Node node : reverseNodes) {
//                System.out.println("    node: " + node.toString());
                if (cfg.isExit(node)) {
                    continue;
                }
                // OUT[node]
                result.setOutFact(node, analysis.newInitialFact());
                for (Node suc : cfg.getSuccsOf(node)) {
                    analysis.meetInto(result.getInFact(suc), result.getOutFact(node));
                }

                // IN[node]
                anyInHasChange |= analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            }
        }

    }
}
