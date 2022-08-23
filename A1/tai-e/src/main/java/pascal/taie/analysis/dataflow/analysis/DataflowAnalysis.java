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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.Edge;

/**
 * 这是一个抽象的数据流分析类，是具体的数据流分析与求解器之间的接口。
 * 也就是说，一个具体的数据流分析（如活跃变量分析）需要实现它的接口，
 * 而求解器（如迭代求解器）需要通过它的接口来求解数据流。
 * 它共有七个 API，而在本次作业中，我们只关注与数据流分析相关的五个关键 API（
 * 见第 4 讲课件的第 301 页）：分析方向、边界条件、初始条件、meet 操作、
 * transfer 函数。你可以阅读源代码与注释快速熟悉这些接口方法。
 *
 * 需要注意的是，这里的API与课程中介绍的稍有区别：为了简单起见，
 * 这里的transfer函数处理的是单条语句而非程序块。
 */

/**
 * Template interface for defining data-flow analysis.
 *
 * @param <Node> type of CFG nodes
 * @param <Fact> type of data-flow facts
 */
public interface DataflowAnalysis<Node, Fact> {

    /**
     * @return true if this analysis is forward, otherwise false.
     */
    boolean isForward();

    /**
     * @return new fact in boundary conditions, i.e., the fact for
     * entry (exit) node in forward (backward) analysis.
     */
    Fact newBoundaryFact(CFG<Node> cfg);

    /**
     * @return new initial fact for non-boundary nodes.
     */
    Fact newInitialFact();

    /**
     * Meets a fact into another (target) fact.
     * This function will be used to handle control-flow confluences.
     */
    void meetInto(Fact fact, Fact target);

    /**
     * Node Transfer function for the analysis.
     * The function transfers data-flow from in (out) fact to out (in) fact
     * for forward (backward) analysis.
     *
     * @return true if the transfer changed the out (in) fact, otherwise false.
     */
    boolean transferNode(Node node, Fact in, Fact out);

    /**
     * @return true if this analysis needs to perform transfer for given edge, otherwise false.
     */
    boolean needTransferEdge(Edge<Node> edge);

    /**
     * Edge Transfer function for this analysis.
     */
    Fact transferEdge(Edge<Node> edge, Fact nodeFact);
}
