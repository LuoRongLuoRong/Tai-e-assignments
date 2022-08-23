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

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.Optional;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    /**
     * 边界值，给 exit 设定的
     * @param cfg 管理节点的数据流图
     * @return data-flow facts
     */
    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
//        System.out.println("LUORONG: newBoundaryFact, exit 设计为空");
        SetFact<Var> ret = new SetFact<>();
        return ret;
    }

    /**
     * 除 exit 节点外的其它节点的初始化值
     * @return data-flow facts
     */
    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
//        System.out.println("LUORONG: newInitialFact, 普通节点设计为空。");
        SetFact<Var> ret = new SetFact<>();
        return ret;
    }

    /**
     * update out
     * OUT[B] = U s(a successor of B) IN[S]
     * 本函数就是将 fact 中的内容并入 target 中
     * @param fact data-flow facts
     * @param target data-flow facts
     */
    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me
//        System.out.println("LUORONG: meetInto");

        if (target != null) {
            target.union(fact);
//            System.out.print("     fact size: " + target.size());
//            fact.print();
//            System.out.print("     target size: " + target.size());
//            target.print();
        } else {
            System.out.println("LUORONG: meetInto, target is null!!!");
        }
    }

    /**
     * update in
     * @param stmt 对应源代码的一行语句
     * @param in inFacts
     * @param out outFacts
     * @return whether in has changed
     */
    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me
        // IN[B] = useB U (OUT[B] - defB)
        System.out.println("LUORONG: transferNode");
        System.out.println("         lineNumber=" + stmt.getLineNumber());

        // return value
        boolean hasChange = false;
        // 深度拷贝 in，目的是检查 in 是否改变了
        SetFact<Var> inCopy = new SetFact<>();
        inCopy.set(in);

        // 1. IN[B] = useB
        in.clear();
        for (RValue rValue: stmt.getUses()) {
            System.out.println(rValue.toString());
            if (rValue instanceof Var) {
                in.add((Var) rValue);
            }
        }

        // 2. (OUT[B] - defB)

        // 深度拷贝
        SetFact<Var> outCopy = new SetFact<>();
        outCopy.set(out);

        Optional<LValue> o = stmt.getDef();
        if (o.isPresent()) {
            if (o.get() instanceof Var) {
                Var defVar = (Var) o.get();
                if (outCopy.contains(defVar)) {
                    outCopy.remove(defVar);
                }
            }

        }

        in.union(outCopy);

        // 观察 in 是否改变了
        return !(in.equals(inCopy));
    }
}
