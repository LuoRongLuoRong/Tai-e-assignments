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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.List;

/**
 * Implementation of interprocedural constant propagation for int values.
 *
 * InterConstantPropagation 类包含了一个 ConstantPropagation 类的字段：cp，这使得你可以利用过程内常量传播实现的逻辑。
 *
 * 你在实现 transfer*Edge() 方法的时候，不应该修改第二个参数，也就是该边的源节点的 OUT fact。
 * 我们在第二次作业中介绍过，你可以从 IR 类中获取方法的参数，且可以使用 API JMethod.getIR() 来获取一个方法的 IR。
 *
 * 在过程间常量传播中，transfer edge 需要处理的边被分为以下四种：
 *
     * Normal edge: 这种边一般是与过程间调用无关的边，edge transfer 函数不需要对此进行特殊的处理。这种边上的 fact 经 transfer edge 之后不会有任何改变。换句话说，此时 edge transfer 是一个恒等函数，即 transferEdge(edge, fact) = fact。
     * Call-to-return edge: 对于方法调用 x = m(…)，edge transfer 函数会把等号左侧的变量（在这个例子里也就是 x）和它的值从 fact 中kill 掉。而对于等号左侧没有变量的调用，比如 m(…)，edge transfer 函数的处理方式与对待 normal edge 的一致：不修改 fact，edge transfer 是一个恒等函数。
     * Call edge: 对于这种边，edge transfer 函数会将实参（argument）在调用点中的值传递给被调用函数的形参（parameter）。具体来说，edge transfer 首先从调用点的 OUT fact 中获取实参的值，然后返回一个新的 fact，这个 fact 把形参映射到它对应的实参的值。举个例子，在图 1 里，transferEdge(2→4, {a=6}) = {x=6}。此时，edge transfer 函数的返回值应该仅包含被调用函数的形参的值（比如图 1 里，addOne() 的 x）。
     * Return edge: edge transfer 函数将被调用方法的返回值传递给调用点等号左侧的变量。具体来说，它从被调用方法的 exit 节点的 OUT fact 中获取返回值（可能有多个，你需要思考一下该怎么处理），然后返回一个将调用点等号左侧的变量映射到返回值的 fact。举个例子，在图1中，transferEdge(6→3, {x=6,y=7}) = {b=7}。此时，edge transfer 函数返回的结果应该仅包含调用点等号左侧变量的值（例如图1在第三条语句处的b）。如果该调用点等号左侧没有变量，那么 edge transfer 函数仅会返回一个空 fact。
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        boolean outHasChanged = !out.equals(in);
        // out 改变了，说明有相同的值冲突了。上一个节点的 out 就需要更新为下一个节点的 in
        if (outHasChanged) {
            out.copyFrom(in);
        }

        return outHasChanged;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 视为普通的过程内常量分析
        return cp.transferNode(stmt, in, out);
    }

    /**
     * Normal edge: 这种边一般是与过程间调用无关的边，edge transfer 函数不需要对此进行特殊的处理。
     * 这种边上的 fact 经 transfer edge 之后不会有任何改变。
     * 换句话说，此时 edge transfer 是一个恒等函数，即 transferEdge(edge, fact) = fact。
     * @param edge
     * @param out
     * @return
     */
    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact outCopy = new CPFact();
        outCopy.copyFrom(out);
        return outCopy;
    }

    /**
     * Call-to-return edge:
     * 对于方法调用 x = m(…)，edge transfer 函数会把等号左侧的变量（在这个例子里也就是 x）和它的值从 fact 中kill 掉。
     * 而对于等号左侧没有变量的调用，比如 m(…)，edge transfer 函数的处理方式与对待 normal edge 的一致：不修改 fact，
     * edge transfer 是一个恒等函数。
     * @param edge
     * @param out
     * @return
     */
    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        // For call-to-return edge, kill the value of the LHS variable of the call site.
        // Its value will flow to return site along the return edges.
        // Otherwise, it may cause imprecision.
        CPFact outCopy = new CPFact();
        outCopy.copyFrom(out);

        Invoke source = (Invoke) edge.getSource();
        Var lVar = source.getLValue();
        if (null != lVar) {
            outCopy.update(lVar, Value.getUndef());
        }
        return outCopy;
    }

    /**
     * Call edge:
     * 对于这种边，edge transfer 函数会将实参（argument）在调用点中的值传递给被调用函数的形参（parameter）。
     * 具体来说，edge transfer 首先从调用点的 OUT fact 中获取实参的值，然后返回一个新的 fact，这个 fact 把形参映射到它对应的实参的值。
     * 举个例子，在图 1 里，transferEdge(2→4, {a=6}) = {x=6}。
     * 此时，edge transfer 函数的返回值应该仅包含被调用函数的形参的值（比如图 1 里，addOne() 的 x）。
     * @param edge
     * @param callSiteOut
     * @return
     */
    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me

        CPFact newOut = new CPFact();

        Invoke source = (Invoke) edge.getSource();
        JMethod callee = edge.getCallee();
        List<Var> params = callee.getIR().getParams();

        for (int i = 0; i < params.size(); ++i) {
            Var targetParam = params.get(i);
            Var sourceParam = source.getRValue().getArg(i);
            newOut.update(targetParam, callSiteOut.get(sourceParam));
        }

        return newOut;
    }

    /**
     * Return edge: edge transfer 函数将被调用方法的返回值传递给调用点等号左侧的变量。
     * 具体来说，它从被调用方法的 exit 节点的 OUT fact 中获取返回值（可能有多个，你需要思考一下该怎么处理），
     * 然后返回一个将调用点等号左侧的变量映射到返回值的 fact。
     * 举个例子，在图1中，transferEdge(6→3, {x=6,y=7}) = {b=7}。
     * 此时，edge transfer 函数返回的结果应该仅包含调用点等号左侧变量的值（例如图1在第三条语句处的b）。
     * 如果该调用点等号左侧没有变量，那么 edge transfer 函数仅会返回一个空 fact。
     * @param edge
     * @param returnOut
     * @return
     */
    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact newOut = new CPFact();

        Invoke target = (Invoke) edge.getTarget();
        Var lVar = target.getLValue();
        // lValue 为空
        if (null == lVar) {
            return newOut;
        }
        // lValue 不为空
        for (Var var: edge.getReturnVars()) {
            newOut.update(lVar, cp.meetValue(newOut.get(lVar), returnOut.get(var)));
        }

        return newOut;
    }
}
