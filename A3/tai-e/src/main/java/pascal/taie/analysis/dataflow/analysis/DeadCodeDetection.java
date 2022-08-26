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

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // 1. 不可达代码（unreachable code）
        // 1.1 控制流不可达代码（control-flow unreachable code）
        //      检测方式：这样的代码可以很简单地利用所在方法的控制流图（CFG，即 control-flow graph）检测出来。
        //      我们只需要从方法入口开始，遍历 CFG 并标记可达语句。当遍历结束时，那些没有被标记的语句就是控制流不可达的。

        // 1.2 分支不可达代码（unreachable branch）
        //      检测方式：为了检测分支不可达代码，我们需要预先对被检测代码应用常量传播分析，
        //      通过它来告诉我们条件值是否为常量，然后在遍历 CFG 时，我们不进入相应的不可达分支。
        // 1.2.1 if 语句
        //      如果它的条件值（通过常量传播得知）是一个常数，那么无论程序怎么执行，它两个分支中的其中一个分支都不会被走到。这样的分支被称为不可达分支。

        // 1.2.2 switch 语句
        //      对于一个 switch 语句，如果它的条件值是一个常数，那么不符合条件值的 case 分支就可能是不可达的。

        Set<Stmt> reachableCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Stmt entry = cfg.getEntry();
        // 待检测的 stmt
        Queue<Stmt> stmts = new LinkedList<>();
        stmts.offer(entry);
        while (!stmts.isEmpty()) {
            Stmt stmt = stmts.poll();
            // 防止重复添加节点，造成无法退出循环
            if (!reachableCode.contains(stmt)) {
                reachableCode.add(stmt);
                // 检查条件值是不是常量
                Value conditionValue = Value.getNAC();
                if (stmt instanceof If exp) {
                    conditionValue = ConstantPropagation.evaluate(exp.getCondition(), constants.getInFact(stmt));
                }
                else if (stmt instanceof SwitchStmt exp) {
                    conditionValue = ConstantPropagation.evaluate(exp.getVar(), constants.getInFact(stmt));
                }
                // 需要对当前正在访问的节点使用 CFG.getOutEdgesOf() 来帮助获得之后要被访问的后继节点。
                boolean inSwitchCase = false;
                for (Edge edge: cfg.getOutEdgesOf(stmt)) {
                    if (conditionValue.isConstant()) {
                        int val = conditionValue.getConstant();
                        System.out.println("ConditionValue is " + val);
                        if (val == 1 && edge.getKind() == Edge.Kind.IF_TRUE) {
                            // if true
                            stmts.offer((Stmt) edge.getTarget());
                        } else if (val == 0 && edge.getKind() == Edge.Kind.IF_FALSE) {
                            // if false
                            stmts.offer((Stmt) edge.getTarget());
                        } else if (edge.getKind() == Edge.Kind.SWITCH_CASE && edge.getCaseValue() == val) {
                            // switch case
                            inSwitchCase = true;
                            stmts.offer((Stmt) edge.getTarget());
                        } else if (edge.getKind() == Edge.Kind.SWITCH_DEFAULT && !inSwitchCase) {
                            // switch default
                            stmts.offer((Stmt) edge.getTarget());
                        }
                    } else {
                        stmts.offer((Stmt) edge.getTarget());
                    }
                }
            }
        }

        // 2. 无用赋值（dead assignment）
        //      检测方式：为了检测无用赋值，我们需要预先对被检测代码施用活跃变量分析。
        //      对于一个赋值语句，如果它等号左侧的变量（LHS 变量）是一个无用变量（换句话说，not live），那么我们可以把它标记为一个无用赋值。
        //      副作用的代码除外。如果带有副作用，那么为了保证 safety，即使 x 不是一个活跃变量，你也不应该把这个赋值语句标记为死代码。

        for (Stmt stmt: reachableCode) {
            // 检测无用赋值
            if (stmt instanceof DefinitionStmt<?,?> definitionStmt) {
                LValue lValue = definitionStmt.getLValue();
                RValue rValue = definitionStmt.getRValue();
                // 检查左侧变量是否是 not live 变量
                if (lValue instanceof Var lVar && !liveVars.getResult(stmt).contains(lVar) && hasNoSideEffect(rValue)) {
                    deadCode.add(stmt);
                }
            }
        }

        for (Stmt stmt: cfg) {
            if (!reachableCode.contains(stmt)) {
                deadCode.add(stmt);
            }
        }

        // special case: Exit should NOT be included
        deadCode.remove(cfg.getExit());

        return deadCode;
    }

    /**
     *
     *         int x = 10;
     *         int y = 1;
     *         int z;
     *         if (x > y) {
     *             z = 100;
     *         } else {
     *             z = 200; // unreachable branch
     *         }
     *         return z;
     *
     * [0@L4] x = 10; {x=10}
     * [1@L5] y = 1; {x=10, y=1}
     * [2@L7] if (x > y) goto 4; {x=10, y=1}
     * [3@L7] goto 7; {x=10, y=1}
     * [4@L7] nop; {x=10, y=1}
     * [5@L8] z = 100; {x=10, y=1, z=100}
     * [6@L7] goto 9; {x=10, y=1, z=100}
     * [7@L7] nop; {x=10, y=1}
     * [8@L10] z = 200; {x=10, y=1, z=200}
     * [9@L10] nop; {x=10, y=1, z=NAC}
     * [10@L12] return z; {x=10, y=1, z=NAC}
     */

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
