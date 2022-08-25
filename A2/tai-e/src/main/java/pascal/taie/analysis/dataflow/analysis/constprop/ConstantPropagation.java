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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Maps;

import javax.swing.text.html.Option;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Stream;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    /**
     * 在实现 newBoundaryFact() 的时候，你要小心地处理每个会被分析的方法的参数。 cfg。getIR().getParams()
     * 具体来说，你要将它们的值初始化为 NAC
     * @param cfg
     * @return
     */
    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact ret = new CPFact();

        // 处理每个会被分析的方法的参数
        for (Var var : cfg.getIR().getParams()){
            if (canHoldInt(var)){
                ret.update(var, Value.getNAC());
            }
        }
        return ret;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        CPFact ret = new CPFact();
        return ret;
    }

    /**
     * IN[B] = ⊔P a predecessor of B OUT[P];
     *
     * 本函数就是将 fact 中的内容并入 target 中
     *
     * @param fact
     * @param target
     */
    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var var: fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     * 对应着格上的 meet 操作（⊓），你应当在 meetInto() 方法中调用它。
     *
     * NAC ⊓ v = NAC
     * UNDEF ⊓ v = v
     * c ⊓ v = ?
     * - c ⊓ c = c
     * - c1 ⊓ c2 = NAC
     *
     * 我自己加的规则：
     * NAC ⊓ NAC = NAC
     * NAC ⊓ UNDEF = NAC
     * UNDEF ⊓ UNDEF = UNDEF
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        if (v1.isUndef() && v2.isUndef()) {
            return Value.getUndef();
        } else if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        }

        if (v1.getConstant() == v2.getConstant()) {
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    /**
     * 调用 evaluate() 来进行表达式的求值。
     *
     * OUT[s] = gen ∪ (IN[s] – {(x, _)})
     *
     * (we use val(x) to denote the lattice value that variable x holds)
     * • s: x = c; // c is a constant
     *      gen = {(x, c)}
     * • s: x = y;
     *      gen = {(x, val(y))}
     * • s: x = y op z;
     *      gen = {(x, f(y,z))}
     *
     * (if s is not an assignment statement, F is the identity function)
     *
     * @param stmt
     * @param in
     * @param out
     * @return
     */
    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // OUT[s] = gen ∪ (IN[s] – {(x, _)})
        if (stmt instanceof DefinitionStmt<?,?> definitionStmt) {
            // 判断一个变量是否在本次作业的分析范围内，并忽略那些不在范围内的变量
            if (definitionStmt.getLValue() instanceof Var var && canHoldInt(var)){
                CPFact inCopy = new CPFact();
                inCopy.copyFrom(in);
                // 用 gen 替换掉 原来的 x 的取值
                inCopy.update(var, evaluate(definitionStmt.getRValue(), inCopy));
                return out.copyFrom(inCopy);
            }
        }

        // OUT[s] = IN[s]
        return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * 这个方法会计算表达式（Exp）的值（Value）。
     * 当然，此处的值是格上的抽象值。
     * 需要参考第 6 讲课件的第 247 页上的内容来实现它的三种情况。
     * 对于其它情况，该方法会像我们在第 2.1 节提到的那样返回 NAC。
     * 应该在 transferNode() 方法中调用它来进行表达式的求值。
     *
     * 运算类型	运算符
     * Arithmetic	+ - * /
     * Condition	== != < > <= >=
     * Shift	    << >> >>>
     * Bitwise	    | & ^
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        // 1. x = c
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        // 2. x = y
        else if (exp instanceof Var var) {
            return in.get(var);
        }
        // 3. x = y op z
        else if (exp instanceof BinaryExp binaryExp) {
            Var op1 = binaryExp.getOperand1();
            Var op2 = binaryExp.getOperand2();
            BinaryExp.Op operator = binaryExp.getOperator();

            Value val1 = in.get(op1);
            Value val2 = in.get(op2);

            // (2) if val(y) or val(z) is NAC, f(y,z) = NAC
            if (val1.isNAC() || val2.isNAC()) {
                return Value.getNAC();
            }

            // (1) if val(y) and val(z) are constant, f(y,z) = val(y) op val(z)
            else if (val1.isConstant() && val2.isConstant()) {
                String op = operator.toString();
                int c1 = val1.getConstant();
                int c2 = val2.getConstant();

                // 1. 除 0 异常
                // 2. 溢出异常

                switch (op) {
                    // + - * / %
                    case "+":
                        return Value.makeConstant(c1 + c2);
                    case "-":
                        return Value.makeConstant(c1 - c2);
                    case "*":
                        return Value.makeConstant(c1 * c2);
                    case "/":
                        if (c2 == 0) {
                            return Value.getNAC();
                        }
                        return Value.makeConstant(c1 / c2);
                    case "%":
                        return Value.makeConstant(c1 % c2);
                    // == != < > <= >=
                    case "==":
                        return Value.makeConstant(c1 == c2 ? 1 : 0);
                    case "!=":
                        return Value.makeConstant(c1 != c2 ? 1 : 0);
                    case "<":
                        return Value.makeConstant(c1 < c2 ? 1 : 0);
                    case ">":
                        return Value.makeConstant(c1 > c2 ? 1 : 0);
                    case "<=":
                        return Value.makeConstant(c1 <= c2 ? 1 : 0);
                    case ">=":
                        return Value.makeConstant(c1 >= c2 ? 1 : 0);
                    // << >> >>>
                    case "<<":
                        return Value.makeConstant(c1 << c2);
                    case ">>":
                        return Value.makeConstant(c1 >> c2);
                    case ">>>":
                        return Value.makeConstant(c1 >>> c2);
                    // | & ^
                    case "|":
                        return Value.makeConstant(c1 | c2);
                    case "&":
                        return Value.makeConstant(c1 & c2);
                    case "^":
                        return Value.makeConstant(c1 ^ c2);
                    default:
                        return Value.getUndef();
                }
            }
            // (3) return UNDEF
            else {
                return Value.getUndef();
            }
        }
        // 其它情况
        else {
            return Value.getNAC();
        }
    }
}
