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
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import static pascal.taie.ir.exp.ArithmeticExp.Op.DIV;
import static pascal.taie.ir.exp.ArithmeticExp.Op.REM;

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

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
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
        CPFact ret = new CPFact();
        return ret;
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var: fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
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

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
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
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // 1. x = c
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        // 2. x = y
        if (exp instanceof Var var) {
            return in.get(var);
        }
        // 3. x = y op z
        if (exp instanceof BinaryExp binaryExp) {
            Var op1 = binaryExp.getOperand1();
            Var op2 = binaryExp.getOperand2();
            BinaryExp.Op operator = binaryExp.getOperator();

            Value val1 = in.get(op1);
            Value val2 = in.get(op2);

            // special case:  x = a / 0, x is undef
            if (val2.isConstant() && val2.getConstant() == 0 && (operator == DIV || operator == REM)) {
                return Value.getUndef();
            }

            // (2) if val(y) or val(z) is NAC, f(y,z) = NAC
            if (val1.isNAC() || val2.isNAC()) {
                return Value.getNAC();
            }

            // (1) if val(y) and val(z) are constant, f(y,z) = val(y) op val(z)
            if (val1.isConstant() && val2.isConstant()) {
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
                            return Value.getUndef();
                        }
                        return Value.makeConstant(c1 / c2);
                    case "%":
                        if (c2 == 0) {
                            return Value.getUndef();
                        }
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
                        return Value.getNAC();
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
