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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.*;
import pascal.taie.language.type.Type;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new LinkedList<>();
        workList.offer(entry);
        Set<JMethod> reachableMethods = new HashSet<>();
        while (!workList.isEmpty()) {
            JMethod jMethod = workList.poll();
            if (reachableMethods.contains(jMethod)) {
                continue;
            }
            reachableMethods.add(jMethod);
            // 遍历其中的 statement: Resolve target methods via CHA
            for (Stmt stmt: jMethod.getIR()) {
                if (stmt instanceof Invoke cs) {
                    Set<JMethod> T = resolve(cs);
                    for (JMethod tMethod: T) {
                        // Add call edges to call graph
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, tMethod));
                        // May discover new method, add it to work list
                        if (!workList.contains(tMethod)) {
                            workList.offer(tMethod);
                        }
                    }
                }
            }
        }

        for (JMethod jMethod: reachableMethods) {
            callGraph.addReachableMethod(jMethod);
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     *
     * Invoke 表示程序中的方法调用（举个例子：x = o.m(a1,a2,…)）以及调用图中的调用点
     * 你可以使用 CallGraphs.getCallKind(Invoke) 来获得调用点的调用类型。
     * 需要使用 getMethodRef() 来获取目标方法的签名信息。
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();

        // m = method signature at callSite
        MethodRef targetMethodRef = callSite.getMethodRef();
        Subsignature targetMethodSignature = targetMethodRef.getSubsignature();
        JClass targetMethodClass = targetMethodRef.getDeclaringClass();

        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC -> T.add(targetMethodClass.getDeclaredMethod(targetMethodSignature));
            case SPECIAL -> {
                JMethod targetMethod = dispatch(targetMethodClass, targetMethodSignature);
                if (null != targetMethod) {
                    T.add(targetMethod);
                }
            }
            case VIRTUAL, INTERFACE -> {
                // c = declared type of receiver variable at callSite
                Queue<JClass> queue = new LinkedList<>();
                queue.offer(targetMethodClass);
                while (!queue.isEmpty()) {
                    JClass jClass = queue.poll();
                    JMethod jMethod = dispatch(jClass, targetMethodSignature);
                    if (null != jMethod) {
                        T.add(jMethod);
                    }
                    // add subclass
                    if (jClass.isInterface()) {
                        queue.addAll(hierarchy.getDirectImplementorsOf(jClass));
                        queue.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
                    } else {
                        queue.addAll(hierarchy.getDirectSubclassesOf(jClass));
                    }
                }
            }
            case DYNAMIC, OTHER -> {
            }
        }

        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * In this lecture, a signature acts as an identifier of a method
     * Signature = class type + method name + descriptor
     * Descriptor = return type + parameter types
     *
     * Dispatch(𝑐, 𝑚) =
     * 1. return m', if c contains non-abstract method m' that has the same name and descriptor as m
     * 2. Dispatch(c', m), c' is superclass of c
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod jMethod = jclass.getDeclaredMethod(subsignature);
        if (null != jMethod && !jMethod.isAbstract()) {
            return jMethod;
        }
        if (jclass.getSuperClass() != null){
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        return null;
    }
}
