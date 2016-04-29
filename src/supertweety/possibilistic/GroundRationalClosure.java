/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.possibilistic;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Constant;
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import supertweety.defaults.DefaultRule;
import supertweety.defaults.PossibilisticZRanker;
import supertweety.logic.GroundTheorySolver;

import java.awt.*;
import java.util.*;
import java.util.List;

/**
 * Created by kuzelkao_cardiff on 29/02/16.
 */
public class GroundRationalClosure {

    public static PossibilisticLogicTheory transform(Collection<DefaultRule> defaults){
        List<Set<Clause>> stratification = new ArrayList<Set<Clause>>();
        List<Set<DefaultRule>> zranking = zranking(defaults);
        if (zranking == null){
            return null;
        }
        for (Set<DefaultRule> level : zranking){
            Set<Clause> s = new HashSet<Clause>();
            for (DefaultRule rule : level){
                s.add(rule.toMaterialImplication());
            }
            stratification.add(s);
        }
        return PossibilisticLogicTheory.fromStratification(stratification);
    }

    public static List<Set<DefaultRule>> zranking(Collection<DefaultRule> defaults){
        Set<DefaultRule> delta = Sugar.<DefaultRule>setFromCollections(defaults);
        List<Set<DefaultRule>> zranking = new ArrayList<Set<DefaultRule>>();
        while (!delta.isEmpty()){
            Set<DefaultRule> tolerated = new HashSet<DefaultRule>();
            Set<Clause> theory = Sugar.<DefaultRule,Clause>funcall(delta, new Sugar.Fun<DefaultRule,Clause>(){
                @Override
                public Clause apply(DefaultRule defaultRule) {
                    return defaultRule.toMaterialImplication();
                }
            });

            for (DefaultRule rule : delta){
                boolean addAntecedent = !theory.contains(rule.antecedent());
                if (addAntecedent){
                    if (rule.antecedent().countLiterals() > 0) {
                        theory.add(rule.antecedent());
                    }
                }
                GroundTheorySolver solver = new GroundTheorySolver(theory);
                if (solver.solve() != null){
                    tolerated.add(rule);
                }
                if (addAntecedent){
                    if (rule.antecedent().countLiterals() > 0) {
                        theory.remove(rule.antecedent());
                    }
                }
            }
            //System.out.println("tolerated: "+tolerated+", theory: "+theoryToString(theory));
            if (tolerated.isEmpty()){
                return null;
            }
            zranking.add(tolerated);
            delta.removeAll(tolerated);
        }
        return zranking;
    }

    private static String theoryToString(Set<Clause> theory){
        StringBuilder sb = new StringBuilder();
        sb.append("[");
        int i = 0;
        for (Clause c : theory){
            sb.append(c.toString(" v "));
            if (i++ < theory.size()-1){
                sb.append(", ");
            }
        }
        sb.append("]");
        return sb.toString();
    }

    public static void main(String[] args){
        List<DefaultRule> defaultRules = Sugar.<DefaultRule>list(
                new DefaultRule("bird(x)","flies(x)"),
                new DefaultRule("penguin(x)","!flies(x)"),
                new DefaultRule("penguin(x)","bird(x)")
        );
        System.out.println(transform(defaultRules));
    }

}
