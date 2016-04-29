/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.possibilistic.learning;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import ida.utils.collections.MultiList;
import ida.utils.collections.MultiMap;
import supertweety.defaults.DefaultRule;
import supertweety.logic.GroundTheorySolver;
import supertweety.misc.Utils;
import supertweety.possibilistic.PossibilisticLogicTheory;
import supertweety.possibilistic.PossibilisticUtils;

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 03/11/15.
 */
public class LearningUtils {

    static int toughest = 0;

    public static List<DefaultRule> coveredExamples_parallelized(final PossibilisticLogicTheory stratification, List<DefaultRule> examples){
        long m1 = System.currentTimeMillis();
        MultiList<DefaultRule,DefaultRule> ml = new MultiList<DefaultRule,DefaultRule>();
        for (DefaultRule example : examples){
            ml.put(example, example);
        }

        List<List<DefaultRule>> chunks = Sugar.splitList(new ArrayList<DefaultRule>(ml.keySet()), Settings.processors);
        final List<DefaultRule> coveredRules = Collections.synchronizedList(new ArrayList<DefaultRule>());
        List<Runnable> tasks = new ArrayList<Runnable>();
        for (final List<DefaultRule> chunk : chunks){
            tasks.add(new Runnable() {
                @Override
                public void run() {
                    List<DefaultRule> covered = coveredExamples(stratification, chunk);
                    coveredRules.addAll(covered);
                }
            });
        }
        Sugar.runInParallel(tasks, Settings.processors);

        List<DefaultRule> retVal = Collections.synchronizedList(new ArrayList<DefaultRule>());
        for (DefaultRule coveredRule : coveredRules){
            retVal.addAll(ml.get(coveredRule));
        }
        Collections.sort(retVal, new Comparator<DefaultRule>(){
            @Override
            public int compare(DefaultRule o1, DefaultRule o2) {
                return o1.toString().compareTo(o2.toString());
            }
        });
        long m2 = System.currentTimeMillis();
//        if (m2-m1 > toughest){
//            toughest = (int)(m2-m1);
//            System.out.println("This was tough (it took "+toughest+"ms): \n"+stratification);
//        }

        return retVal;
    }

    private static List<DefaultRule> coveredExamples(PossibilisticLogicTheory stratification, List<DefaultRule> examples){
//        unoptimized version
//        List<DefaultRule> retVal = new ArrayList<DefaultRule>();
//        for (DefaultRule rule : examples) {
//            if (stratification.implies(rule.antecedent().literals(), rule.consequent())){
//                retVal.addRule(rule);
//            }
//        }
//        return retVal;

        //this is important
        stratification = PossibilisticUtils.removeDrownedLevels(stratification);



        List<DefaultRule> retVal = new ArrayList<DefaultRule>();

        for (DefaultRule rule : examples){
            PossibilisticLogicTheory relevantSubtheory = relevantSubtheory(stratification, rule);
            Set<Literal> literalsInTheRelevantSubtheory = new HashSet<Literal>();
            for (Clause c : Sugar.flatten(relevantSubtheory.toLevelList())){
                literalsInTheRelevantSubtheory.addAll(c.literals());
            }

            Clause bodyConjunction = rule.antecedent();
            LinkedHashSet<Literal> bodyLiterals = bodyConjunction.literals();
            Clause consequentClause = rule.consequent();
            boolean mayBeImplied = false;
            for (Literal l : consequentClause.literals()){
                // If the theory only contains !l or does not contain l at all then
                // for any model with l = true, there is a model in which l = false
                // and therefore l cannot be implied, analogically if we have a clause in the consequent
                // (and not just one literal) then if the theory contains only !l_i (for each l_i in the consequent clause)
                // or does not contain l at all then for any model we can have a model where all l_i = false - this holds for
                // any non-drowned cut of the theory
                if (literalsInTheRelevantSubtheory.contains(l) || bodyLiterals.contains(l)){
                    mayBeImplied = true;
                    break;
                }
            }

            if (mayBeImplied){
                Set<Clause> clausesInSubtheory;
                if (relevantSubtheory.weights().size() == 1 && (clausesInSubtheory = relevantSubtheory.toLevelList().get(0)).size() == 1){
                    Clause clauseFromSubtheory = Sugar.chooseOne(clausesInSubtheory);
                    if (Sugar.isSubsetOf(clauseFromSubtheory.literals(), rule.toMaterialImplication().literals())){
                        retVal.add(rule);
                    }
                } else {
                    if (Sugar.intersection(Sugar.union(rule.antecedent().literals(), Utils.flipSigns(rule.antecedent()).literals()), literalsInTheRelevantSubtheory).isEmpty()){
                        Collection<Clause> clausesFromTheory = Sugar.flatten(relevantSubtheory.toLevelList());
                        //subsumption checking
                        boolean subsumed = false;
                        for (Clause fromTheory : clausesFromTheory){
                            if (Sugar.isSubsetOf(fromTheory.literals(), rule.consequent().literals())){
                                subsumed = true;
                                break;
                            }
                        }
                        if (subsumed){
                            retVal.add(rule);
                        } else {
                            GroundTheorySolver gts = new GroundTheorySolver(Sugar.union(clausesFromTheory, wrapLiteralsToClauses(rule.antecedent().literals()), wrapLiteralsToClauses(Utils.flipSigns(rule.consequent()).literals())));
                            if (gts.solve() == null){
                                retVal.add(rule);
                            }
                        }
                    } else {
                        //System.out.println(rule+" --relevant-->\n "+relevantSubtheory+"\n<<<");
                        if (relevantSubtheory.implies(bodyConjunction.literals(), consequentClause)) {
                            retVal.add(rule);
                        }
                    }
                }
            }
        }
        return retVal;
    }

    private static Set<Clause> wrapLiteralsToClauses(Collection<Literal> literals){
        Set<Clause> retVal = new HashSet<Clause>();
        for (Literal l : literals) {
            retVal.add(new Clause(l));
        }
        return retVal;
    }

    private static List<DefaultRule> possiblyAffectedExamples(Clause newRule, PossibilisticLogicTheory previous, List<DefaultRule> examples){
        PossibilisticLogicTheory copy = PossibilisticLogicTheory.fromStratification(previous.toLevelList());
        copy.addRule(newRule, copy.maxNecessity());
        if (PossibilisticUtils.removeDrownedLevels(copy).weights().size() < previous.weights().size()){
            return examples;
        }
        List<DefaultRule> retVal = new ArrayList<DefaultRule>();
        for (DefaultRule example : examples){
            Set<Literal> examplesLiterals = Sugar.setFromCollections(example.consequent().literals(), example.antecedent().literals());
            if (Sugar.intersection(newRule.literals(), examplesLiterals).size() > 0){
                retVal.add(example);
            } else {
                Set<Literal> component = component(new Clause(examplesLiterals), previous);
                if (Sugar.intersection(newRule.literals(), component).size() > 0){
                    retVal.add(example);
                }
            }
        }
        return retVal;
    }

    private static PossibilisticLogicTheory relevantSubtheory(PossibilisticLogicTheory plt, DefaultRule example){
        PossibilisticLogicTheory retVal = new PossibilisticLogicTheory();
        Set<Literal> component = component(new Clause(Sugar.iterable(example.antecedent().literals(), example.consequent().literals())), plt);
        for (double level : plt.weights()){
            for (Clause c : plt.getAlphaLevel(level)) {
                Literal l = Sugar.chooseOne(c.literals());
//                System.out.println(plt);
//                System.out.println(component);
//                System.out.println(l+" "+plt.getAlphaLevel(level).size());
                if (component.contains(l) || component.contains(l.negation())) {
                    retVal.addRule(c, level);
                }
            }
        }
        return retVal;
    }

    private static Set<Literal> component(Clause seed, PossibilisticLogicTheory plt){
        MultiMap<Literal,Clause> lookup = new MultiMap<Literal,Clause>();
        for (Clause c : Sugar.flatten(plt.toLevelList())){
            for (Literal l : c.literals()){
                lookup.put(l, c);
                lookup.put(l.negation(), c);
            }
        }
        Set<Literal> retVal = new HashSet<Literal>(seed.literals());
        Stack<Literal> stack = new Stack<Literal>();
        stack.addAll(seed.literals());
        while (!stack.isEmpty()){
            Literal l = stack.pop();
            retVal.add(l);
            for (Clause containedIn : lookup.get(l)){
                for (Literal ci : containedIn.literals()){
                    if (!retVal.contains(ci)){
                        retVal.add(ci);
                        stack.push(ci);
                    }
                }
            }
        }
        return retVal;
    }

    public static List<DefaultRule> coverableAndNotCoveredExamples_parallelized(final PossibilisticLogicTheory stratification, List<DefaultRule> examples){
        List<List<DefaultRule>> chunks = Sugar.splitList(examples, Settings.processors);
        final List<DefaultRule> retVal = Collections.synchronizedList(new ArrayList<DefaultRule>());
        List<Runnable> tasks = new ArrayList<Runnable>();
        for (final List<DefaultRule> chunk : chunks){
            tasks.add(new Runnable() {
                @Override
                public void run() {
                    List<DefaultRule> covered = coverableAndNotCoveredExamples(stratification, chunk);
                    retVal.addAll(covered);
                }
            });
        }
        Sugar.runInParallel(tasks, Settings.processors);
        return retVal;
    }

    public static List<DefaultRule> coverableAndNotCoveredExamples(PossibilisticLogicTheory stratification, List<DefaultRule> examples){
        stratification = PossibilisticUtils.removeDrownedLevels(stratification);
        Set<Literal> literals = new HashSet<Literal>();
        for (Clause c : Sugar.flatten(stratification.toLevelList())){
            literals.addAll(c.literals());
        }
        if (literals.isEmpty()){
            return examples;
        }
        List<DefaultRule> retVal = new ArrayList<DefaultRule>();
        for (DefaultRule rule : examples){
            Clause bodyConjunction = rule.antecedent();
            LinkedHashSet<Literal> bodyLiterals = bodyConjunction.literals();
            Clause headClause = rule.consequent();
            boolean mayBeImplied = false;
            for (Literal l : headClause.literals()){
                if (literals.contains(l) || bodyLiterals.contains(l)){
                    mayBeImplied = true;
                    break;
                }
            }
            PossibilisticLogicTheory relevantSubtheory = relevantSubtheory(stratification, rule);
            if (mayBeImplied && relevantSubtheory.solve(bodyConjunction.literals()) == null){
                retVal.add(rule);
            }
        }
        return retVal;
    }
}
