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
import ida.utils.Combinatorics;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import supertweety.defaults.DefaultRule;
import supertweety.possibilistic.PossibilisticLogicTheory;
import supertweety.possibilistic.PossibilisticUtils;

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 03/11/15.
 */
public class HeuristicPossibilisticLearner {

    private List<Clause> hardRules;

    private List<DefaultRule> defaults, nondefaults;

    private int candidatesSampleSize = 100;

    private static Random random = new Random(2015);

    private List<PossibilisticLogicTheory> incrementalLearnerHistory;

    private boolean useDefaultsAsFeatures = false;

    private long timeout = Long.MAX_VALUE;

    public HeuristicPossibilisticLearner(List<DefaultRule> defaults, List<DefaultRule> nondefaults){
        this.defaults = defaults;
        this.nondefaults = nondefaults;
    }

    public HeuristicPossibilisticLearner(List<DefaultRule> defaults, List<DefaultRule> nondefaults, List<Clause> hardRules){
        this(defaults, nondefaults);
        this.hardRules = hardRules;
    }


    public PossibilisticLogicTheory greedyIncrementalLearner(int iterations){
        this.incrementalLearnerHistory = new ArrayList<PossibilisticLogicTheory>();
        Set<Clause> bestRules = new LinkedHashSet<Clause>();
        PossibilisticLogicTheory bestStratification = new PossibilisticLogicTheory();
        if (this.hardRules != null){
            bestStratification.addAll(this.hardRules, 1.0);
        }

        long startTime = System.currentTimeMillis();

        double bestScore = Double.NEGATIVE_INFINITY;

        outerLoop: for (int i = 0; i < iterations; i++){
            System.out.println("Iteration: "+(i+1)+", time from start: "+(System.currentTimeMillis()-startTime));


            Set<Clause> candidateClauses = makeCandidateSample(
                    Sugar.collectionDifference(this.defaults, LearningUtils.coveredExamples_parallelized(bestStratification, this.defaults)),
                    LearningUtils.coveredExamples_parallelized(bestStratification, this.nondefaults), this.candidatesSampleSize, !useDefaultsAsFeatures);

            Clause bestCandidateClause = selectBest(candidateClauses, bestStratification, this.defaults, this.nondefaults, this.hardRules, startTime, timeout);

            if (System.currentTimeMillis()-startTime >= timeout){
                break outerLoop;
            }

            Pair<PossibilisticLogicTheory,Double> bestCandidateStratification = addRuleGreedily(bestStratification, bestCandidateClause, this.defaults, this.nondefaults, this.hardRules);

            // Greedy minimization of the best sampled candidate feature
            if (!useDefaultsAsFeatures) {
                while (bestCandidateClause.countLiterals() > 1) {
                    candidateClauses = new LinkedHashSet<Clause>();
                    for (Literal l : bestCandidateClause.literals()) {
                        candidateClauses.add(new Clause(Sugar.setDifference(bestCandidateClause.literals(), Sugar.<Literal>set(l))));
                    }
                    Clause newCandidateForBestClause = selectBest(candidateClauses, bestStratification, this.defaults, this.nondefaults, this.hardRules, startTime, timeout);
                    Pair<PossibilisticLogicTheory, Double> newCandidateForBestStratification = addRuleGreedily(bestStratification, newCandidateForBestClause, this.defaults, this.nondefaults, this.hardRules);
                    if (newCandidateForBestStratification.s > bestCandidateStratification.s ||
                            (newCandidateForBestStratification.s == bestCandidateStratification.s && newCandidateForBestStratification.r.toLevelList().size() == bestStratification.toLevelList().size())) {
                        bestCandidateClause = newCandidateForBestClause;
                        bestCandidateStratification = newCandidateForBestStratification;
                        System.out.println("greedy working!");
                    } else {
                        break;
                    }

                    if (System.currentTimeMillis()-startTime >= timeout){
                        break outerLoop;
                    }
                }
            }

            if (bestCandidateStratification.s > bestScore){

                bestScore = bestCandidateStratification.s;
                bestStratification = PossibilisticUtils.removeDrownedLevels(bestCandidateStratification.r);
                bestStratification = PossibilisticUtils.simplifyByUnitPropagation(bestStratification);
                bestStratification = prune(bestStratification, this.defaults, this.nondefaults, hardRules == null ? null : new LinkedHashSet<Clause>(hardRules));

                // Greedily repositioning the already present rules
                for (Clause rule : Sugar.<Clause>flatten(bestStratification.toLevelList())){
                    if (hardRules == null || !hardRules.contains(rule)) {
                        PossibilisticLogicTheory auxTheory = PossibilisticLogicTheory.fromStratification(bestStratification.toLevelList());
                        auxTheory.remove(rule);
                        Pair<PossibilisticLogicTheory, Double> auxPair = addRuleGreedily(auxTheory, rule, this.defaults, this.nondefaults, this.hardRules);
                        if (auxPair.s > bestScore) {
                            bestStratification = auxPair.r;
                            bestScore = auxPair.s;
                        }
                    }
                }
                if (System.currentTimeMillis()-startTime >= timeout){
                    break outerLoop;
                }
            }

            this.incrementalLearnerHistory.add(bestStratification);
            System.out.println("Best score so far: "+bestScore);
            System.out.println(bestStratification+"\n\n");
            if (System.currentTimeMillis()-startTime >= timeout){
                break outerLoop;
            }
        }
        PossibilisticLogicTheory filtered = PossibilisticUtils.removeImpliedRules(bestStratification);

        return filtered;
    }

    private static PossibilisticLogicTheory prune(PossibilisticLogicTheory possibilisticLogicTheory, List<DefaultRule> defaults, List<DefaultRule> nondefaults, Set<Clause> hardRules){
        double bestScore = score(possibilisticLogicTheory, defaults, nondefaults);
        PossibilisticLogicTheory retVal = PossibilisticLogicTheory.fromStratification(possibilisticLogicTheory.toLevelList());
        for (double alpha : possibilisticLogicTheory.weights()){
            for (Clause rule : possibilisticLogicTheory.getAlphaLevel(alpha)){
                if (hardRules == null || !hardRules.contains(rule)) {
                    retVal.remove(rule);
                    double score = score(retVal, defaults, nondefaults);
                    if (score >= bestScore) {
                        System.out.println("Pruning: " + (score - bestScore));
                        bestScore = score;
                    } else {
                        retVal.addRule(rule, alpha);
                    }
                }
            }
        }
        return retVal;
    }

    private static Clause selectBest(Collection<Clause> candidates, PossibilisticLogicTheory possibilisticLogicTheory, List<DefaultRule> defaults, List<DefaultRule> nondefaults, List<Clause> hardRules, long startTime, long timeout){
        double bestScore = Double.NEGATIVE_INFINITY;
        double bestNumberOfLevels = Double.POSITIVE_INFINITY;
        double bestClauseLength = Double.POSITIVE_INFINITY;
        long bestsEvaluationTime = Long.MAX_VALUE;
        Clause bestClause = null;
        for (Clause candidate : candidates){
            if (System.currentTimeMillis()-startTime > timeout){
                return null;
            }
            Pair<PossibilisticLogicTheory, Double> pair = addRuleGreedily(possibilisticLogicTheory, candidate, defaults, nondefaults, hardRules);
            long m1 = System.currentTimeMillis();
            double score = pair.s;
            long m2 = System.currentTimeMillis();
            long evaluationTime = m2-m1;
            double numberOfLevels = pair.r.weights().size();
            double clauseLength = candidate.countLiterals();
            if (score > bestScore ||
                    (score == bestScore && numberOfLevels < bestNumberOfLevels) ||
                    (score == bestScore && numberOfLevels == bestNumberOfLevels && clauseLength < bestClauseLength)
                    || (score == bestScore && numberOfLevels == bestNumberOfLevels && clauseLength == bestClauseLength && evaluationTime < bestsEvaluationTime)) {
                bestScore = score;
                bestNumberOfLevels = numberOfLevels;
                bestClauseLength = clauseLength;
                bestClause = candidate;
                bestsEvaluationTime = evaluationTime;
            }
        }
        return bestClause;
    }

    public List<PossibilisticLogicTheory> incrementalLearnerHistory(){
        return this.incrementalLearnerHistory;
    }

    public static Pair<PossibilisticLogicTheory,Double> addRuleGreedily(PossibilisticLogicTheory theory, Clause newRule, List<DefaultRule> defaults, List<DefaultRule> nonDefaults, List<Clause> hardRules){
        PossibilisticLogicTheory best = null;
        double bestScore = Double.NEGATIVE_INFINITY;
        List<Set<Clause>> levels = theory.toLevelList();

        Set<Clause> hardRulesInTheory = null;
        if (hardRules != null && hardRules.size() > 0){
            hardRulesInTheory = levels.remove(levels.size()-1);
        }
        int subsumedFromLevelXBelow = -1;
        outerLoop: for (int i = levels.size()-1; i > 0; i--){
            for (Clause c : levels.get(i)){
                if (Sugar.isSubsetOf(c.literals(), newRule.literals())){
                    subsumedFromLevelXBelow = i;
                    break outerLoop;
                }
            }
        }


        for (int i = subsumedFromLevelXBelow+1; i < levels.size(); i++){
            levels.get(i).add(newRule);
            if (hardRulesInTheory != null){
                levels.add(hardRulesInTheory);
            }
            PossibilisticLogicTheory plt = PossibilisticLogicTheory.fromStratification(levels);
            double score = score(plt, defaults, nonDefaults);
            if (score > bestScore){
                bestScore = score;
                best = plt;
            }
            levels.get(i).remove(newRule);
            if (hardRulesInTheory != null){
                levels.remove(levels.size()-1);
            }
        }
        //growing from bottom
        List<Set<Clause>> growingFromBottom = new ArrayList<Set<Clause>>();
        growingFromBottom.add(Sugar.<Clause>set(newRule));
        growingFromBottom.addAll(levels);
        if (subsumedFromLevelXBelow == -1){
            if (hardRulesInTheory != null){
                growingFromBottom.add(hardRulesInTheory);
            }
            PossibilisticLogicTheory pltGrowingFromBottom = PossibilisticLogicTheory.fromStratification(growingFromBottom);
            double score = score(pltGrowingFromBottom, defaults, nonDefaults);
            if (score > bestScore) {
                bestScore = score;
                best = pltGrowingFromBottom;
            }
        }
        //growing from top
        List<Set<Clause>> growingFromTop = new ArrayList<Set<Clause>>();
        growingFromTop.addAll(levels);
        growingFromTop.add(Sugar.<Clause>set(newRule));
        if (hardRulesInTheory != null){
            growingFromTop.add(hardRulesInTheory);
        }
        PossibilisticLogicTheory pltGrowingFromTop = PossibilisticLogicTheory.fromStratification(growingFromTop);
        double score = score(pltGrowingFromTop, defaults, nonDefaults);
        if (score > bestScore){
            best = pltGrowingFromTop;
            bestScore = score;
        }
        //inserting new level
        for (int i = subsumedFromLevelXBelow+1; i < levels.size(); i++){
            List<Set<Clause>> auxLevels = new ArrayList<Set<Clause>>();
            auxLevels.addAll(levels.subList(0, i));
            auxLevels.add(Sugar.<Clause>set(newRule));
            auxLevels.addAll(levels.subList(i, levels.size()));
            if (hardRulesInTheory != null) {
                auxLevels.add(hardRulesInTheory);
            }
            PossibilisticLogicTheory plt = PossibilisticLogicTheory.fromStratification(auxLevels);
            score = score(plt, defaults, nonDefaults);
            if (score > bestScore){
                bestScore = score;
                best = plt;
            }
        }
        return new Pair<PossibilisticLogicTheory,Double>(best, bestScore);
    }

    public static double score(PossibilisticLogicTheory plt, List<DefaultRule> defaults, List<DefaultRule> nondefaults){
        return LearningUtils.coveredExamples_parallelized(plt, defaults).size()-LearningUtils.coveredExamples_parallelized(plt, nondefaults).size();
    }

    protected static Set<Clause> makeCandidateSample(Collection<DefaultRule> defaults, Collection<DefaultRule> nondefaults, int sampleSize, boolean sampleSubRules){
        List<DefaultRule> pool = new ArrayList<DefaultRule>(new LinkedHashSet<DefaultRule>(defaults));
        for (DefaultRule nondefault : new LinkedHashSet<DefaultRule>(nondefaults)){
            Literal l = Sugar.chooseRandomOne(new ArrayList<Literal>(nondefault.consequent().literals()), random);
            pool.add(new DefaultRule(nondefault.antecedent(), new Clause(l.negation())));
        }
        Set<DefaultRule> candidateDefaultRules = Combinatorics.randomCombination(new ArrayList(pool), Math.min(sampleSize, defaults.size()), random).toSet();
        if (sampleSubRules) {
            return Sugar.<DefaultRule, Clause>funcall(candidateDefaultRules,
                    new Sugar.Fun<DefaultRule, Clause>() {
                        @Override
                        public Clause apply(DefaultRule defaultRule) {
                            if (defaultRule.antecedent().countLiterals()+defaultRule.consequent().countLiterals() <= 1){
                                return defaultRule.toMaterialImplication();
                            } else {
                                int length = random.nextInt(defaultRule.antecedent().countLiterals()+1);
                                List<Literal> literals = Combinatorics.randomCombination(Sugar.listFromCollections(defaultRule.toMaterialImplication().literals()), length, random).toList();
                                literals.addAll(defaultRule.consequent().literals());
                                return new Clause(literals);
                            }
                        }
                    });
        } else {
            return Sugar.funcall(candidateDefaultRules, new Sugar.Fun<DefaultRule,Clause>(){
                @Override
                public Clause apply(DefaultRule defaultRule) {
                    return defaultRule.toMaterialImplication();
                }
            });
        }
//        List<DefaultRule> pool = new ArrayList<DefaultRule>(new LinkedHashSet<DefaultRule>(defaults));
//        for (DefaultRule nondefault : new LinkedHashSet<DefaultRule>(nondefaults)){
//            Literal l = Sugar.chooseRandomOne(new ArrayList<Literal>(nondefault.consequent().literals()), random);
//            pool.addRule(new DefaultRule(nondefault.antecedent(), new Clause(l.negation())));
//        }
//        Set<DefaultRule> candidateDefaultRules = Combinatorics.randomCombination(new ArrayList(pool), Math.min(sampleSize, defaults.size()), random).toSet();
//        if (sampleSubRules) {
//            return Sugar.<DefaultRule, Clause>funcall(candidateDefaultRules,
//                    new Sugar.Fun<DefaultRule, Clause>() {
//                        @Override
//                        public Clause apply(DefaultRule defaultRule) {
//                            List<Literal> literals = Combinatorics.randomCombination(Sugar.listFromCollections(defaultRule.toMaterialImplication().literals()), random).toList();
//                            literals.addAll(defaultRule.consequent().literals());
//                            return new Clause(literals);
//                        }
//                    });
//        } else {
//            return Sugar.funcall(candidateDefaultRules, new Sugar.Fun<DefaultRule,Clause>(){
//                @Override
//                public Clause apply(DefaultRule defaultRule) {
//                    return defaultRule.toMaterialImplication();
//                }
//            });
//        }
    }

    public void setCandidatesSampleSize(int candidatesSampleSize) {
        this.candidatesSampleSize = candidatesSampleSize;
    }

    public void setUseDefaultsAsFeatures(boolean useDefaultsAsFeatures){
        this.useDefaultsAsFeatures = useDefaultsAsFeatures;
    }

    public void setTimeout(long timeout){
        this.timeout = timeout;
    }
}
