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
import ida.utils.Combinatorics;
import ida.utils.Sugar;
import supertweety.defaults.DefaultRule;
import supertweety.possibilistic.PossibilisticLogicTheory;
import supertweety.possibilistic.PossibilisticUtils;

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 03/11/15.
 */
public class PossibilisticLearner {

    private List<Clause> hardRules;

    private List<DefaultRule> defaults, nondefaults;

    private List<Clause> rules;

    private boolean sampleSubRules = false;

    private int candidatesSampleSize = 100;

    private int weightLearnerIterations = Integer.MAX_VALUE;

    private static Random random = new Random(2015);

    private List<PossibilisticLogicTheory> incrementalLearnerHistory;

    public PossibilisticLearner(List<DefaultRule> defaults, List<DefaultRule> nondefaults){
        this.defaults = defaults;
        this.nondefaults = nondefaults;
    }

    public PossibilisticLearner(List<DefaultRule> defaults, List<DefaultRule> nondefaults, List<Clause> hardRules){
        this(defaults, nondefaults);
        this.hardRules = hardRules;
    }

    public void setRules(List<Clause> rules){
        this.rules = rules;
    }

    public PossibilisticLogicTheory weightLearning(){
        WeightLearner weightLearner = new WeightLearner(this.rules, this.hardRules, this.defaults, this.nondefaults);
        weightLearner.initSearch();
        weightLearner.search(weightLearnerIterations);
        //return PossibilisticUtils.removeImpliedRules(PossibilisticUtils.removeDrownedLevels(weightLearner.bestSoFar()));
        return weightLearner.bestSoFar();
    }

    public PossibilisticLogicTheory greedySayuLearn(int iterations){
        Set<Clause> bestRules = new HashSet<Clause>();
        PossibilisticLogicTheory bestStratification = null;
        int bestScore = Integer.MIN_VALUE;
        for (int i = 0; i < iterations; i++){
            System.out.println("Iteration: "+i);
            Set<Clause> candidateClauses = makeCandidateSample(this.candidatesSampleSize);
            int bestCandidateScore = Integer.MIN_VALUE;
            Clause bestCandidateClause = null;
            PossibilisticLogicTheory bestCandidateStratification = null;
            for (Clause candidateClause : candidateClauses) {
                List<Clause> candidateTheory = new ArrayList<Clause>(bestRules);
                candidateTheory.add(candidateClause);
                WeightLearner weightLearner = new WeightLearner(candidateTheory, this.hardRules, this.defaults, this.nondefaults);
                weightLearner.initSearch();
                weightLearner.setLowerBound(Math.max(bestScore, bestCandidateScore));
                weightLearner.search(weightLearnerIterations);
                PossibilisticLogicTheory plt = weightLearner.bestSoFar();
                if (plt != null) {
                    int score = score(plt);
                    if (score > bestCandidateScore) {
                        bestCandidateClause = candidateClause;
                        bestCandidateStratification = plt;
                        bestCandidateScore = score;
                    }
                }
            }
            if (bestCandidateClause != null) {
                bestRules.add(bestCandidateClause);
            }
            if (bestCandidateScore > bestScore){
                bestScore = bestCandidateScore;
                bestStratification = bestCandidateStratification;
                //bestStratification.
            }
            System.out.println("Best score so far: "+bestScore);
            System.out.println(bestStratification+"\n\n");
        }
        return bestStratification;
    }

    public PossibilisticLogicTheory greedyIncrementalLearner(int iterations){
        this.incrementalLearnerHistory = new ArrayList<PossibilisticLogicTheory>();
        Set<Clause> bestRules = new HashSet<Clause>();
        PossibilisticLogicTheory bestStratification = new PossibilisticLogicTheory();
        if (this.hardRules != null){
            bestStratification.addAll(this.hardRules, 1.0);
        }
        int bestScore = Integer.MIN_VALUE;
        for (int i = 0; i < iterations; i++){
            System.out.println("Iteration: "+(i+1));
            Set<Clause> candidateClauses = makeCandidateSample(this.candidatesSampleSize);
            int bestCandidateScore = Integer.MIN_VALUE;
            Clause bestCandidateClause = null;
            PossibilisticLogicTheory bestCandidateStratification = null;
            for (Clause candidateClause : Sugar.setDifference(candidateClauses, bestRules)){
                PossibilisticLogicTheory plt = PossibilisticUtils.removeDrownedLevels(addRuleGreedily(bestStratification, candidateClause));
                int score = score(plt);
                if (score > bestCandidateScore){
                    bestCandidateClause = candidateClause;
                    bestCandidateStratification = plt;
                    bestCandidateScore = score;
                }
            }
            if (bestCandidateClause != null) {
                bestRules.add(bestCandidateClause);
            }
            if (bestCandidateScore > bestScore){
                bestScore = bestCandidateScore;
                bestStratification = PossibilisticUtils.removeImpliedRules(bestCandidateStratification);
            }
            this.incrementalLearnerHistory.add(bestStratification);
            System.out.println("Best score so far: "+bestScore);
            System.out.println(bestStratification+"\n\n");
        }
        return bestStratification;
    }

    public List<PossibilisticLogicTheory> incrementalLearnerHistory(){
        return this.incrementalLearnerHistory;
    }

    private void addHardRules(PossibilisticLogicTheory plt){
        if (this.hardRules != null) {
            for (Clause hardRule : this.hardRules){
                plt.add(hardRule, 1.0);
            }
        }
    }

    public PossibilisticLogicTheory addRuleGreedily(PossibilisticLogicTheory theory, Clause newRule){
        PossibilisticLogicTheory best = null;
        int bestScore = Integer.MIN_VALUE;
        List<Set<Clause>> levels = theory.toLevelList();
        Set<Clause> hardRulesInTheory = null;
        if (containsHardRules(theory)){
            hardRulesInTheory = levels.remove(levels.size()-1);
        }
        for (int i = 0; i < levels.size(); i++){
            levels.get(i).add(newRule);
            PossibilisticLogicTheory plt = PossibilisticLogicTheory.fromStratification(levels);
            if (hardRulesInTheory != null){
                plt.addAll(hardRulesInTheory, 1.0);
            }
            plt = PossibilisticUtils.removeImpliedRules(plt);
            int score = score(plt);
            if (score > bestScore || (score == bestScore && numRules(plt) < numRules(best))){
                bestScore = score;
                best = plt;
            }
            levels.get(i).remove(newRule);
        }
        List<Set<Clause>> growingFromBottom = new ArrayList<Set<Clause>>();
        growingFromBottom.add(Sugar.<Clause>set(newRule));
        growingFromBottom.addAll(levels);
        PossibilisticLogicTheory plt = PossibilisticLogicTheory.fromStratification(growingFromBottom);
        if (hardRulesInTheory != null){
            plt.addAll(hardRulesInTheory, 1.0);
        }
        plt = PossibilisticUtils.removeImpliedRules(plt);
        int score = score(plt);
        if (score > bestScore || (score == bestScore && numRules(plt) < numRules(best))){
            bestScore = score;
            best = plt;
        }
        List<Set<Clause>> growingFromTop = new ArrayList<Set<Clause>>();
        growingFromTop.addAll(levels);
        growingFromTop.add(Sugar.<Clause>set(newRule));
        plt = PossibilisticLogicTheory.fromStratification(growingFromTop);
        if (hardRulesInTheory != null){
            plt.addAll(hardRulesInTheory, 1.0);
        }
        plt = PossibilisticUtils.removeImpliedRules(plt);
        score = score(plt);
        if (score > bestScore || (score == bestScore && numRules(plt) < numRules(best))){
            best = plt;
        }
        return best;
    }

    private static boolean containsHardRules(PossibilisticLogicTheory plt){
        return plt.getAlphaLevel(1.0).size() > 0;
    }

    private static int numRules(PossibilisticLogicTheory plt){
        int retVal = 0;
        for (Set<Clause> set : plt.toLevelList()){
            retVal += set.size();
        }
        return retVal;
    }



    public int score(PossibilisticLogicTheory plt){
        return LearningUtils.coveredExamples_parallelized(plt, defaults).size()-LearningUtils.coveredExamples_parallelized(plt, nondefaults).size();
    }

    protected Set<Clause> makeCandidateSample(int sampleSize){
        if (this.rules != null){
            if (sampleSubRules){
                return Sugar.<Clause, Clause>funcall(Combinatorics.randomCombination(this.rules, Math.min(sampleSize, this.rules.size()), random).toSet(),
                        new Sugar.Fun<Clause, Clause>() {
                            @Override
                            public Clause apply(Clause rule) {
                                return new Clause(Combinatorics.randomCombination(Sugar.listFromCollections(rule.literals()), random).toList());
                            }
                        });
            } else {
                return Combinatorics.randomCombination(this.rules, Math.min(this.rules.size(), sampleSize), random).toSet();
            }
        } else {
            if (sampleSubRules) {
                return Sugar.<DefaultRule, Clause>funcall(Combinatorics.randomCombination(this.defaults, Math.min(sampleSize, this.defaults.size()), random).toSet(),
                        new Sugar.Fun<DefaultRule, Clause>() {
                            @Override
                            public Clause apply(DefaultRule defaultRule) {
                                return new Clause(Combinatorics.randomCombination(Sugar.listFromCollections(defaultRule.toMaterialImplication().literals()), random).toList());
                            }
                        });
            } else {
                return Sugar.<DefaultRule, Clause>funcall(Combinatorics.randomCombination(this.defaults, Math.min(sampleSize, this.defaults.size()), random).toSet(),
                        new Sugar.Fun<DefaultRule, Clause>() {
                            @Override
                            public Clause apply(DefaultRule defaultRule) {
                                return new Clause(Sugar.listFromCollections(defaultRule.toMaterialImplication().literals()));
                            }
                        });
            }
        }
    }

    public void setCandidateSampleSize(int candidateSampleSize){
        this.candidatesSampleSize = candidateSampleSize;
    }

    public void setSampleSubRules(boolean sampleSubRules) {
        this.sampleSubRules = sampleSubRules;
    }

    public void setCandidatesSampleSize(int candidatesSampleSize) {
        this.candidatesSampleSize = candidatesSampleSize;
    }

    public void setWeightLearnerIterations(int weightLearnerIterations) {
        this.weightLearnerIterations = weightLearnerIterations;
    }
}
