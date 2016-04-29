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
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import ida.utils.collections.MultiMap;
import ida.utils.tuples.Pair;
import supertweety.defaults.DefaultRule;
import supertweety.logic.ModelCounter;
import supertweety.logic.TheorySolver;
import supertweety.misc.Utils;

import java.math.BigInteger;
import java.util.*;

/**
 * Created by kuzelkao_cardiff on 09/11/15.
 */
public class PossibilisticUtils {

    public static PossibilisticLogicTheory simplifyByUnitPropagation(PossibilisticLogicTheory plt){
        List<Set<Clause>> levels = plt.toLevelList();
        List<Double> weights = new ArrayList<Double>(plt.weights());
        boolean changed;
        do {
            changed = false;
            for (int i = 0; i < levels.size(); i++){
                Set<Literal> negatedSingletonsFromUpperLevels = new HashSet<Literal>();
                for (int j = i; j < levels.size(); j++){
                    for (Clause c : levels.get(j)){
                        if (c.countLiterals() == 1){
                            negatedSingletonsFromUpperLevels.add(Sugar.chooseOne(c.literals()).negation());
                        }
                    }
                }
                Set<Clause> newLevelI = new HashSet<Clause>();
                for (Clause c : levels.get(i)){
                    if (!Sugar.intersection(c.literals(), negatedSingletonsFromUpperLevels).isEmpty()){
                        newLevelI.add(new Clause(Sugar.setDifference(c.literals(), negatedSingletonsFromUpperLevels)));
                        changed = true;
                    } else {
                        newLevelI.add(c);
                    }
                }
                levels.set(i, newLevelI);
            }
        } while (changed);
        return PossibilisticLogicTheory.fromStratification(levels, weights, plt.hardRules());
    }

    public static PossibilisticLogicTheory simplifyByResolution(PossibilisticLogicTheory plt){
        List<Set<Clause>> levels = plt.toLevelList();
        List<Double> weights = new ArrayList<Double>(plt.weights());
        MultiMap<Literal,Pair<Clause,Integer>> clausesByLiterals = new MultiMap<Literal,Pair<Clause,Integer>>();
        Map<Pair<Clause,Integer>,Pair<Clause,Integer>> unique = new HashMap<Pair<Clause,Integer>,Pair<Clause,Integer>>();
        int levelIndex = 0;
        for (Set<Clause> level : levels){
            for (Clause c : level){
                Pair<Clause,Integer> p = new Pair<Clause,Integer>(c, levelIndex);
                unique.put(p, p);
            }
            levelIndex++;
        }
        levelIndex = 0;
        for (Set<Clause> level : levels){
            for (Clause c : level){
                for (Literal l : c.literals()){
                    clausesByLiterals.put(l, unique.get(new Pair<Clause,Integer>(c, levelIndex)));
                }
            }
            levelIndex++;
        }

        for (int i = levels.size()-1; i >= 0; i--){
            Set<Clause> levelI = Sugar.setFromCollections(levels.get(i));
            for (Clause clauseFromLevelI : levelI){
                for (Literal l : clauseFromLevelI.literals()){
                    Literal negatedL = l.negation();
                    Set<Literal> withoutL = Sugar.setDifference(clauseFromLevelI.literals(), l);
                    for (Pair<Clause,Integer> p : clausesByLiterals.get(negatedL)){
                        if (p.s <= i && Sugar.isSubsetOf(withoutL, p.r.literals())){
                            Clause simplified = new Clause(Sugar.setDifference(p.r.literals(), negatedL));
                            Sugar.replace(levels.get(p.s), p.r, simplified);
                            p.r = simplified;
                        }
                    }
                }
            }
        }
        return PossibilisticLogicTheory.fromStratification(levels, weights, plt.hardRules());
    }


    public static PossibilisticLogicTheory removeDrownedLevels(PossibilisticLogicTheory possibilisticLogicTheory){
        Pair<Set<Literal>,Double> solution = possibilisticLogicTheory.solve(Sugar.<Literal>set());
        if (solution == null){
            return new PossibilisticLogicTheory();
        } else {
            if (possibilisticLogicTheory.minNecessity() == solution.s){
                return possibilisticLogicTheory;
            } else {
                return possibilisticLogicTheory.subtheory(solution.s);
            }
        }
    }

    public static boolean isImplied(Clause clause, Collection<Clause> alphaLevel, Collection<Clause> strictAlphaCut){
        Set<Clause> copyOfAlphaLevel = Sugar.setFromCollections(alphaLevel);
        copyOfAlphaLevel.remove(clause);
        for (Literal clauseLit : Utils.flipSigns(clause).literals()){
            if (!clauseLit.predicate().startsWith("@")) {
                copyOfAlphaLevel.add(new Clause(Sugar.list(clauseLit)));
            }
        }
        TheorySolver gps = new TheorySolver();
        return gps.solve(Sugar.union(copyOfAlphaLevel, strictAlphaCut)) == null;
    }

    public static PossibilisticLogicTheory removeImpliedRules(PossibilisticLogicTheory possibilisticLogicTheory){
        PossibilisticLogicTheory filtered = new PossibilisticLogicTheory();
        filtered.addAllHardRules(possibilisticLogicTheory.hardRules());
        for (double alpha : Sugar.listFromCollections(possibilisticLogicTheory.weights())){
            List<Clause> strictAlphaCut = possibilisticLogicTheory.getStrictAlphaCut(alpha);
            Set<Clause> alphaLevel = Sugar.setFromCollections(possibilisticLogicTheory.getAlphaLevel(alpha));
            Map<Clause,Integer> clauseLengths = new HashMap<Clause,Integer>();
            for (Clause c : alphaLevel){
                clauseLengths.put(c, c.countLiterals());
            }
            for (Clause c : Sugar.sortDesc(Sugar.listFromCollections(alphaLevel), clauseLengths)){
                if (isImplied(c, alphaLevel, strictAlphaCut)){
                    alphaLevel.remove(c);
                } else {
                    filtered.addRule(c, alpha);
                }
            }
        }
        return filtered;
    }

    public static PossibilisticLogicTheory simplifyBySAT(PossibilisticLogicTheory plt){
        int count = Sugar.flatten(plt.toLevelList()).size();
        PossibilisticLogicTheory filtered = new PossibilisticLogicTheory();
        filtered.addAllHardRules(plt.hardRules());
        for (double alpha : Sugar.listFromCollections(plt.weights())){
            List<Clause> strictAlphaCut = plt.getStrictAlphaCut(alpha);
            Set<Clause> alphaLevel = Sugar.setFromCollections(plt.getAlphaLevel(alpha));

            for (Clause c : Sugar.listFromCollections(alphaLevel)){
                boolean changed;
                do {
                    changed = false;
                    if (c.countLiterals() > 1) {
                        for (Literal l : c.literals()) {
                            Clause shorter = new Clause(Sugar.setDifference(c.literals(), l));
                            alphaLevel.add(shorter);
                            boolean implied = isImplied(shorter, alphaLevel, strictAlphaCut);
                            alphaLevel.remove(shorter);
                            if (implied) {
                                Sugar.replace(alphaLevel, c, shorter);
                                c = shorter;
                                changed = true;
                            }
                        }
                    }
                } while (changed);
                //System.out.println("Remaining to process: "+(count-(++i)));
            }
            filtered.addAll(alphaLevel, alpha);
        }
        return filtered;
    }

    private static int sizeInLiterals(PossibilisticLogicTheory plt){
        int retVal = 0;
        for (Set<Clause> level : plt.toLevelList()){
            for (Clause c : level){
                retVal += c.countLiterals();
            }
        }
        return retVal;
    }

    public static PossibilisticLogicTheory collapse(PossibilisticLogicTheory plt, int maxSizeInLiterals){
        return collapse(plt, maxSizeInLiterals, false);
    }

    public static PossibilisticLogicTheory collapseWithRecomputationOfWeights(PossibilisticLogicTheory plt, int maxSizeInLiterals){
        return collapse(plt, maxSizeInLiterals, true);
    }

    private static PossibilisticLogicTheory collapse(PossibilisticLogicTheory plt, int maxSizeInLiterals, boolean recomputeWeights){
        List<Double> weights = new ArrayList<Double>(plt.weights());
        while (sizeInLiterals(plt) > maxSizeInLiterals && plt.weights().size() > 1){
            List<Set<Clause>> levels = plt.toLevelList();
            Set<Clause> merged = Sugar.setFromCollections(levels.get(levels.size()-1), levels.get(levels.size()-2));
            PossibilisticLogicTheory auxPlt = PossibilisticLogicTheory.fromStratification(Sugar.<Set<Clause>>list(merged), plt.hardRules());
            auxPlt = simplifyBySAT(removeImpliedRules(simplifyByResolution(simplifyByUnitPropagation(auxPlt))));

            if (recomputeWeights) {
                List<Double> log2modelCounts = log2ModelCountsOfCuts(PossibilisticLogicTheory.fromStratification(Sugar.<Set<Clause>>list(levels.get(levels.size() - 2), levels.get(levels.size() - 1))));
                double count1 = Math.pow(2, log2modelCounts.get(1)-log2modelCounts.get(0));
                double count2 = Math.pow(2, plt.propositionalVariables().size()-log2modelCounts.get(1));
                double p1 = 1 - weights.get(weights.size() - 2);
                double p2 = 1 - weights.get(weights.size() - 1);
                double p12 = (count1 * p1 + count2 * p2) / (count1 + count2);

                weights.remove(weights.size() - 1);
                weights.remove(weights.size() - 1);
                weights.add(1 - p12);
            }

            levels.remove(levels.size()-1);
            levels.set(levels.size()-1, auxPlt.toLevelList().get(0));
            plt = PossibilisticLogicTheory.fromStratification(levels, weights, plt.hardRules());
        }
        return plt;
    }

    public static PossibilisticLogicTheory collapseKL(PossibilisticLogicTheory plt, int maxSizeInLiterals){

        while (sizeInLiterals(plt) > maxSizeInLiterals && plt.weights().size() > 1){
            List<Set<Clause>> levels = plt.toLevelList();
            List<Double> weights = new ArrayList<Double>(plt.weights());
            List<Double> log2ModelCountsOfCuts = log2ModelCountsOfCuts(plt);
            log2ModelCountsOfCuts.add((double)plt.propositionalVariables().size());

            int downIndexToBeMerged = -1;
            double bestScore = Double.POSITIVE_INFINITY;
            double selectedP12 = Double.NaN;
            for (int i = levels.size()-2; i >= 0; i--){
                double count1 = Math.pow(2, log2ModelCountsOfCuts.get(i+1)-log2ModelCountsOfCuts.get(i));
                double count2 = Math.pow(2, log2ModelCountsOfCuts.get(i+2)-log2ModelCountsOfCuts.get(i+1));
                double p1 = 1 - weights.get(weights.size() - 2);
                double p2 = 1 - weights.get(weights.size() - 1);
                double p12 = (count1 * p1 + count2 * p2) / (count1 + count2);
                double klDiv = ((count1*p1 == 0) ? 0 : count1*p1*Math.log(p1/p12)) + ((count2*p2 == 0) ? 0 : count2*p2*Math.log(p2/p12));
                if (klDiv < bestScore){
                    downIndexToBeMerged = i;
                    bestScore = klDiv;
                    selectedP12 = p12;
                }
            }
            Set<Clause> merged = Sugar.setFromCollections(levels.get(downIndexToBeMerged), levels.get(downIndexToBeMerged+1));
            PossibilisticLogicTheory auxPlt = PossibilisticLogicTheory.fromStratification(Sugar.<Set<Clause>>list(merged), plt.hardRules());
            auxPlt = simplifyBySAT(removeImpliedRules(simplifyByResolution(simplifyByUnitPropagation(auxPlt))));

            weights.remove(downIndexToBeMerged);
            weights.set(downIndexToBeMerged, 1-selectedP12);

            levels.remove(downIndexToBeMerged);
            levels.set(downIndexToBeMerged, auxPlt.toLevelList().get(0));
            plt = PossibilisticLogicTheory.fromStratification(levels, weights, plt.hardRules());
        }
        return plt;
    }

    public static List<Double> log2ModelCountsOfCuts(PossibilisticLogicTheory plt){
        ModelCounter modelCounter = Globals.modelCounterFactory.newInstance();
        List<Double> retVal = new ArrayList<Double>();
        for (double alpha : plt.weights()){
            List<Clause> alphaCut = plt.getAlphaCut(alpha);
            try {
                BigInteger modelCount = modelCounter.modelCount(alphaCut);
                retVal.add(Sugar.logBigInteger(modelCount)/Math.log(2));
            } catch (Exception e){
                throw new RuntimeException("Something went wrong when trying to run the model counter! ",e);
            }
        }
        return retVal;
    }

    private static double logModelCount(Collection<Clause> rules){
        ModelCounter modelCounter = Globals.modelCounterFactory.newInstance();
        try {
            BigInteger modelCount = modelCounter.modelCount(rules);
            return Sugar.logBigInteger(modelCount)/Math.log(2);
        } catch (Exception e){
            throw new RuntimeException("Something went wrong when trying to run the model counter! ",e);
        }
    }

    private static Set<Literal> propositionalVariables(Collection<Clause> rules){
        Set<Literal> retVal = new HashSet<Literal>();
        for (Clause c : rules){
            for (Literal l : c.literals()){
                if (l.isNegated()){
                    retVal.add(l.negation());
                } else {
                    retVal.add(l);
                }
            }
        }
        return retVal;
    }

    public static double probability(PossibilisticLogicTheory plt, Collection<Clause> rules){
        plt = plt.copy();
        plt.addAllHardRules(rules);
        List<Double> weights = new ArrayList<Double>(plt.weights());
        List<Double> logModelCounts = log2ModelCountsOfCuts(plt);
        logModelCounts.add(logModelCount(rules)+Sugar.setDifference(plt.propositionalVariables(), propositionalVariables(rules)).size());
        double retVal = 0;
        for (int i = 0; i < weights.size(); i++){
            retVal += (1-weights.get(i)) * (Math.pow(2, logModelCounts.get(i + 1))-Math.pow(2, logModelCounts.get(i)));
        }
        return retVal;
    }

    /* A simple default has just one literal in the consequent.
     */
    public static List<DefaultRule> simpleDefaultsList(Clause c, PossibilisticLogicTheory plt){
        List<DefaultRule> retVal = new ArrayList<DefaultRule>();
        for (Literal l : c.literals()){
            Collection<Literal> evidence = Utils.flipSigns(Sugar.setDifference(c.literals(), l));
            if (plt.implies(evidence, new Clause(l))){
                retVal.add(new DefaultRule(new Clause(evidence), new Clause(l)));
            }
        }
        return retVal;
    }



    public static void main(String[] args){
        PossibilisticLogicTheory plt = new PossibilisticLogicTheory();
        plt.addRule(Clause.parse("!bird(x),antarctic(x),flies(x)"), 1);
        plt.addRule(Clause.parse("!bird(x),!antarctic(x),!flies(x)"), 1);
        plt.addRule(Clause.parse("!bird(x),!antarctic(x)"), 0.9375);
        plt.addRule(Clause.parse("!flies(x),bird(x)"), 0.875);
        plt.addRule(Clause.parse("!bird(x)"), 0.8125);

        System.out.println(plt);
        System.out.println(probability(plt, Sugar.list(Clause.parse("bird(x)"))));

        plt = collapseKL(plt, 9);
        System.out.println(plt);
        System.out.println(probability(plt, Sugar.list(Clause.parse("bird(x)"))));
    }
}
