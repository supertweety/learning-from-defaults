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
import ida.ilp.logic.Constant;
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import supertweety.defaults.DefaultRule;
import supertweety.logic.GroundTheorySolver;
import supertweety.possibilistic.PossibilisticLogicTheory;

import java.util.*;

/**
 * Created by ondrejkuzelka on 18/10/15.
 */
public class WeightLearner {

    private Collection<Clause> theory;

    private Collection<Clause> hardRules;

    private List<DefaultRule> positiveExamples = new ArrayList<DefaultRule>();

    private List<DefaultRule> negativeExamples = new ArrayList<DefaultRule>();

    private PriorityQueue<SearchNode> open;

    private SearchNode bestSoFar = null;

    private int lowerBound = Integer.MIN_VALUE;

    public WeightLearner(Collection<Clause> theory, Collection<Clause> hardRules, List<DefaultRule> positiveExamples, List<DefaultRule> negativeExamples){
        this.theory = theory;
        this.hardRules = hardRules;
        this.positiveExamples = positiveExamples;
        this.negativeExamples = negativeExamples;
    }

    public void initSearch(){
        this.open = new PriorityQueue<SearchNode>(new Comparator<SearchNode>(){
            @Override
            public int compare(SearchNode o1, SearchNode o2) {
                return o2.heuristic()-o1.heuristic();
            }
        });

        PossibilisticLogicTheory auxPlt = PossibilisticLogicTheory.fromStratification(Sugar.list(theory));
        PossibilisticLogicTheory emptyPossibilisticTheory = PossibilisticLogicTheory.fromStratification(Sugar.list(Sugar.<Clause>set()));
        if (this.hardRules != null) {
            auxPlt.addAll(this.hardRules, 1.0);
        }
        List<DefaultRule> coveredPositiveExamples = LearningUtils.coveredExamples(auxPlt, this.positiveExamples);
        List<DefaultRule> coverablePositiveExamples = LearningUtils.coverableAndNotCoveredExamples(auxPlt, Sugar.listDifference(this.positiveExamples, coveredPositiveExamples));
        List<DefaultRule> coveredNegativeExamples = LearningUtils.coveredExamples(auxPlt, this.negativeExamples);
        List<DefaultRule> coverableNegativeExamples = LearningUtils.coverableAndNotCoveredExamples(auxPlt, Sugar.listDifference(this.negativeExamples, coveredNegativeExamples));
        this.open.add(
                new SearchNode(emptyPossibilisticTheory, Sugar.listFromCollections(this.theory), coveredPositiveExamples, coveredNegativeExamples, coverablePositiveExamples, coverableNegativeExamples,
                    new CandidateConstructor(Sugar.listFromCollections(this.theory), coverablePositiveExamples)));
        this.bestSoFar = this.open.peek();
    }

    public void search(int iterations){
        outerLoop: for (int i = 0; i < iterations && !this.open.isEmpty(); i++){
            SearchNode current = this.open.poll();
            if (current.scoreUpperBound() < Math.max(this.lowerBound, this.bestSoFar.score())){
                continue outerLoop;
            }
            List<Clause> candidateExpansion = current.candidateConstructor.nextCandidate();
            Collection<Clause> remainingTheory = current.remainingTheory;
            if (candidateExpansion != null){
                open.add(current);
                List<Clause> complementOfCandidateExpansion = Sugar.<Clause>listDifference(current.remainingTheory, candidateExpansion);

                if (!candidateExpansion.isEmpty() && !complementOfCandidateExpansion.isEmpty()) {
                    PossibilisticLogicTheory newPLT = PossibilisticLogicTheory.merge(
                            current.stratification,
                            PossibilisticLogicTheory.fromStratification(Sugar.list(complementOfCandidateExpansion)));
                    PossibilisticLogicTheory auxPLT = PossibilisticLogicTheory.merge(newPLT, PossibilisticLogicTheory.fromStratification(Sugar.<List<Clause>>list(candidateExpansion)));
                    if (this.hardRules != null) {
                        auxPLT.addAll(this.hardRules, 1.0);
                    }
                    List<DefaultRule> coveredPositiveExamples = LearningUtils.coveredExamples(auxPLT, current.coverablePositiveExamples);
                    List<DefaultRule> coverablePositiveExamples = LearningUtils.coverableAndNotCoveredExamples(auxPLT, Sugar.listDifference(current.coverablePositiveExamples, coveredPositiveExamples));
                    List<DefaultRule> coveredNegativeExamples = LearningUtils.coveredExamples(auxPLT, current.coverableNegativeExamples);
                    List<DefaultRule> coverableNegativeExamples = LearningUtils.coverableAndNotCoveredExamples(auxPLT, Sugar.listDifference(current.coverableNegativeExamples, coveredNegativeExamples));
                    SearchNode expandedNode = new SearchNode(newPLT, candidateExpansion,
                            Sugar.listFromCollections(current.coveredPositiveExamples, coveredPositiveExamples),
                            Sugar.listFromCollections(current.coveredNegativeExamples, coveredNegativeExamples),
                            coverablePositiveExamples, coverableNegativeExamples,
                            new CandidateConstructor(candidateExpansion, coverablePositiveExamples));
                    //System.out.println("<<START\n"+newPLT+", score = "+expandedNode.score()+", pos = "+expandedNode.coveredPositiveExamples+", neg = "+expandedNode.coverableNegativeExamples+"   END>>\n");
                    if (expandedNode.score() > this.bestSoFar.score() ||
                            (expandedNode.score() == this.bestSoFar.score() && expandedNode.stratification.levels().size() < this.bestSoFar.stratification.levels().size())) {
                        this.bestSoFar = expandedNode;
                    }
                    // simple branch and bound pruning
                    if (Math.max(this.lowerBound, this.bestSoFar.score()) <= expandedNode.scoreUpperBound()) {
                        open.add(expandedNode);
                    }
                }
            }
        }
        //System.out.println(open.size());
    }

    public void setLowerBound(int lowerBound){
        this.lowerBound = lowerBound;
    }

    public PossibilisticLogicTheory bestSoFar(){
        if (this.bestSoFar == null){
            return null;
        }
        PossibilisticLogicTheory retVal = PossibilisticLogicTheory.merge(this.bestSoFar.stratification, PossibilisticLogicTheory.fromStratification(Sugar.list(this.bestSoFar.remainingTheory)));
        if (this.hardRules != null){
            retVal.addAll(this.hardRules, 1.0);
        }
        return retVal;
    }

    private class SearchNode {

        private PossibilisticLogicTheory stratification;

        private List<Clause> remainingTheory;

        private List<DefaultRule> coveredPositiveExamples;

        private List<DefaultRule> coverablePositiveExamples;

        private List<DefaultRule> coveredNegativeExamples;

        private List<DefaultRule> coverableNegativeExamples;

        private CandidateConstructor candidateConstructor;

        private SearchNode(PossibilisticLogicTheory stratification, List<Clause> remainingTheory,
                           List<DefaultRule> coveredPositiveExamples, List<DefaultRule> coveredNegativeExamples,
                           List<DefaultRule> coverablePositiveExamples, List<DefaultRule> coverableNegativeExamples,
                           CandidateConstructor candidateconstructor){
            this.stratification = stratification;
            this.remainingTheory = remainingTheory;
            this.coveredPositiveExamples = coveredPositiveExamples;
            this.coverablePositiveExamples = coverablePositiveExamples;
            this.coveredNegativeExamples = coveredNegativeExamples;
            this.coverableNegativeExamples = coverableNegativeExamples;
            this.candidateConstructor = candidateconstructor;
        }

        private int score(){
            return this.coveredPositiveExamples.size()-this.coveredNegativeExamples.size();
        }

        private int heuristic(){
            return this.score();
        }

        private int scoreUpperBound(){
            return this.coveredPositiveExamples.size()+this.coverablePositiveExamples.size()-coveredNegativeExamples.size();
        }

    }

    private class CandidateConstructor {

        private List<Clause> candidateClauses;

        private Set<Literal> candidateIndicators = new HashSet<Literal>();

        private Date timestamp = new Date();

        private GroundTheorySolver gts;

        private CandidateConstructor(List<Clause> candidateClauses, List<DefaultRule> remainingPositiveExamples){
            this.candidateClauses = candidateClauses;
            List<Clause> satProblemClauses = new ArrayList<Clause>();
            int i = 0;
            for (Clause c : candidateClauses){
                Literal indicator = new Literal("@ind", Constant.construct(String.valueOf(i)));
                candidateIndicators.add(indicator);
                satProblemClauses.add(new Clause(Sugar.union(c.literals(), indicator.negation())));
                i++;
            }

            i = 0;
            Set<Literal> exampleIndicators = new HashSet<Literal>();
            for (DefaultRule rule : remainingPositiveExamples){
                Literal ind = new Literal("@exind", Constant.construct(String.valueOf(i)));
                exampleIndicators.add(ind);
                for (Literal l : rule.antecedent().literals()){
                    satProblemClauses.add(new Clause(Sugar.<Literal>list(l, ind.negation())));
                }
                i++;
            }
            satProblemClauses.add(new Clause(exampleIndicators));
            //satProblemClauses.add(new Clause(candidateIndicators));
            if (hardRules != null) {
                satProblemClauses.addAll(hardRules);
            }
            this.gts = new GroundTheorySolver(satProblemClauses);
        }

        public List<Clause> nextCandidate(){
            Set<Literal> solution = gts.solve();
            if (solution == null){
                return null;
            }
            List<Clause> retVal = new ArrayList<Clause>();
            Set<Literal> newConstraint = new HashSet<Literal>();
            for (Literal l : solution){
                if (this.candidateIndicators.contains(l)){
                    retVal.add(candidateClauses.get(Integer.parseInt(l.get(0).name())));
                    newConstraint.add(l.negation());
                }
            }
            for (Literal ind : candidateIndicators){
                if (!solution.contains(ind)) {
                    newConstraint.add(ind);
                }
            }
            gts.addClause(new Clause(newConstraint));
            return retVal;
        }
    }

    public static void main(String[] args){
        Set<Clause> theory = Sugar.<Clause>set(Clause.parse("!bird(x),flies(x)"), Clause.parse("!penguin(x), !flies(x)"), Clause.parse("!penguin(x),bird(x)"));
        List<DefaultRule> positiveExamples = Sugar.<DefaultRule>list(
                new DefaultRule("bird(x)", "flies(x)"),
                new DefaultRule("penguin(x)", "!flies(x)"),
                new DefaultRule("penguin(x)", "bird(x)")/*,
                new DefaultRule("penguin(x)", "flies(x)"),
                new DefaultRule("penguin(x)", "flies(x)"),
                new DefaultRule("penguin(x)", "flies(x)"),
                new DefaultRule("penguin(x)", "flies(x)")*/);
        List<DefaultRule> negativeExamples = Sugar.<DefaultRule>list(new DefaultRule("bird(x)", "penguin(x)"));
        WeightLearner sl = new WeightLearner(theory, null, positiveExamples, negativeExamples);
        sl.initSearch();
        sl.search(10000);
        System.out.println(sl.bestSoFar());
//        Set<Clause> theory = Sugar.<Clause>set(Clause.parse("a(x)"), Clause.parse("b(x)"), Clause.parse("c(x)"),Clause.parse("!a(x)"), Clause.parse("!b(x)"), Clause.parse("!c(x)"));
//        List<DefaultRule> positiveExamples = Sugar.<DefaultRule>list(new DefaultRule("!a(x)", "b(x)"), new DefaultRule("!c(x)", "b(x)"), new DefaultRule("!a(x)", "c(x)"));
//        List<DefaultRule> negativeExamples = Sugar.<DefaultRule>list(new DefaultRule("!b(x)", "c(x)"));
//        StratificationLearner sl = new StratificationLearner(theory, positiveExamples, negativeExamples);
//        sl.initSearch();
//        sl.search(10000);
//        System.out.println(sl.bestSoFar());
    }
}
