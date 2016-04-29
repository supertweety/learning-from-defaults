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
import ida.ilp.logic.LogicUtils;
import ida.utils.Cache;
import ida.utils.Sugar;
import ida.utils.VectorUtils;
import ida.utils.collections.MultiMap;
import ida.utils.tuples.Pair;
import supertweety.logic.GroundTheorySolver;
import supertweety.logic.TheorySolver;
import supertweety.misc.Utils;

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 19/01/15.
 */
public class PossibilisticLogicTheory {

    private Set<Clause> hardRules = new HashSet<Clause>();

    private TreeSet<Double> weights = new TreeSet<Double>();

    private MultiMap<Double, Clause> rules = new MultiMap<Double, Clause>();

    //private int hashCode = -1;

    private Boolean isGround = null;

    public static boolean USE_CACHING = false;

    private final static Cache<Set<Clause>,Set<Literal>> cache = new Cache<Set<Clause>,Set<Literal>>();

    private final static Set<Literal> NIL_SOLUTION = new HashSet<Literal>();

    private Set<Literal> additionalElementsOfUniverse = new HashSet<Literal>();

    public PossibilisticLogicTheory copy(){
        PossibilisticLogicTheory retVal = new PossibilisticLogicTheory();
        retVal.hardRules.addAll(this.hardRules);
        retVal.weights.addAll(this.weights);
        retVal.rules.putAll(this.rules);
        retVal.isGround = this.isGround;
        retVal.additionalElementsOfUniverse.addAll(this.additionalElementsOfUniverse);
        return retVal;
    }

    public PossibilisticLogicTheory(){}

    public PossibilisticLogicTheory(MultiMap<Double, Clause> rules) {
        this(rules, null);
    }

    public PossibilisticLogicTheory(List<Pair<Clause, Double>> rules){
        this(rules, null);
    }

    public PossibilisticLogicTheory(MultiMap<Double, Clause> rules, Set<Clause> hardRules) {
        this.set(rules);
        if (hardRules != null) {
            this.hardRules = hardRules;
        }
    }

    public PossibilisticLogicTheory(List<Pair<Clause, Double>> rules, Set<Clause> hardRules){
        MultiMap<Double,Clause> mm = new MultiMap<Double,Clause>();
        for (Pair<Clause,Double> rule : rules){
            mm.put(rule.s, rule.r);
        }
        this.set(mm);
        if (hardRules != null){
            this.hardRules = hardRules;
        }
    }

    public static PossibilisticLogicTheory fromStratification(List<? extends Collection<Clause>> stratification, List<Double> weights){
        return fromStratification(stratification, weights, null);
    }

    public static PossibilisticLogicTheory fromStratification(List<? extends Collection<Clause>> stratification, List<Double> weights, Set<Clause> hardRules){
        MultiMap<Double,Clause> rules = new MultiMap<Double,Clause>();
        for (int i = stratification.size()-1; i >= 0; i--){
            rules.putAll(weights.get(i), stratification.get(i));
        }
        return new PossibilisticLogicTheory(rules, hardRules);
    }

    public static PossibilisticLogicTheory fromStratification(List<? extends Collection<Clause>> stratification){
        return fromStratification(stratification, new HashSet<Clause>());
    }

    public static PossibilisticLogicTheory fromStratification(List<? extends Collection<Clause>> stratification, Set<Clause> hardRules){
        MultiMap<Double,Clause> rules = new MultiMap<Double,Clause>();
        double d = stratification.size()+1;
        for (int i = stratification.size()-1; i >= 0; i--){
            rules.putAll((i+1)/d, stratification.get(i));
        }
        return new PossibilisticLogicTheory(rules, hardRules);
    }

    public static PossibilisticLogicTheory merge(PossibilisticLogicTheory bottom, PossibilisticLogicTheory top){
        List<Set<Clause>> levels = new ArrayList<Set<Clause>>();
        levels.addAll(bottom.toLevelList());
        levels.addAll(top.toLevelList());
        return fromStratification(levels);
    }

    private void set(MultiMap<Double,Clause> rules){
        for (Map.Entry<Double, Set<Clause>> entry : rules.entrySet()) {
            for (Clause c : entry.getValue()) {
                this.rules.put(entry.getKey(), c);
            }
            this.weights.add(entry.getKey());
        }
        this.isGround = null;
    }

    public void addRule(Clause rule, double weight){
        this.rules.put(weight, rule);
        this.weights.add(weight);
        if (!LogicUtils.isGround(rule)){
            this.isGround = Boolean.FALSE;
        }
    }

    public void addHardRule(Clause hardRule){
        this.hardRules.add(hardRule);
    }

    public void remove(Clause rule, double weight){
        this.rules.remove(weight, rule);
        if (this.rules.get(weight).isEmpty()){
            this.weights.remove(weight);
        }
        this.isGround = null;
    }

    public void removeHardRule(Clause hardRule){
        this.hardRules.remove(hardRule);
    }

    public void remove(Clause rule){
        for (double weight : new ArrayList<Double>(this.weights)){
            this.remove(rule, weight);
        }
    }

    public void addAll(Collection<Clause> rules, double weight){
        for (Clause rule : rules){
            this.addRule(rule, weight);
        }
    }

    public void addAllHardRules(Collection<Clause> hardRules){
        this.hardRules.addAll(hardRules);
    }

    public Pair<Set<Literal>,Double> solve(Collection<Literal> evidence){
        double[] levels = VectorUtils.toDoubleArray(this.rules.keySet());
        Arrays.sort(levels);
        int min = 0;
        int max = levels.length-1;
        Set<Literal> solution = null;
        double solutionLevel = Double.NaN;
        while (max >= min){
            int mid = (min+max)/2;
            Set<Literal> currentSolution = null;
            if ((currentSolution = this.solve(levels[mid], evidence)) != null){
                max = mid-1;
                solution = currentSolution;
                solutionLevel = levels[mid];
            } else {
                min = mid+1;
            }
        }
        if (solution == null){
            return null;
        } else {
            return new Pair<Set<Literal>,Double>(solution, solutionLevel);
        }
    }

    private static double cached = 0, noncached = 0;

    private Set<Literal> solveSatProblem(Set<Clause> satProblem){
        Set<Literal> solution;
        if (USE_CACHING) {
            synchronized (cache) {
                solution = cache.get(satProblem);
            }
            if (solution != null) {
                cached++;
                if (solution == NIL_SOLUTION) {
                    return null;
                }
                return solution;
            } else {
                noncached++;
//                if ((int) (cached + noncached) % 10000 == 0) {
//                    System.out.println((cached / (cached + noncached))*100 + " percent of sat queries cached!");
//                    cached = 0;
//                    noncached = 0;
//                }
                if (!this.isGround()) {
                    TheorySolver ts = new TheorySolver();
                    solution = ts.solve(satProblem);
                } else {
                    GroundTheorySolver gts = new GroundTheorySolver(satProblem);
                    solution = gts.solve();
                }
                synchronized (cache) {
                    if (solution == null) {
                        cache.put(satProblem, NIL_SOLUTION);
                    } else {
                        cache.put(satProblem, solution);
                    }
                }
                return solution;
            }
        } else {
            if (!this.isGround()) {
                TheorySolver ts = new TheorySolver();
                solution = ts.solve(satProblem);
            } else {
                GroundTheorySolver gts = new GroundTheorySolver(satProblem);
                solution = gts.solve();
            }
            return solution;
        }
    }

    public double minNecessity(){
        return this.weights.first();
    }

    public double maxNecessity(){
        return this.weights.last();
    }

    public boolean implies(Collection<Literal> evidence, Literal literal){
        return implies(evidence, new Clause(literal));
    }

    public boolean implies(Collection<Literal> antecedent, Clause consequent){
        if (isTautology(consequent)){
            return true;
        }
        Pair<Set<Literal>,Double> aSolutionForEvidence = solve(antecedent);
        if (aSolutionForEvidence == null){
            return false;
        }

        Set<Literal> solution = solveSatProblem(Sugar.union(this.getAlphaCut(aSolutionForEvidence.s), wrapLiteralsToClauses(antecedent), wrapLiteralsToClauses(Utils.flipSigns(consequent).literals())));
//        if (!this.isGround()) {
//            TheorySolver ts = new TheorySolver();
//            solution = ts.solve(this.getAlphaCut(aSolutionForEvidence.s), Sugar.union(antecedent, Utils.flipSigns(consequent).literals()));
//        } else {
//            GroundTheorySolver gts = new GroundTheorySolver(Sugar.union(this.getAlphaCut(aSolutionForEvidence.s), wrapLiteralsToClauses(antecedent), wrapLiteralsToClauses(Utils.flipSigns(consequent).literals())));
//            solution = gts.solve();
//        }
        if (solution == null){
            return true;
        }
        return false;
    }

    public boolean isGround(){
        if (this.isGround == null){
            boolean ig = true;
            outerLoop: for (Map.Entry<Double,Set<Clause>> entry : this.rules.entrySet()){
                for (Clause c : entry.getValue()){
                    if (!LogicUtils.isGround(c)){
                        ig = false;
                        break outerLoop;
                    }
                }
            }
            for (Clause c : hardRules){
                if (!LogicUtils.isGround(c)){
                    ig = false;
                    break;
                }
            }
            this.isGround = ig;
        }
        return this.isGround;
    }

    private static boolean isTautology(Clause clause){
        for (Literal l : clause.literals()){
            if (clause.containsLiteral(l.negation())){
                return true;
            }
        }
        return false;
    }

    public Set<Literal> solve(double alpha, Collection<Literal> evidence){
        return solveSatProblem(Sugar.union(this.hardRules, this.getAlphaCut(alpha), wrapLiteralsToClauses(evidence)));
//        if (this.isGround()){
//            return new GroundTheorySolver(Sugar.union(this.getAlphaCut(alpha), wrapLiteralsToClauses(evidence))).solve();
//        } else {
//            return new TheorySolver().solve(this.getAlphaCut(alpha), Sugar.setFromCollections(evidence));
//        }
    }

    //assuming it is ground
    public Set<Literal> propositionalVariables(){
        Set<Literal> retVal = new HashSet<Literal>();
        for (Map.Entry<Double,Set<Clause>> entry : this.rules.entrySet()){
            for (Clause c : entry.getValue()){
                for (Literal l : c.literals()){
                    if (l.isNegated()){
                        retVal.add(l.negation());
                    } else {
                        retVal.add(l);
                    }
                }
            }
        }
        for (Clause c : hardRules){
            for (Literal l : c.literals()){
                if (l.isNegated()){
                    retVal.add(l.negation());
                } else {
                    retVal.add(l);
                }
            }
        }
        retVal.addAll(additionalElementsOfUniverse);
        return retVal;
    }

    public void addAdditionalPropositionalVariable(Literal literal){
        this.additionalElementsOfUniverse.add(literal);
    }

    private Set<Clause> wrapLiteralsToClauses(Collection<Literal> literals){
        Set<Clause> retVal = new HashSet<Clause>();
        for (Literal l : literals) {
            retVal.add(new Clause(l));
        }
        return retVal;
    }

    public List<Clause> getAlphaCut(double alpha){
        List<Clause> retVal = new ArrayList<Clause>();
        Double higher = new Double(alpha);
        while (higher != null) {
            retVal.addAll(rules.get(higher));
            higher = weights.higher(higher);
        }
        retVal.addAll(hardRules);
        return retVal;
    }

    public List<Clause> getStrictAlphaCut(double alpha){
        List<Clause> retVal = new ArrayList<Clause>();
        Double higher = new Double(alpha);
        higher = weights.higher(higher);
        while (higher != null) {
            retVal.addAll(rules.get(higher));
            higher = weights.higher(higher);
        }
        retVal.addAll(hardRules);
        return retVal;
    }

    public PossibilisticLogicTheory subtheory(double minNecessity){
        PossibilisticLogicTheory plt = new PossibilisticLogicTheory();
        for (Map.Entry<Double,Set<Clause>> entry : this.rules.entrySet()){
            if (entry.getKey() >= minNecessity){
                for (Clause rule : entry.getValue()){
                    plt.addRule(rule, entry.getKey());
                }
            }
        }
        plt.hardRules.addAll(this.hardRules);
        return plt;
    }

    public PossibilisticLogicTheory strictSubtheory(double minNecessity){
        PossibilisticLogicTheory plt = new PossibilisticLogicTheory();
        for (Map.Entry<Double,Set<Clause>> entry : this.rules.entrySet()){
            if (entry.getKey() > minNecessity){
                for (Clause rule : entry.getValue()){
                    plt.addRule(rule, entry.getKey());
                }
            }
        }
        plt.hardRules.addAll(this.hardRules);
        return plt;
    }

    /**
     *
     * @return levels of the possibilistic logic theory sorted from smallest necessity to highest necessity.
     */
    public ArrayList<Set<Clause>> toLevelList(){
        ArrayList<Set<Clause>> retVal = new ArrayList<Set<Clause>>();
        for (double alpha : this.weights()){
            retVal.add(Sugar.setFromCollections(getAlphaLevel(alpha)));
        }
        return retVal;
    }

    public Set<Clause> hardRules(){
        return this.hardRules;
    }

    public List<Clause> getAlphaLevel(double alpha){
        return Sugar.listFromCollections(this.rules.get(alpha));
    }

    public TreeSet<Double> weights(){
        return this.weights;
    }

    public String toString(){
        StringBuilder sb = new StringBuilder();
        if (!this.hardRules.isEmpty()) {
            sb.append("---------------------\n" +
                    "Hard rules:\n");
            for (Clause hardRule : this.hardRules){
                sb.append(hardRule).append("\n");
            }
        }
        for (double level : Sugar.sortDesc(Sugar.listFromCollections(weights()))){
            sb.append("---------------------\nLevel "+level+"\n");
            for (Clause clause : getAlphaLevel(level)) {
                sb.append(clause);
                sb.append("\n");
            }
        }
        return sb.toString();
    }

    @Override
    public int hashCode(){
        return this.rules.hashCode();
    }

    @Override
    public boolean equals(Object o){
        if (o instanceof PossibilisticLogicTheory){
            PossibilisticLogicTheory plt = (PossibilisticLogicTheory)o;
            return plt.rules.equals(this.rules) && plt.hardRules.equals(this.hardRules);
        }
        return false;
    }

    private static boolean falsified(Clause c, Set<Literal> evidence){
        for (Literal l : c.literals()){
            if (!evidence.contains(l.negation())){
                return false;
            }
        }
        return true;
    }

    public void removeRulesDirectlyFalsifiedByEvidence(Set<Literal> evidence){
        for (Clause c : Sugar.flatten(this.toLevelList())){
            if (falsified(c, evidence)) {
                this.remove(c);
            }
        }
    }

    public static void main(String[] args){
        List<List<Clause>> stratification = Sugar.<List<Clause>>list(
                Sugar.<Clause>list(Clause.parse("a(x)")),
                Sugar.<Clause>list(Clause.parse("b(x)")),
                Sugar.<Clause>list(Clause.parse("c(x)"))
        );
        PossibilisticLogicTheory plt = PossibilisticLogicTheory.fromStratification(stratification);
        System.out.println(plt);
        System.out.println(plt.implies(Clause.parse("!b(x)").literals(), Clause.parse("c(x)")));
        System.out.println(plt.implies(Clause.parse("!a(x)").literals(), Clause.parse("b(x)")));
        System.out.println(plt.implies(Clause.parse("!a(x)").literals(), Clause.parse("c(x)")));
        System.out.println(plt.implies(Clause.parse("!c(x)").literals(), Clause.parse("a(x)")));

        System.out.println(merge(plt, PossibilisticLogicTheory.fromStratification(Sugar.list(Sugar.<Clause>list(Clause.parse("x(x)"))))));
    }

}
