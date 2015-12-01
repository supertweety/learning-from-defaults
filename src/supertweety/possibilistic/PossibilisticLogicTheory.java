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

    private TreeSet<Double> weights = new TreeSet<Double>();

    private MultiMap<Double, Clause> rules = new MultiMap<Double, Clause>();

    private int hashCode = -1;

    private Boolean isGround = null;

    public PossibilisticLogicTheory(){}

    public PossibilisticLogicTheory(MultiMap<Double, Clause> rules) {
        this.set(rules);
    }

    public PossibilisticLogicTheory(List<Pair<Clause, Double>> rules){
        MultiMap<Double,Clause> mm = new MultiMap<Double,Clause>();
        for (Pair<Clause,Double> rule : rules){
            mm.put(rule.s, rule.r);
        }
        this.set(mm);
    }

    public static PossibilisticLogicTheory fromStratification(List<? extends Collection<Clause>> stratification){
        MultiMap<Double,Clause> rules = new MultiMap<Double,Clause>();
        double d = stratification.size()+1;
        for (int i = stratification.size()-1; i >= 0; i--){
            rules.putAll((i+1)/d, stratification.get(i));
        }
        return new PossibilisticLogicTheory(rules);
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

    public void add(Clause rule, double weight){
        this.rules.put(weight, rule);
        this.weights.add(weight);
        if (!LogicUtils.isGround(rule)){
            this.isGround = Boolean.FALSE;
        }
    }

    public void addAll(Collection<Clause> rules, double weight){
        for (Clause rule : rules){
            this.add(rule, weight);
        }
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

    public double minNecessity(){
        return this.weights.first();
    }

    public double maxNecessity(){
        return this.weights.last();
    }

    public boolean implies(Collection<Literal> antecedent, Clause consequent){
        if (isTautology(consequent)){
            return true;
        }
        Pair<Set<Literal>,Double> aSolutionForEvidence = solve(antecedent);
        if (aSolutionForEvidence == null){
            return false;
        }

        Set<Literal> solution = null;
        if (this.isGround()) {
            TheorySolver ts = new TheorySolver();
            solution = ts.solve(this.getAlphaCut(aSolutionForEvidence.s), Sugar.union(antecedent, Utils.flipSigns(consequent).literals()));
        } else {
            GroundTheorySolver gts = new GroundTheorySolver(Sugar.union(this.getAlphaCut(aSolutionForEvidence.s), wrapLiteralsToClauses(antecedent), wrapLiteralsToClauses(Utils.flipSigns(consequent).literals())));
            solution = gts.solve();
        }
        if (solution == null){
            return true;
        }
//        Pair<Set<Literal>,Double> aSolutionForEvidenceAndNegatedConsequence = solve(Sugar.union(antecedent, Utils.flipSigns(consequent).literals()));
//        if (aSolutionForEvidenceAndNegatedConsequence == null){
//            return true;
//        } else if (aSolutionForEvidenceAndNegatedConsequence.s > aSolutionForEvidence.s){
//            return true;
//        }
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
        if (this.isGround()){
            return new GroundTheorySolver(Sugar.union(this.getAlphaCut(alpha), wrapLiteralsToClauses(evidence))).solve();
        } else {
            return new TheorySolver().solve(this.getAlphaCut(alpha), Sugar.setFromCollections(evidence));
        }
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
        return retVal;
    }

    public PossibilisticLogicTheory subtheory(double minNecessity){
        PossibilisticLogicTheory plt = new PossibilisticLogicTheory();
        for (Map.Entry<Double,Set<Clause>> entry : this.rules.entrySet()){
            if (entry.getKey() >= minNecessity){
                for (Clause rule : entry.getValue()){
                    plt.add(rule, entry.getKey());
                }
            }
        }
        return plt;
    }

    /**
     *
     * @return levels of the possibilistic logic theory sorted from smallest necessity to highest necessity.
     */
    public List<Set<Clause>> toLevelList(){
        List<Set<Clause>> retVal = new ArrayList<Set<Clause>>();
        for (double alpha : this.levels()){
            retVal.add(Sugar.setFromCollections(getAlphaLevel(alpha)));
        }
        return retVal;
    }

    public List<Clause> getAlphaLevel(double alpha){
        return Sugar.listFromCollections(this.rules.get(alpha));
    }

    public TreeSet<Double> levels(){
        return this.weights;
    }

    public String toString(){
        StringBuilder sb = new StringBuilder();
        for (double level : Sugar.sortDesc(Sugar.listFromCollections(levels()))){
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
        if (this.hashCode == -1){
            this.hashCode = this.rules.hashCode();
        }
        return this.hashCode;
    }

    @Override
    public boolean equals(Object o){
        if (o instanceof PossibilisticLogicTheory){
            PossibilisticLogicTheory plt = (PossibilisticLogicTheory)o;
            return plt.rules.equals(this.rules);
        }
        return false;
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
