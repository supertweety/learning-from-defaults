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
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * Created by ondrejkuzelka on 17/01/16.
 */
public class IntervalPossibilisticLogicTheory {

    private PossibilisticLogicTheory upper, lower;

    private int hashCode = -1;

    public IntervalPossibilisticLogicTheory(){
        this.lower = new PossibilisticLogicTheory();
        this.upper = new PossibilisticLogicTheory();
    }


    public IntervalPossibilisticLogicTheory(List<Triple<Clause, Double, Double>> rules){
        List<Pair<Clause,Double>> ll = new ArrayList<Pair<Clause,Double>>();
        List<Pair<Clause,Double>> ul = new ArrayList<Pair<Clause,Double>>();
        for (Triple<Clause,Double,Double> t : rules){
            ll.add(new Pair<Clause,Double>(t.r, t.s));
            ul.add(new Pair<Clause,Double>(t.r, t.t));
        }
        this.lower = new PossibilisticLogicTheory(ll);
        this.upper = new PossibilisticLogicTheory(ul);
    }

    public Pair<Set<Literal>,Double> solve(Collection<Literal> evidence){
        Pair<Set<Literal>,Double> upperSolution = this.upper.solve(evidence);
        if (upperSolution == null){
            return null;
        }
        Double lower = this.upper.weights().lower(upperSolution.s);
        double drowningLevel = lower == null ? upperSolution.s : lower;
        PossibilisticLogicTheory auxTheory = this.lower.strictSubtheory(drowningLevel);
        return auxTheory.solve(evidence);
    }

    public boolean implies(Collection<Literal> antecedent, Clause consequent){
        Pair<Set<Literal>,Double> upperSolution = this.upper.solve(antecedent);
        Double lower = this.upper.weights().lower(upperSolution.s);
        double drowningLevel = lower == null ? upperSolution.s : lower;
        PossibilisticLogicTheory auxTheory = this.lower.strictSubtheory(drowningLevel);
        return auxTheory.implies(antecedent, consequent);
    }

    public void addRule(Clause clause, double lowerBound, double upperBound){
        this.lower.addRule(clause, lowerBound);
        this.upper.addRule(clause, upperBound);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        IntervalPossibilisticLogicTheory that = (IntervalPossibilisticLogicTheory) o;

        if (lower != null ? !lower.equals(that.lower) : that.lower != null) return false;
        if (upper != null ? !upper.equals(that.upper) : that.upper != null) return false;

        return true;
    }

    public String toString(){
        return "UPPER:\n"+this.upper.toString()+"\nLOWER: "+this.lower.toString();
    }

    @Override
    public int hashCode() {
        int result = upper != null ? upper.hashCode() : 0;
        result = 31 * result + (lower != null ? lower.hashCode() : 0);
        return result;
    }

    public static void main(String[] args){
        List<Triple<Clause,Double,Double>> list = Sugar.<Triple<Clause,Double,Double>>list(
                new Triple<Clause,Double,Double>(Clause.parse("a(x)"), 0.2, 0.3),
                new Triple<Clause,Double,Double>(Clause.parse("b(x)"), 0.25, 0.35),
                new Triple<Clause,Double,Double>(Clause.parse("c(x)"), 0.31, 0.4)
        );
        IntervalPossibilisticLogicTheory ipl = new IntervalPossibilisticLogicTheory(list);
        System.out.println(ipl.implies(Clause.parse("!a(x)").literals(), Clause.parse("b(x)")));
        System.out.println(ipl.implies(Clause.parse("!a(x)").literals(), Clause.parse("c(x)")));
    }

}
