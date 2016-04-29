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

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 07/03/16.
 */
public class DefaultsExtractor {

    public static Set<DefaultRule> extractSystemPDefaults(PossibilisticLogicTheory plt, int maxAntecedentLength){
        return extractSystemPDefaults(plt, Sugar.<Clause>set(), maxAntecedentLength);
    }

    public static Set<DefaultRule> extractSystemPDefaults(PossibilisticLogicTheory plt, Set<Clause> hardRules, int maxAntecedentLength){
        Set<Literal> universe = new HashSet<Literal>();
        for (Clause rule : Sugar.flatten(plt.toLevelList())){
            for (Literal l : rule.literals()){
                if (l.isNegated()){
                    universe.add(l.negation());
                } else {
                    universe.add(l);
                }
            }
        }
        Set<DefaultRule> defaultRules = new HashSet<DefaultRule>();
        Sets<Literal> bounds = new Sets<Literal>();
        bounds.store(new HashSet<Literal>(), impliedLiterals(new HashSet<Literal>(), plt, universe));
        for (Pair<Set<Literal>,Set<Literal>> p : bounds.bounds()){
            if (p.r.size() != p.s.size()) {
                for (Literal consLit : Sugar.setDifference(p.s, p.r)) {
                    defaultRules.add(new DefaultRule(new Clause(p.r), new Clause(consLit)));
                }
            }
        }
        for (int antecedentLength = 1; antecedentLength <= maxAntecedentLength; antecedentLength++){
            PossibilisticLogicTheory fromShorter = GroundRationalClosure.transform(defaultRules);
            newCandidates(plt, antecedentLength, bounds, universe);
            for (Pair<Set<Literal>,Set<Literal>> p : bounds.bounds(antecedentLength)){
                if (p.r.size() != p.s.size()) {
                    for (Literal consLit : Sugar.setDifference(p.s, p.r)) {
                        PossibilisticLogicTheory fromShorterWithoutFalsifiedEvidence = PossibilisticLogicTheory.fromStratification(fromShorter.toLevelList(), hardRules);
                        fromShorterWithoutFalsifiedEvidence.removeRulesDirectlyFalsifiedByEvidence(p.r);
                        if (!fromShorterWithoutFalsifiedEvidence.implies(p.r, consLit)) {
                            defaultRules.add(new DefaultRule(new Clause(p.r), new Clause(consLit)));
                            //System.out.println(new DefaultRule(new Clause(p.r), new Clause(consLit)));
                        }
                    }
                }
            }
        }

        return defaultRules;
    }

    private static void newCandidates(PossibilisticLogicTheory plt, int antecedentLength, Sets<Literal> bounds, Set<Literal> universe){
        for (Pair<Set<Literal>,Set<Literal>> previous : bounds.bounds(antecedentLength-1)){
            for (Set<Literal> candidateAntecedent : newCandidates(previous.r, previous.s, universe)){
                if (!bounds.inside(candidateAntecedent)){
                    //System.out.println("~~ "+candidateAntecedent + " ~~> " + impliedLiterals(candidateAntecedent, plt, universe));
                    bounds.store(candidateAntecedent, Sugar.union(candidateAntecedent, impliedLiterals(candidateAntecedent, plt, universe)));
                }
            }
        }
    }

    private static Set<Literal> impliedLiterals(Set<Literal> evidence, PossibilisticLogicTheory plt, Set<Literal> universe){
        Set<Literal> retVal = new HashSet<Literal>();
        for (Literal l : universe){
            Literal negL = l.negation();
            if (!evidence.contains(l) && !evidence.contains(negL)){
                if (plt.implies(evidence, l)){
                    retVal.add(l);
                } else if (plt.implies(evidence, negL)){
                    retVal.add(negL);
                }
            }
        }
        return retVal;
    }

    private static Set<Set<Literal>> newCandidates(Set<Literal> lowerBound, Set<Literal> upperBound, Set<Literal> universe){
        Set<Set<Literal>> retVal = new HashSet<Set<Literal>>();
        for (Literal l : universe){
            Literal lNeg = l.negation();
            if (!upperBound.contains(l) && !lowerBound.contains(lNeg)){
                retVal.add(Sugar.union(lowerBound, l));
            }
            if (!upperBound.contains(lNeg) && !lowerBound.contains(l)){
                retVal.add(Sugar.union(lowerBound, lNeg));
            }
        }
        return retVal;
    }


    private static class Sets<T> {

        private MultiMap<Integer,Pair<Set<T>,Set<T>>> pairs = new MultiMap<Integer,Pair<Set<T>,Set<T>>>();

        private MultiMap<T,Pair<Set<T>,Set<T>>> mmL = new MultiMap<T,Pair<Set<T>,Set<T>>>();

        public boolean inside(Set<T> set){
            for (T t : set){
                for (Pair<Set<T>,Set<T>> candidate : mmL.get(t)){
                    if (Sugar.isSubsetOf(candidate.r, set) && Sugar.isSubsetOf(set, candidate.s)){
                        return true;
                    }
                }
            }
            return false;
        }

        public void store(Set<T> lower, Set<T> upper){
            Pair<Set<T>,Set<T>> p = new Pair<Set<T>,Set<T>>(lower, upper);
            pairs.put(p.r.size(), p);
            for (T t : lower){
                mmL.put(t, p);
            }
        }

        public Set<Pair<Set<T>,Set<T>>> bounds(int lowerBoundSize){
            return pairs.get(lowerBoundSize);
        }

        public Set<Pair<Set<T>,Set<T>>> bounds(){
            return Sugar.setFromCollections(Sugar.flatten(this.pairs.values()));
        }

    }

    public static void main(String[] args){
        PossibilisticLogicTheory plt = PossibilisticLogicTheory.fromStratification(
                Sugar.<Set<Clause>>list(
                        Sugar.<Clause>set(Clause.parse("!bird(x),flies(x)")),
                        Sugar.<Clause>set(Clause.parse("!penguin(x),bird(x)")),
                        Sugar.<Clause>set(Clause.parse("!penguin(x),!flies(x)"))
                )
        );
        List<DefaultRule> rules = Sugar.listFromCollections(new DefaultsExtractor().extractSystemPDefaults(plt, 2));
        Collections.sort(rules, new Comparator<DefaultRule>() {
            @Override
            public int compare(DefaultRule o1, DefaultRule o2) {
                if (o1.antecedent().countLiterals()-o2.antecedent().countLiterals() == 0){
                    return o1.toString().compareTo(o2.toString());
                } else {
                    return o1.antecedent().countLiterals() - o2.antecedent().countLiterals();
                }
            }
        });
    }

//    private static class MaxSets<T> {
//
//        private Set<Set<T>> maxsets = new HashSet<Set<T>>();
//
//        private MultiMap<T,Set<T>> mm = new MultiMap<T,Set<T>>();
//
//        private final Set<T> emptySet = new HashSet<T>();
//
//        public boolean containsSuperset(Set<T> set){
//            Set<Set<T>> candidates = null;
//            for (T t : set){
//                if (candidates == null){
//                    candidates = mm.get(t);
//                } else {
//                    candidates = Sugar.intersection(candidates, mm.get(t));
//                }
//            }
//            return candidates != null && !candidates.isEmpty();
//        }
//
//        public Set<Set<T>> getSubsetsOf(Set<T> set){
//            Set<Set<T>> retVal = new HashSet<Set<T>>();
//            if (maxsets.contains(emptySet)){
//                retVal.add(emptySet);
//            }
//            for (T t : set){
//                for (Set<T> s : mm.get(t)){
//                    if (Sugar.isSubsetOf(s, set)){
//                        retVal.add(s);
//                    }
//                }
//            }
//            return retVal;
//        }
//
//        public void removeAll(Collection<Set<T>> sets){
//            maxsets.removeAll(sets);
//            for (Set<T> s : sets){
//                for (T t : s){
//                    mm.remove(t, s);
//                }
//            }
//        }
//
//        public void store(Set<T> upper){
//            if (!containsSuperset(upper)){
//                removeAll(getSubsetsOf(upper));
//            }
//            maxsets.add(upper);
//            for (T t : upper){
//                mm.put(t, upper);
//            }
//        }
//    }
}
