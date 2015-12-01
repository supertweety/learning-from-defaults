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
import supertweety.logic.TheorySolver;
import supertweety.misc.Utils;

import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * Created by kuzelkao_cardiff on 09/11/15.
 */
public class PossibilisticUtils {


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
        for (double alpha : Sugar.listFromCollections(possibilisticLogicTheory.levels())){
            List<Clause> strictAlphaCut = possibilisticLogicTheory.getStrictAlphaCut(alpha);
            List<Clause> alphaLevel = possibilisticLogicTheory.getAlphaLevel(alpha);
            for (Clause c : Sugar.listFromCollections(alphaLevel)){
                if (isImplied(c, alphaLevel, strictAlphaCut)){
                    alphaLevel.remove(c);
                } else {
                    filtered.add(c, alpha);
                }
            }
        }
        return filtered;
    }
}
