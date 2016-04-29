/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.logic.utils;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import ida.utils.collections.ValueToIndex;
import supertweety.logic.ModelCounter;

import java.io.*;
import java.util.*;

/**
 * Created by kuzelkao_cardiff on 17/03/16.
 */
public class RelsatIO {

    public static void write(Collection<Clause> groundClauses, Writer writer) throws IOException {
        PrintWriter pw = new PrintWriter(writer);
        ValueToIndex<Literal> vti = new ValueToIndex<Literal>(1);
        for (Clause c : groundClauses){
            for (Literal l : c.literals()){
                if (l.isNegated()){
                    l = l.negation();
                }
                vti.valueToIndex(l);
            }
        }
        pw.println("p cnf "+vti.size()+" "+groundClauses.size());
        for (Clause c : groundClauses){
            pw.println(clauseToString(c, vti));
        }
        pw.println();
        pw.flush();
    }

    private static String clauseToString(Clause clause, ValueToIndex<Literal> vti){
        StringBuilder sb = new StringBuilder();
        List<Integer> literals = new ArrayList<Integer>();
        for (Literal l : clause.literals()){
            if (l.isNegated()){
                literals.add(-vti.valueToIndex(l.negation()));
            } else {
                literals.add(vti.valueToIndex(l));
            }
        }
        Collections.sort(literals, new Comparator<Integer>() {
            @Override
            public int compare(Integer o1, Integer o2) {
                return Math.abs(o1)-Math.abs(o2);
            }
        });
        int j = 0;
        for (Integer i : literals){
            sb.append(i);
            sb.append("\t");
            j++;
        }
        sb.append("0");
        return sb.toString();
    }

//    public static Collection<Clause> read(Reader reader) throws IOException {
//        return null;
//    }

}
