/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.logic;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import ida.utils.collections.ValueToIndex;
import ida.utils.tuples.Pair;
import org.sat4j.core.VecInt;
import org.sat4j.maxsat.WeightedMaxSatDecorator;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import java.math.BigInteger;
import java.util.*;

/**
 * Created by kuzelkao_cardiff on 04/02/15.
 */
public class GroundTheorySolver {

    private List<Pair<Clause,BigInteger>> softProgram = new ArrayList<Pair<Clause,BigInteger>>();

    private List<Clause> hardProgram = new ArrayList<Clause>();

    private List<Clause> newHardClauses_forSolver = new ArrayList<Clause>();

    private List<Clause> newHardClauses_forOptimizer = new ArrayList<Clause>();

    private List<int[]> hardDimacsClauses;

    private List<Pair<int[],BigInteger>> softDimacsClauses;

    private ValueToIndex<Literal> literalsToIndices = new ValueToIndex<Literal>(1);

    private int optimizationTimeout = Integer.MAX_VALUE;

    private ISolver solver;

    private WeightedMaxSatDecorator optimizer;

    public GroundTheorySolver(Collection<Clause> hardProgram){
        this(hardProgram, null);
    }

    public GroundTheorySolver(Collection<Clause> hardProgram, Collection<Pair<Clause, BigInteger>> softProgram){
        if (softProgram != null) {
            for (Pair<Clause, BigInteger> c : softProgram) {
                for (Literal literal : c.r.literals()) {
                    literalsToIndices.valueToIndex(literal);
                }
                if (c.s == null) {
                    this.hardProgram.add(c.r);
                } else {
                    this.softProgram.add(new Pair<Clause, BigInteger>(c.r, c.s));
                }
            }
        }
        this.softDimacsClauses = this.toSoftDimacsClauses(this.softProgram);
        for (Clause c : hardProgram){
            for (Literal literal : c.literals()){
                literalsToIndices.valueToIndex(literal);
            }
            this.hardProgram.add(c);
        }
        this.hardDimacsClauses = this.toHardDimacsClauses(this.hardProgram);
    }

    /**
     * The clause may only use ground literals already in the theory added to the constructor.
     * @param clause
     */
    public void addClause(Clause clause) {
        this.newHardClauses_forSolver.add(clause);
        this.newHardClauses_forOptimizer.add(clause);
    }

    public Set<Literal> solve(){
        try {
            if (this.solver == null) {
                this.solver = SolverFactory.newDefault();
                //this.solver = SolverFactory.newMiniLearningHeap();
                this.solver.newVar(this.literalsToIndices.size());
                this.solver.setExpectedNumberOfClauses(softProgram.size());
                for (int[] clause : hardDimacsClauses) {
                    //System.out.println("hard dimacs clause: "+VectorUtils.intArrayToString(clause));
                    try {
                        this.solver.addClause(new VecInt(clause));
                    } catch (ContradictionException ce) {
                        //no solution
                        return null;
                    }
                }
            }
            for (Clause newHardClause : this.newHardClauses_forSolver) {
                this.hardProgram.add(newHardClause);
                this.hardDimacsClauses.add(this.toHardDimacsClause(newHardClause));
            }
//            if (hardDimacsClauses.size() > 100)
//                System.out.println("Dimacs clauses: "+hardDimacsClauses.size());
            try {
                for (Clause newHardClause : this.newHardClauses_forSolver) {
                    this.solver.addClause(new VecInt(this.toHardDimacsClause(newHardClause)));
                }
            } catch (ContradictionException ce){
                this.newHardClauses_forSolver.clear();
                return null;
            }
            this.newHardClauses_forSolver.clear();
            IProblem problem = this.solver;
            if (problem.isSatisfiable()) {
                int[] model = problem.model();
                Set<Literal> solution = new HashSet<Literal>();
                for (int i : model){
                    if (i > 0){
                        solution.add(literalsToIndices.indexToValue(i));
                    }
                }
                return solution;
            } else {
                return null;
            }
        } catch (TimeoutException e){
            e.printStackTrace();
            return null;
        }
    }

    public Set<Literal> optimize(){
        try {
            if (this.optimizer == null) {
                this.optimizer = new WeightedMaxSatDecorator(org.sat4j.pb.SolverFactory.newDefaultOptimizer());
                this.optimizer.newVar(this.literalsToIndices.size());
                this.optimizer.setExpectedNumberOfClauses(softProgram.size() + hardProgram.size());
                //solver.setTopWeight(BigInteger.valueOf(Integer.MAX_VALUE));
                this.optimizer.setTimeoutMs(optimizationTimeout);
                if (this.hardDimacsClauses != null) {
                    for (int[] clause : hardDimacsClauses) {
                        this.optimizer.addHardClause(new VecInt(clause));
                    }
                }

                if (this.softDimacsClauses != null) {
                    for (Pair<int[], BigInteger> clause : this.softDimacsClauses) {
                        this.optimizer.addSoftClause(clause.s, new VecInt(clause.r));
                    }
                }
            }
            for (Clause newHardClauseForOptimizer : this.newHardClauses_forOptimizer){
                this.hardProgram.add(newHardClauseForOptimizer);
                this.hardDimacsClauses.add(this.toHardDimacsClause(newHardClauseForOptimizer));
                this.optimizer.addHardClause(new VecInt(this.toHardDimacsClause(newHardClauseForOptimizer)));
            }
            this.newHardClauses_forOptimizer.clear();
            if (this.optimizer.isSatisfiable()) {
                int[] model = solver.model();
                Set<Literal> solution = new HashSet<Literal>();
                model = this.optimizer.model();

                for (int i : model) {
                    if (i > 0) {
                        solution.add(literalsToIndices.indexToValue(i));
                    }
                }
                return solution;
            }
        } catch (Exception e){
            return null;
        }
        return null;
    }

    private List<Pair<int[],BigInteger>> toSoftDimacsClauses(Collection<Pair<Clause, BigInteger>> program){
        List<Pair<int[],BigInteger>> retVal = new ArrayList<Pair<int[],BigInteger>>();
        for (Pair<Clause,BigInteger> c : program) {
            int[] clause = new int[c.r.literals().size()];
            int i = 0;
            for (Literal l : c.r.literals()){
                if (l.isNegated()){
                    clause[i] = -literalsToIndices.valueToIndex(l.negation());
                } else {
                    clause[i] = literalsToIndices.valueToIndex(l);
                }
                i++;
            }

            retVal.add(new Pair<int[],BigInteger>(clause,c.s));
        }
        return retVal;
    }

    private List<int[]> toHardDimacsClauses(List<Clause> program){
        List<int[]> retVal = new ArrayList<int[]>();
        for (Clause c : program) {
            retVal.add(this.toHardDimacsClause(c));
        }
        return retVal;
    }

    private int[] toHardDimacsClause(Clause c){
        int[] hardDimacsClause = new int[c.literals().size()];
        int i = 0;
        for (Literal l : c.literals()){
            if (l.isNegated()){
                hardDimacsClause[i] = -literalsToIndices.valueToIndex(l.negation());
            } else {
                hardDimacsClause[i] = literalsToIndices.valueToIndex(l);
            }
            i++;
        }
        return hardDimacsClause;
    }

    public static void main(String[] args) {
        Clause c1 = Clause.parse("a(x), b(x), c(x)");
        Clause c2 = Clause.parse("!b(x)");
        GroundTheorySolver gts = new GroundTheorySolver(Sugar.list(c1));
        System.out.println(gts.solve());
        gts.addClause(c2);
        System.out.println(gts.solve());
        gts.addClause(Clause.parse("!c(x)"));
        System.out.println(gts.solve());
        gts.addClause(Clause.parse("!a(x)"));
        System.out.println(gts.solve());
    }

    public void setOptimizationTimeout(int optimizationTimeout) {
        this.optimizationTimeout = optimizationTimeout;
    }
}
