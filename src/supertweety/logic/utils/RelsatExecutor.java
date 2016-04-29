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
import ida.utils.Sugar;
import ida.utils.UniqueIDs;
import supertweety.logic.ModelCounter;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.math.BigInteger;
import java.util.Collection;
import java.util.Random;

/**
 * Created by kuzelkao_cardiff on 17/03/16.
 */
public class RelsatExecutor implements ModelCounter {

    private String path;

    private long id;

    private final static Random random = new Random(System.nanoTime());

    public RelsatExecutor(String path){
        this.path = path;
        this.id = random.nextLong();
    }

    public BigInteger modelCount(Collection<Clause> satProblem) throws Exception {
        BigInteger retVal = null;
        String filepath = path+"satproblem"+id+".cnf";
        String solutionsPrefix = "Number of solutions: ";
        FileWriter writer = new FileWriter(filepath);
        RelsatIO.write(satProblem, writer);
        writer.close();

        String[] cmd = { "/bin/sh", "-c", "cd "+path+"; ./relsat -#c "+filepath };
        Process p = Runtime.getRuntime().exec(cmd);

        BufferedReader stdInput = new BufferedReader(new InputStreamReader(p.getInputStream()));
        BufferedReader stdError = new BufferedReader(new InputStreamReader(p.getErrorStream()));

        String s;
        while ((s = stdInput.readLine()) != null) {
            if (s.startsWith(solutionsPrefix)){
                s = s.substring(solutionsPrefix.length());
                retVal = new BigInteger(s);
            }
        }

        while ((s = stdError.readLine()) != null) {
            System.err.println("Errors when executing RELSAT: "+s);
        }
        p.waitFor();
        new File(filepath).delete();
        if (retVal == null){
            return BigInteger.ZERO;
        }
        return retVal;
    }

    public static void main(String[] args) throws Exception {
        RelsatExecutor re = new RelsatExecutor("/Users/kuzelkao_cardiff/Dropbox/Experiments/ECAI16/relsat_2.02/");
        BigInteger bi = re.modelCount(Sugar.<Clause>list(
                Clause.parse("!bird(x),flies(x)"),
                Clause.parse("bird(x),pig(x)")
        ));
        System.out.println(bi);
    }
}
