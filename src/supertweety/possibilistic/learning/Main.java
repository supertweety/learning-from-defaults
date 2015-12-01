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
import ida.utils.CommandLine;
import ida.utils.Sugar;
import ida.utils.tuples.Quadruple;
import supertweety.defaults.DefaultRule;
import supertweety.possibilistic.PossibilisticLogicTheory;
import supertweety.possibilistic.learning.misc.ArffFromDefaults;

import java.io.FileReader;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Created by kuzelkao_cardiff on 03/11/15.
 */
public class Main {

    public static void main(String[] args) throws Exception {
        long time1 = System.currentTimeMillis();
        Map<String,String> params = CommandLine.parseParams(args);
        if (params.containsKey("-action")){
            String action = params.get("-action");
            if (action.equals("arff")){
                String pos = params.get("-pos");
                String neg = params.get("-neg");
                String posTest = params.get("-testpos");
                String negTest = params.get("-testneg");
                String trainArff = pos+".train.arff";
                String testArff = pos+".test.arff";
                FileReader posReader = new FileReader(pos);
                FileReader negReader = new FileReader(neg);
                FileReader posTestReader = new FileReader(posTest);
                FileReader negTestReader = new FileReader(negTest);
                FileWriter trainWriter = new FileWriter(trainArff);
                FileWriter testWriter = new FileWriter(testArff);
                ArffFromDefaults.writeArffFiles(posReader, negReader, posTestReader, negTestReader, trainWriter, testWriter);
                posReader.close();
                negReader.close();
                posTestReader.close();
                negTestReader.close();
                trainWriter.close();
                testWriter.close();
            } else if (action.equals("multiclassArff")){
                String pos = params.get("-pos");
                String posTest = params.get("-testpos");
                String trainArff = pos+".mcl.train.arff";
                String testArff = pos+".mcl.test.arff";
                FileReader posReader = new FileReader(pos);
                FileReader posTestReader = new FileReader(posTest);
                FileWriter trainWriter = new FileWriter(trainArff);
                FileWriter testWriter = new FileWriter(testArff);
                ArffFromDefaults.writeMulticlassArffFiles(posReader, posTestReader, trainWriter, testWriter);
                posReader.close();
                posTestReader.close();
                trainWriter.close();
                testWriter.close();
            }
        } else {
            String pos = params.get("-pos");
            String neg = params.get("-neg");
            String posTest = params.get("-testpos");
            String negTest = params.get("-testneg");
            String iterations = params.get("-iterations");
            List<DefaultRule> defaults = DatasetReader.readDefaultRuleDataset(new FileReader(pos));
            List<DefaultRule> nondefaults = DatasetReader.readDefaultRuleDataset(new FileReader(neg));
            List<Clause> hardRules = null;
            if (params.containsKey("-hardRules")){
                hardRules = new ArrayList<Clause>();
                for (String line : Sugar.readLines(new FileReader(params.get("-hardRules")))){
                    line = line.trim();
                    if (line.length() > 0){
                        hardRules.add(Clause.parse(line));
                    }
                }
            }

            PossibilisticLearner pl = new PossibilisticLearner(defaults, nondefaults, hardRules);

            if (params.containsKey("-candidates")){
                pl.setCandidatesSampleSize(Integer.parseInt(params.get("-candidates")));
            }
            if (params.containsKey("-ruleSubsampling")){
                pl.setSampleSubRules(Boolean.parseBoolean(params.get("-ruleSubsampling")));
            }
            if (params.containsKey("-candidateSampleSize")){
                pl.setCandidatesSampleSize(Integer.parseInt(params.get("-candidateSampleSize")));
            }
            if (params.containsKey("-rules")){
                List<Clause> rules = new ArrayList<Clause>();
                for (String line : Sugar.readLines(new FileReader(params.get("-rules")))){
                    line = line.trim();
                    if (line.length() > 0){
                        rules.add(Clause.parse(line));
                    }
                    System.out.println(line);
                }
                pl.setRules(rules);
            }


            final int INCREMENTAL = 1, SAYU = 2, MEMOIZATION_OF_DEFAULTS = 3, WEIGHT_LEARNING = 4;
            int mode = INCREMENTAL;
            if (params.containsKey("-method")){
                if (params.get("-method").equals("incremental")){
                    mode = INCREMENTAL;
                } else if (params.get("-method").equals("sayu")){
                    mode = SAYU;
                } else if (params.get("-method").equals("memoization")){
                    mode = MEMOIZATION_OF_DEFAULTS;
                } else if (params.get("-method").equals("weightlearning")){
                    mode = WEIGHT_LEARNING;
                }
            }

            PossibilisticLogicTheory learnedTheory = null;

            if (mode == INCREMENTAL) {
                learnedTheory = pl.greedyIncrementalLearner(Integer.parseInt(iterations));
            } else if (mode == SAYU){
                learnedTheory = pl.greedySayuLearn(Integer.parseInt(iterations));
            } else if (mode == WEIGHT_LEARNING){
                learnedTheory = pl.weightLearning();
            }

            System.out.println(learnedTheory);

            if (posTest != null && negTest != null) {
                List<DefaultRule> testDefaults = DatasetReader.readDefaultRuleDataset(new FileReader(posTest));
                List<DefaultRule> testNondefaults = DatasetReader.readDefaultRuleDataset(new FileReader(negTest));

                if (learnedTheory != null) {
                    List<DefaultRule> coveredPositiveTest = LearningUtils.coveredExamples(learnedTheory, testDefaults);
                    List<DefaultRule> coveredNegativeTest = LearningUtils.coveredExamples(learnedTheory, testNondefaults);
                    double coveredPositive = coveredPositiveTest.size();
                    double coveredNegative = coveredNegativeTest.size();
                    double accuracy = (coveredPositive + testNondefaults.size() - coveredNegative) / (testDefaults.size() + testNondefaults.size());
                    double majorityAccuracy = Math.max(testDefaults.size(), testNondefaults.size()) / (double) (testDefaults.size() + testNondefaults.size());
                    System.out.println("Covered positive: " + coveredPositive);
                    System.out.println("Covered negative: " + coveredNegative);
                    System.out.println("Accuracy: " + accuracy);
                }

                if (mode == INCREMENTAL){
                    List<Double> testSetAccuracies = new ArrayList<Double>();
                    List<Double> trainSetAccuracies = new ArrayList<Double>();
                    List<Quadruple<Double,Double,Double,Double>> stats = new ArrayList<Quadruple<Double,Double,Double,Double>>();
                    for (PossibilisticLogicTheory theoryN : pl.incrementalLearnerHistory()){
                        List<DefaultRule> coveredPosTest = LearningUtils.coveredExamples(theoryN, testDefaults);
                        List<DefaultRule> coveredNegTest = LearningUtils.coveredExamples(theoryN, testNondefaults);
                        List<DefaultRule> coveredPosTrain = LearningUtils.coveredExamples(theoryN, defaults);
                        List<DefaultRule> coveredNegTrain = LearningUtils.coveredExamples(theoryN, nondefaults);
                        double acc = (coveredPosTest.size() + testNondefaults.size() - coveredNegTest.size()) / (double)(testDefaults.size() + testNondefaults.size());
                        double trainAcc = (coveredPosTrain.size() + nondefaults.size() - coveredNegTrain.size()) / (double)(defaults.size() + nondefaults.size());
                        testSetAccuracies.add(acc);
                        trainSetAccuracies.add(trainAcc);
                        stats.add(new Quadruple<Double,Double,Double,Double>((double)coveredPosTrain.size(), (double)coveredNegTrain.size(), (double)coveredPosTest.size(), (double)coveredNegTest.size()));
                    }
                    System.out.println("lc = "+testSetAccuracies);
                    System.out.println("train_lc = "+trainSetAccuracies);
                    System.out.println("stats: "+stats);
                } else if (mode == SAYU){

                } else if (mode == MEMOIZATION_OF_DEFAULTS){
                    List<DefaultRule> misclassified = new ArrayList<DefaultRule>();
                    Set<DefaultRule> positiveSet = Sugar.setFromCollections(defaults);
                    for (DefaultRule d : testDefaults){
                        if (!positiveSet.contains(d)){
                            misclassified.add(d);
                        }
                    }
                    for (DefaultRule d : testNondefaults){
                        if (positiveSet.contains(d)){
                            misclassified.add(d);
                        }
                    }
                    double testAcc = 1.0-misclassified.size()/(double)(testDefaults.size()+testNondefaults.size());
                    System.out.println("Memoization accuracy: "+testAcc);
                }
            }
        }
        long time2 = System.currentTimeMillis();
        System.out.println("Finished in "+(time2-time1)+"ms");
    }

}
