/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.possibilistic.learning.misc;

import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import supertweety.defaults.DefaultRule;
import supertweety.possibilistic.learning.DatasetReader;

import java.io.Reader;
import java.io.Writer;
import java.util.List;

/**
 * Created by kuzelkao_cardiff on 05/11/15.
 */
public class ArffFromDefaults {

    public static void writeArffFiles(Reader positiveExamples, Reader negativeExamples, Reader positiveTestExamples, Reader negativeTestExamples,
                                      Writer trainOutput, Writer testOutput) throws Exception {

        List<DefaultRule> defaultsTest = DatasetReader.readDefaultRuleDataset(positiveTestExamples);
        List<DefaultRule> nondefaultsTest = DatasetReader.readDefaultRuleDataset(negativeTestExamples);

        Table<String,String> testTable = new Table<String,String>();
        int i = 0;
        for (DefaultRule rule : defaultsTest){
            for (Literal l : rule.antecedent().literals()){
                testTable.add(String.valueOf(i), "Ant: "+l.toString(), "+");
            }
            testTable.add(String.valueOf(i), "Cons: "+rule.consequent().toString(), "+");
            testTable.addClassification(String.valueOf(i), "+");
            i++;
        }
        for (DefaultRule rule : nondefaultsTest){
            for (Literal l : rule.antecedent().literals()){
                testTable.add(String.valueOf(i), "Ant: "+l.toString(), "+");
            }
            testTable.add(String.valueOf(i), "Cons: "+rule.consequent().toString(), "+");
            testTable.addClassification(String.valueOf(i), "-");
            i++;
        }
        for (String attribute : testTable.attributes()){
            testTable.setAttributeDefaultValue(attribute, "-");
        }

        List<DefaultRule> defaults = DatasetReader.readDefaultRuleDataset(positiveExamples);
        List<DefaultRule> nondefaults = DatasetReader.readDefaultRuleDataset(negativeExamples);
        Table<String,String> trainTable = new Table<String,String>();
        i = 0;
        for (DefaultRule rule : defaults){
            for (Literal l : rule.antecedent().literals()){
                trainTable.add(String.valueOf(i), "Ant: "+l.toString(), "+");
            }
            trainTable.add(String.valueOf(i), "Cons: "+rule.consequent().toString(), "+");
            trainTable.addClassification(String.valueOf(i), "+");
            i++;
        }
        for (DefaultRule rule : nondefaults){
            for (Literal l : rule.antecedent().literals()){
                trainTable.add(String.valueOf(i), "Ant: "+l.toString(), "+");
            }
            trainTable.add(String.valueOf(i), "Cons: "+rule.consequent().toString(), "+");
            trainTable.addClassification(String.valueOf(i), "-");
            i++;
        }
        for (String attribute : trainTable.attributes()){
            trainTable.setAttributeDefaultValue(attribute, "-");
        }

        for (String a : Sugar.collectionDifference(testTable.attributes(), trainTable.attributes())){
            testTable.removeAttribute(a);
        }
        for (String a : Sugar.collectionDifference(trainTable.attributes(), testTable.attributes())){
            for (String example : testTable.examples()){
                testTable.add(example, a, "-");
            }
        }

        testTable.makeCompatible(trainTable);
        trainTable.makeCompatible(testTable);

        trainTable.saveWithoutFiltering(trainOutput);
        testTable.saveWithoutFiltering(testOutput);
    }

    public static void writeMulticlassArffFiles(Reader positiveExamples, Reader positiveTestExamples,
                                      Writer trainOutput, Writer testOutput) throws Exception {

        List<DefaultRule> defaultsTest = DatasetReader.readDefaultRuleDataset(positiveTestExamples);

        Table<String,String> testTable = new Table<String,String>();
        int i = 0;
        for (DefaultRule rule : defaultsTest){
            for (Literal l : rule.antecedent().literals()){
                testTable.add(String.valueOf(i), "Ant: "+l.toString(), "+");
            }
            testTable.addClassification(String.valueOf(i), Sugar.chooseOne(rule.consequent().literals()).toString());
            i++;
        }
        for (String attribute : testTable.attributes()){
            testTable.setAttributeDefaultValue(attribute, "-");
        }

        List<DefaultRule> defaults = DatasetReader.readDefaultRuleDataset(positiveExamples);
        Table<String,String> trainTable = new Table<String,String>();
        i = 0;
        for (DefaultRule rule : defaults){
            for (Literal l : rule.antecedent().literals()){
                trainTable.add(String.valueOf(i), "Ant: "+l.toString(), "+");
            }
            trainTable.addClassification(String.valueOf(i), Sugar.chooseOne(rule.consequent().literals()).toString());
            i++;
        }
        for (String attribute : trainTable.attributes()){
            trainTable.setAttributeDefaultValue(attribute, "-");
        }

        for (String a : Sugar.collectionDifference(testTable.attributes(), trainTable.attributes())){
            testTable.removeAttribute(a);
        }
        for (String a : Sugar.collectionDifference(trainTable.attributes(), testTable.attributes())){
            for (String example : testTable.examples()){
                testTable.add(example, a, "-");
            }
        }

        testTable.makeCompatible(trainTable);
        trainTable.makeCompatible(testTable);

        trainTable.saveWithoutFiltering(trainOutput);
        testTable.saveWithoutFiltering(testOutput);
    }

}
