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

import ida.utils.Sugar;
import supertweety.defaults.DefaultRule;

import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;

/**
 * Created by kuzelkao_cardiff on 03/11/15.
 */
public class DatasetReader {

    public final static String ARROW = "->";

    public static List<DefaultRule> readDefaultRuleDataset(Reader reader) throws IOException {
        List<DefaultRule> retVal = new ArrayList<DefaultRule>();
        for (String line : Sugar.readLines(reader)){
            line = line.trim();
            if (line.contains(ARROW)){
                String[] spl = line.split("->");
                if (spl.length == 2){
                    retVal.add(new DefaultRule(spl[0], spl[1]));
                } else if (spl.length == 1){
                    if (line.startsWith(ARROW)){
                        retVal.add(new DefaultRule("", spl[0]));
                    } else {
                        //... nothing ...
                    }
                } else {
                    //... nothing ...
                }
            }
        }
        return retVal;
    }

    public static void main(String[] args) throws Exception {
        Reader r = new FileReader("/Users/kuzelkao_cardiff/Dropbox/Experiments/KR/datasets/plants/plants.defaults.txt");
        for (DefaultRule dr : readDefaultRuleDataset(r)){
            System.out.println(dr);
        }
    }
}
