# learning-from-defaults

The learning algorithms can be used with the following parameter settings.

Incremental heuristic learning:

-pos poker.defaults.txt -neg poker.nondefaults.txt -testpos poker.defaults.test.txt -testneg poker.nondefaults.test.txt -hardRules /Users/kuzelkao_cardiff/Dropbox/Experiments/KR/datasets/poker/poker.hardrules.txt -ruleSubsampling true -iterations 100 -method incremental

SAYU learning (only usable for small number of iterations because it needs to run the exact parameter learning algorithm)

-pos poker.defaults.txt -neg poker.nondefaults.txt -testpos poker.defaults.test.txt -testneg poker.nondefaults.test.txt -hardRules /Users/kuzelkao_cardiff/Dropbox/Experiments/KR/datasets/poker/poker.hardrules.txt -ruleSubsampling true -iterations 100 -method SAYU
