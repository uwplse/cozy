from cozy.counterexample import *
from tests.counterexamples import *

for target, new_target, counterexample in tests:
    e = ENot(EEq(target, new_target))
    counterexample_2 = find_counterexample(e)
    if counterexample_2 is None:
        print("missed counter-example: %s\nfor: %s\n" % (counterexample, pprint(e)))