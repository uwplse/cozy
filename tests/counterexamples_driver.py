from cozy.counterexample import *
from tests.counterexamples import *

for target, new_target, counterexample in tests:
    e = ENot(EEq(target, new_target))
    counterexample_2 = find_counterexample(e)
    assert counterexample == counterexample_2, pprint(e)
