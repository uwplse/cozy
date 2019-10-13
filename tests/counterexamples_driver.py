from cozy.random_assignment import *
from tests.counterexamples import *

for target, new_target, counterexample in tests:
    e = ENot(EEq(target, new_target))
    counterexample_2 = satisfy(e)
    assert eval(e, counterexample)
    if counterexample_2 is None:
        print("missed solution: %s\nfor: %s\n" % (counterexample, pprint(e)))
    else:
        print("Found solution\n")