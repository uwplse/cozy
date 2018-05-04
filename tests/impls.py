import pickle
import unittest

from cozy.parse import parse
from cozy.typecheck import typecheck
from cozy.desugar import desugar
from cozy.syntax_tools import pprint
from cozy.synthesis.impls import construct_initial_implementation

class TestImplObjects(unittest.TestCase):

    def test_pickling(self):
        i = parse("""
            Foo:
                type T = Native "int"
                extern newX(x : Int) : T = "..."
                extern readX(x : T) : Int = "..."
                state xs : Set<T>
                state intsA : Set<Int>
                state intsB : Set<Int>
                invariant intsA == [readX(x) - 1 | x <- xs];
                invariant intsB == [readX(x) + 1 | x <- xs];
                query getA()
                    intsA
                query getB()
                    intsB
            """)
        errs = typecheck(i)
        assert not errs, errs
        i = desugar(i)
        i1 = construct_initial_implementation(i)
        print(pprint(i1.code))
        i2 = pickle.loads(pickle.dumps(i1))
        assert i1.code == i2.code
