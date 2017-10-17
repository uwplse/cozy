import unittest

from cozy.desugar import desugar
from cozy.typecheck import typecheck
from cozy.parse import parse
from cozy.invariant_preservation import check_ops_preserve_invariants

def get_invariant_preservation_errs(spec : str):
    spec = parse(spec)
    errs = typecheck(spec)
    assert not errs
    spec = desugar(spec)
    return check_ops_preserve_invariants(spec)
    assert errs
    assert "modX" in errs[0]
    assert "modY" in errs[1]

class TestRepInference(unittest.TestCase):

    def test_indirect_handle_write(self):
        errs = get_invariant_preservation_errs("""
            PreserveInvariant:

                handletype T = Int
                handletype U = { score : Int }

                state xs : Bag<(T, U)>

                assume all [x.0.val > 0 | x <- xs];
                assume all [x.1.val.score > 0 | x <- xs];

                op add(x : T, y : U)
                    assume x.val > 0;
                    assume y.val.score > 0;
                    xs.add((x, y));

                op modX(x : T, newVal: Int)
                    x.val = newVal;

                op modY(y : U, newVal: Int)
                    y.val.score = newVal;

                query q()
                    xs
        """)
        assert errs
        assert "modX" in errs[0]
        assert "modY" in errs[1]
