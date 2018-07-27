import unittest

from cozy.desugar import desugar
from cozy.typecheck import typecheck
from cozy.parse import parse_spec
from cozy.invariant_preservation import check_ops_preserve_invariants, check_calls_wf

def get_invariant_preservation_errs(spec : str):
    spec = parse_spec(spec)
    errs = list(typecheck(spec))
    assert not errs, str(errs)
    spec = desugar(spec)
    errs.extend(check_calls_wf(spec))
    errs.extend(check_ops_preserve_invariants(spec))
    if errs:
        print("{} errors:".format(len(errs)))
        for e in errs:
            print(" - {}".format(e))
    return errs

class TestInvariantPreservationChecks(unittest.TestCase):

    def test_indirect_handle_write(self):
        errs = get_invariant_preservation_errs("""
            PreserveInvariant:

                handletype ETRUE = Int
                handletype U = { score : Int }

                state xs : Bag<(ETRUE, U)>

                invariant all [x.0.val > 0 | x <- xs];
                invariant all [x.1.val.score > 0 | x <- xs];

                op add(x : ETRUE, y : U)
                    assume x.val > 0;
                    assume y.val.score > 0;
                    xs.add((x, y));

                op modX(x : ETRUE, newVal: Int)
                    x.val = newVal;

                op modY(y : U, newVal: Int)
                    y.val.score = newVal;

                query q()
                    xs
        """)
        assert errs
        assert "modX" in errs[0]
        assert "modY" in errs[1]

    def test_preconds(self):
        errs = get_invariant_preservation_errs("""
            PreserveInvariant:

                state x : Int

                query q()
                    assume false;
                    0

                query p()
                    q()
        """)
        assert errs
        assert "q" in errs[0]

    def test_if_guard(self):
        errs = get_invariant_preservation_errs("""
            PreserveInvariant:

                state x : Int

                query q()
                    assume false;
                    0

                op foo()
                    if (1 < 0) { x = q(); }
        """)
        assert not errs

    def test_update_sequence(self):
        errs = get_invariant_preservation_errs("""
            PreserveInvariant:

                state x : Int

                query q()
                    assume x > 0;
                    0

                op foo()
                    x = 1;
                    x = q();
        """)
        assert not errs

    def test_no_update_leakage(self):
        errs = get_invariant_preservation_errs("""
            PreserveInvariant:

                state x : Int

                query q()
                    assume x > 0;
                    0

                op foo()
                    x = 1;
                    x = 2;

                op bar()
                    x = q();
        """)
        assert errs
        assert "q" in errs[0]

    def test_guarded_update_sequence(self):
        errs = get_invariant_preservation_errs("""
            PreserveInvariant:

                state x : Int

                query q()
                    assume x > 0;
                    0

                op foo(b : Bool)
                    if (b) {
                        x = 1;
                        x = 2;
                    }
                    x = q();
        """)
        assert errs
        assert "q" in errs[0]

    def test_guard_with_let(self):
        errs = get_invariant_preservation_errs("""
            PreserveInvariant:

                state x : Int

                query q()
                    assume x > 0;
                    0

                op foo(b : Bool)
                    let a = false;
                    if (a) {
                        x = q();
                    }
        """)
        assert not errs

    def test_guard_after_mutation(self):
        errs = get_invariant_preservation_errs("""
            PreserveInvariant:

                state x : Int

                query q()
                    assume x > 0;
                    0

                op foo(b : Bool)
                    x = 1;
                    if (x < 0) {
                        x = q();
                    }
        """)
        assert not errs
