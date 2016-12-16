import unittest

from cozy.synthesis.high_level_interface import CoolCostModel
from cozy.typecheck import INT, retypecheck
from cozy.target_syntax import *
from cozy.syntax_tools import equal, pprint
from cozy.solver import valid

class TestCostModel(unittest.TestCase):

    def test_map_vs_filter(self):
        # e1 = Filter {(\_var11 : xs.Handle -> ((_var11).val == z))} ((xs + []))
        xs = EVar("xs").with_type(TBag(INT))
        x = EVar("x").with_type(INT)
        z = EVar("z").with_type(INT)
        e1 = EFilter(EBinOp(xs, "+", EEmptyList().with_type(xs.type)),
            ELambda(x, equal(x, z)))
        e2 = EMapGet(
            EMakeMap(xs,
                ELambda(x, x),
                ELambda(xs, xs)),
            z)
        assert retypecheck(e1)
        assert retypecheck(e2)
        assert valid(equal(e1, e2))

        cost = CoolCostModel([xs]).cost
        assert cost(e1) > cost(e2), "{} @ {} > {} @ {}".format(pprint(e1), cost(e1), pprint(e2), cost(e2))

    def test_basics(self):
        ys = EVar('ys').with_type(TBag(THandle('ys', TInt())))
        e = EBinOp(EUnaryOp('sum', EFlatMap(EBinOp(ys, '+', EEmptyList().with_type(TBag(THandle('ys', TInt())))).with_type(TBag(THandle('ys', TInt()))), ELambda(EVar('_var12').with_type(THandle('ys', TInt())), ESingleton(ENum(1).with_type(TInt())).with_type(TBag(TInt())))).with_type(TBag(TInt()))).with_type(TInt()), '==', ENum(0).with_type(TInt())).with_type(TBool())
        assert CoolCostModel([ys]).cost(e) > 0

    def test_add_empty(self):
        ys = EVar('ys').with_type(TBag(THandle('ys', TInt())))
        e1 = ys
        e2 = EBinOp(ys, "+", EEmptyList().with_type(ys.type))
        assert retypecheck(e1)
        assert retypecheck(e2)
        cost = CoolCostModel([ys]).cost

        cm = CoolCostModel([ys])
        from cozy.synthesis.rep_inference import infer_rep
        for ex in [e1, e2]:
            print("="*50 + " " + pprint(ex))
            for (st, e) in infer_rep([ys], ex):
                print("COST={} (mem={}, cpu={}, split={})".format(cm.cost(ex), sum(cm.memcm.cost(p) for (v,p) in st), cm.rtcm.cost(e), cm.split_cost(st, e)))
                for (v, p) in st:
                    print("  {} : {} = {}".format(v.id, pprint(v.type), pprint(p)))
                print("  return {} : {}".format(pprint(e), pprint(e.type)))

        print("_" * 80)
        assert cost(e1) < cost(e2), "{} vs {}".format(cost(e1), cost(e2))

    def test_sum_empty(self):
        e1 = ENum(0).with_type(TInt())
        e2 = EUnaryOp("sum", EEmptyList().with_type(TBag(TInt()))).with_type(TInt())
        cost = CoolCostModel([]).cost

        assert cost(e1) < cost(e2), "{} vs {}".format(cost(e1), cost(e2))
