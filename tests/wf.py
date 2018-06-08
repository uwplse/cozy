import unittest

from cozy.common import OrderedSet
from cozy.target_syntax import *
from cozy.structures.heaps import *
from cozy.pools import RUNTIME_POOL
from cozy.typecheck import retypecheck
from cozy.wf import exp_wf
from cozy.contexts import RootCtx

class TestWf(unittest.TestCase):

    def test_heap_wf(self):
        e = EHeapPeek2(EStateVar(EMakeMinHeap(EVar('xs'), ELambda(EVar('_var21501'), EVar('_var21501')))), EStateVar(EUnaryOp('len', EVar('xs'))))
        assert retypecheck(e, env={
            "xs": INT_BAG,
            "_var21501": INT})
        state_vars = OrderedSet([EVar('xs').with_type(TBag(TInt()))])
        args = OrderedSet([EVar('x').with_type(TInt())])
        pool = RUNTIME_POOL
        assert exp_wf(e, context=RootCtx(args=args, state_vars=state_vars), pool=pool)
