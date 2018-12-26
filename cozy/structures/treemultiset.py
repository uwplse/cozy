'''Ordered multiset structure
TODO(zhen): define a virtual class for universal structure extension
            and move useful documentation there from heaps.py and this file
'''

from cozy.common import pick_to_sum, No
from cozy.syntax import *
from cozy.syntax_tools import fresh_var, pprint, inline_lets
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL

TTreeMultiset = declare_case(Type, "TTreeMultisetNative", ["elem_type"])
SInsert  = declare_case(Stm, "SInsert", ["target", "x"])
SErase   = declare_case(Stm, "SErase",  ["target", "x"])

TMinTreeMultiset = declare_case(Type, "TMinTreeMultiset", ["elem_type"])
TMaxTreeMultiset = declare_case(Type, "TMaxTreeMultiset", ["elem_type"])
EMakeMaxTreeMultiset = declare_case(Exp, "EMakeMaxTreeMultiset", ["e"])
EMakeMinTreeMultiset = declare_case(Exp, "EMakeMinTreeMultiset", ["e"])
def with_type_safe_min(self, t):
    assert isinstance(t, TMinTreeMultiset)
    self.type = t
    return self
def with_type_safe_max(self, t):
    assert isinstance(t, TMaxTreeMultiset)
    self.type = t
    return self
EMakeMaxTreeMultiset.with_type = with_type_safe_max
EMakeMinTreeMultiset.with_type = with_type_safe_min

ETreeMultisetElems = declare_case(Exp, "ETreeMultisetElems", ["e"])
ETreeMultisetPeek  = declare_case(Exp, "ETreeMultisetPeek", ["e", "index"])

def _parent(idx : Exp) -> Exp:
    return EBinOp(idx, "-", ONE).with_type(INT)

class Ordereds(object):

    def owned_types(self):
        return (TMinTreeMultiset, TMaxTreeMultiset, EMakeMinTreeMultiset, EMakeMaxTreeMultiset, ETreeMultisetElems, ETreeMultisetPeek)

    def default_value(self, t : Type, default_value) -> Exp:
        """Construct a default value of the given type.

        The `default_value` parameter should be used to recursively construct
        a default value of a child type.
        """

        f = EMakeMinTreeMultiset if isinstance(t, TMinTreeMultiset) else EMakeMaxTreeMultiset
        return f(EEmptyList().with_type(TBag(t.elem_type))).with_type(t)

    def check_wf(self, e : Exp, is_valid, state_vars : {EVar}, args : {EVar}, pool = RUNTIME_POOL, assumptions : Exp = ETRUE):
        """Return None or a string indicating a well-formedness error."""
        return None

    # TODO(zhen): document this
    def possibly_useful(self,
            e           : Exp,
            context,
            pool        : Pool,
            assumptions : Exp,
            ops         : [Op],
            solver) -> bool:
        if isinstance(e, ETreeMultisetPeek):
            if pool != RUNTIME_POOL:
                return No("ordered peek in state position")
        return True

    def typecheck(self, e : Exp, typecheck, report_err):
        """Typecheck expression `e`.

        This function must write a type to `e.type` or call `report_err` to
        indicate a type error.  It is allowed to do both.

        The `typecheck` parameter should be used to make a recursive call to
        typecheck child nodes.
        """
        from cozy.typecheck import is_scalar
        if isinstance(e, EMakeMaxTreeMultiset):
            assert is_scalar(e.e.type.elem_type)
            typecheck(e.e)
            e.type = TMaxTreeMultiset(e.e.type.elem_type)
        elif isinstance(e, EMakeMinTreeMultiset):
            assert is_scalar(e.e.type.elem_type)
            typecheck(e.e)
            e.type = TMinTreeMultiset(e.e.type.elem_type)
        elif isinstance(e, ETreeMultisetPeek):
            typecheck(e.e)
            typecheck(e.index)
            ok = True
            if not (isinstance(e.e.type, (TMaxTreeMultiset, TMinTreeMultiset)) and isinstance(e.index.type, INT)):
                report_err(e, "cannot peek a non-ordered")
                ok = False
            if ok:
                e.type = e.e.type.elem_type
        elif isinstance(e, ETreeMultisetElems):
            typecheck(e.e)
            if isinstance(e.e.type, TMinTreeMultiset) or isinstance(e.e.type, TMaxTreeMultiset):
                e.type = TList(e.e.type.elem_type)
            else:
                report_err(e, "cannot get ordered elems of non-ordered")
        else:
            raise NotImplementedError(e)

    def encoding_type(self, t : Type) -> Type:
        assert isinstance(t, TMaxTreeMultiset) or isinstance(t, TMinTreeMultiset)
        return TList(t.elem_type)

    def encode(self, e : Exp) -> Exp:
        if isinstance(e, EMakeMinTreeMultiset):
            return ESorted(e.e, ETRUE).with_type(TList(e.e.type.elem_type))
        elif isinstance(e, EMakeMaxTreeMultiset):
            return ESorted(e.e, EFALSE).with_type(TList(e.e.type.elem_type))
        elif isinstance(e, ETreeMultisetElems):
            ee = inline_lets(e.e)
            if isinstance(ee, EMakeMaxTreeMultiset):
                return ESorted(ee.e, EFALSE).with_type(e.type)
            elif isinstance(ee, EMakeMinTreeMultiset):
                return ESorted(ee.e, ETRUE).with_type(e.type)
        elif isinstance(e, ETreeMultisetPeek):
            return EListGet(e.e, e.index).with_type(e.type)
        raise NotImplementedError(e)

    def enumerate(self, context, size, pool, enumerate_subexps, enumerate_lambdas):
        from cozy.typecheck import is_collection

        if pool == STATE_POOL:
            for (sz1, sz2) in pick_to_sum(2, size-1):
                for e in enumerate_subexps(context, sz1, pool):
                    if is_collection(e.type):
                        elem_type = e.type.elem_type
                        yield EMakeMaxTreeMultiset(e).with_type(TMaxTreeMultiset(elem_type))
                        yield EMakeMinTreeMultiset(e).with_type(TMinTreeMultiset(elem_type))

    def storage_size(self, e : Exp, storage_size) -> Exp:
        """Compute the storage size (in bytes) of the given expression.

        The `storage_size` parameter should be used to recursively compute
        storage sizes for other expressions.
        """
        assert type(e.type) in (TMinTreeMultiset, TMaxTreeMultiset)
        return storage_size(ETreeMultisetElems(e).with_type(TList(e.type.elem_type)))

    def mutate_in_place(self, lval, e, op, assumptions, invariants, make_subgoal):
        # TODO: maybe we can remove this check
        if not isinstance(op, SCall):
            return
        t = TBag(lval.type.elem_type)
        if op.func == "add":
            x = op.args[0]
            return SCall(lval, "add_all", (ESingleton(x).with_type(t),))
        elif op.func == "remove":
            x = op.args[0]
            return SCall(lval, "remove_all", (ESingleton(x).with_type(t),))

    def rep_type(self, t : Type) -> Type:
        assert isinstance(t, TMinTreeMultiset) or isinstance(t, TMaxTreeMultiset), repr(t)
        return TTreeMultiset(t.elem_type)

    def codegen(self, e : Exp, concretization_functions : { str : Exp }, out : EVar) -> Stm:
        """Return statements that write the result of `e` to `out`.

        The returned statements must declare the variable `out`; it will not be
        declared by the caller.

        This function also requires the `concretization_functions` that
        describe the invariants for variables in `e`.
        """
        if isinstance(e, EMakeMinTreeMultiset) or isinstance(e, EMakeMaxTreeMultiset):
            assert out.type == self.rep_type(e.type)
            extended_concretization_functions = dict(concretization_functions)
            extended_concretization_functions[out.id] = e
            dummy_out = EVar(out.id).with_type(e.type)
            return seq([
                SDecl(out, None),
                self.implement_stmt(SCall(dummy_out, "add_all", (e.e,)), extended_concretization_functions)])
        elif isinstance(e, ETreeMultisetElems):
            elem_type = e.type.elem_type
            x = fresh_var(elem_type, "x")
            from cozy.syntax_tools import shallow_copy
            xs = shallow_copy(e.e).replace_type(e.type)
            return seq([
                SDecl(out, EEmptyList().with_type(out.type)),
                SForEach(x, xs, SCall(out, "add", (x,)))])
        elif isinstance(e, ETreeMultisetPeek):
            return SDecl(out, e)
        else:
            raise NotImplementedError(e)

    def implement_stmt(self, s : Stm, concretization_functions : { str : Exp }) -> Stm:
        """Convert a call to a ordered function into simpler statements.

        This function also requires the `concretization_functions` that
        describe the invariants for variables in `e`.
        """
        if isinstance(s, SCall):
            elem_type = s.target.type.elem_type
            target = EVar(s.target.id).with_type(self.rep_type(s.target.type))
            if s.func == "add_all":
                x = fresh_var(elem_type, "x")
                return SForEach(x, s.args[0], SInsert(target, x))
            elif s.func == "remove_all":
                x = fresh_var(elem_type, "x")
                return SForEach(x, s.args[0], SErase(target, x))
            else:
                raise ValueError("ordereds do not support the function {}".format(s.func))
        else:
            raise ValueError("the statement {} is not an update to a ordered variable".format(pprint(s)))
