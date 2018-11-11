from cozy.common import pick_to_sum
from cozy.syntax import *
from cozy.target_syntax import TArray, SArrayAlloc
from cozy.syntax_tools import fresh_var, pprint
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL
from cozy.codegen.misc import EEscape, SEscape

TMinOrdered = declare_case(Type, "TMinOrdered", ["elem_type"])
TMaxOrdered = declare_case(Type, "TMaxOrdered", ["elem_type"])
EMakeMinOrdered = declare_case(Exp, "EMakeMinOrdered", ["e"])
def with_type_safe(self, t):
    assert isinstance(t, TMinOrdered)
    self.type = t
    return self
EMakeMinOrdered.with_type = with_type_safe
def with_type_safe_max(self, t):
    assert isinstance(t, TMaxOrdered)
    self.type = t
    return self
EMakeMaxOrdered = declare_case(Exp, "EMakeMaxOrdered", ["e"])
EMakeMaxOrdered.with_type = with_type_safe_max

EOrderedElems = declare_case(Exp, "EOrderedElems", ["e"])

def _parent(idx : Exp) -> Exp:
    return EBinOp(idx, "-", ONE).with_type(INT)

class Ordereds(object):

    def owned_types(self):
        return (TMinOrdered, TMaxOrdered, EMakeMinOrdered, EMakeMaxOrdered, EOrderedElems)

    def default_value(self, t : Type, default_value) -> Exp:
        """Construct a default value of the given type.

        The `default_value` parameter should be used to recursively construct
        a default value of a child type.
        """

        f = EMakeMinOrdered if isinstance(t, TMinOrdered) else EMakeMaxOrdered
        return f(EEmptyList().with_type(TBag(t.elem_type))).with_type(t)

    def check_wf(self, e : Exp, is_valid, state_vars : {EVar}, args : {EVar}, pool = RUNTIME_POOL, assumptions : Exp = ETRUE):
        """Return None or a string indicating a well-formedness error."""
        return None

    def possibly_useful(self,
            e           : Exp,
            context,
            pool        : Pool,
            assumptions : Exp,
            ops         : [Op],
            solver) -> bool:
        return True

    def typecheck(self, e : Exp, typecheck, report_err):
        """Typecheck expression `e`.

        This function must write a type to `e.type` or call `report_err` to
        indicate a type error.  It is allowed to do both.

        The `typecheck` parameter should be used to make a recursive call to
        typecheck child nodes.
        """
        if isinstance(e, EMakeMaxOrdered):
            typecheck(e.e)
            e.type = TMaxOrdered(e.e.type.elem_type)
        elif isinstance(e, EMakeMinOrdered):
            typecheck(e.e)
            e.type = TMinOrdered(e.e.type.elem_type)
        elif isinstance(e, EOrderedElems):
            typecheck(e.e)
            if isinstance(e.e.type, TMinOrdered) or isinstance(e.e.type, TMaxOrdered):
                e.type = TList(e.e.type.elem_type)
            else:
                report_err(e, "cannot get ordered elems of non-ordered")
        else:
            raise NotImplementedError(e)

    def encoding_type(self, t : Type) -> Type:
        assert isinstance(t, TMaxOrdered) or isinstance(t, TMinOrdered)
        return TList(t.elem_type)

    def encode(self, e : Exp) -> Exp:
        if isinstance(e, EMakeMinOrdered):
            return ESorted(e.e, ETRUE).with_type(TList(e.e.type.elem_type))
        elif isinstance(e, EMakeMaxOrdered):
            return ESorted(e.e, EFALSE).with_type(TList(e.e.type.elem_type))
        elif isinstance(e, EOrderedElems):
            if isinstance(e.e, EMakeMaxOrdered):
                return ESorted(e.e.e, EFALSE).with_type(e.type)
            elif isinstance(e.e, EMakeMinOrdered):
                return ESorted(e.e.e, ETRUE).with_type(e.type)
        raise NotImplementedError(e)

    def enumerate(self, context, size, pool, enumerate_subexps, enumerate_lambdas):
        from cozy.typecheck import is_collection

        if pool == STATE_POOL:
            for (sz1, sz2) in pick_to_sum(2, size-1):
                for e in enumerate_subexps(context, sz1, pool):
                    if is_collection(e.type):
                        elem_type = e.type.elem_type
                        yield EMakeMaxOrdered(e).with_type(TMaxOrdered(elem_type))
                        yield EMakeMinOrdered(e).with_type(TMinOrdered(elem_type))

    def storage_size(self, e : Exp, storage_size) -> Exp:
        """Compute the storage size (in bytes) of the given expression.

        The `storage_size` parameter should be used to recursively compute
        storage sizes for other expressions.
        """
        assert type(e.type) in (TMinOrdered, TMaxOrdered)
        return storage_size(EOrderedElems(e).with_type(TList(e.type.elem_type)))

    def mutate_in_place(self, lval, e, op, assumptions, invariants, make_subgoal):
        t = TBag(lval.type.elem_type)
        if op.func == "add":
            x = op.args[0]
            return SCall(lval, "add_all", (ESingleton(x).with_type(t),))
        elif op.func == "remove":
            x = op.args[0]
            return SCall(lval, "remove_all", (ESingleton(x).with_type(t),))

    def rep_type(self, t : Type) -> Type:
        assert isinstance(t, TMinOrdered) or isinstance(t, TMaxOrdered), repr(t)
        return TNative("TreeMultiset<Integer>")

    def codegen(self, e : Exp, concretization_functions : { str : Exp }, out : EVar) -> Stm:
        """Return statements that write the result of `e` to `out`.

        The returned statements must declare the variable `out`; it will not be
        declared by the caller.

        This function also requires the `concretization_functions` that
        describe the invariants for variables in `e`.
        """
        if isinstance(e, EMakeMinOrdered) or isinstance(e, EMakeMaxOrdered):
            if isinstance(e, EMakeMinOrdered):
                constructor = "TreeMultiset.create()"
            else:
                constructor = "TreeMultiset.create(java.util.Comparator.reverseOrder())"
            assert out.type == self.rep_type(e.type)
            elem_type = e.type.elem_type
            extended_concretization_functions = dict(concretization_functions)
            extended_concretization_functions[out.id] = e
            dummy_out = EVar(out.id).with_type(e.type)
            a = fresh_var(TArray(elem_type), "ordered_elems")
            return seq([
                SArrayAlloc(a, ZERO),
                SDecl(out, EEscape(constructor, (), ())),
                self.implement_stmt(SCall(dummy_out, "add_all", (e.e,)), extended_concretization_functions)])
        elif isinstance(e, EOrderedElems):
            elem_type = e.type.elem_type
            x = fresh_var(elem_type, "x")
            from cozy.syntax_tools import shallow_copy
            xs = shallow_copy(e.e).with_type(e.type)
            return seq([
                SDecl(out, EEmptyList().with_type(out.type)),
                SForEach(x, xs, SCall(out, "add", (x,)))])
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
                return SForEach(x, s.args[0], SEscape("{indent}{target}.add({x});\n", ("target", "x"), (target, x)))
            elif s.func == "remove_all":
                x = fresh_var(elem_type, "x")
                return SForEach(x, s.args[0], SEscape("{indent}{target}.remove({x});\n", ("target", "x"), (target, x)))
            else:
                raise ValueError("ordereds do not support the function {}".format(s.func))
        else:
            raise ValueError("the statement {} is not an update to a ordered variable".format(pprint(s)))
