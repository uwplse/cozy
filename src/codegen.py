import collections

import plans
import predicates
from common import fresh_name
import structures
from abstract_types import (
    Iterable,
    SortedIterable,
    BinarySearchable,
    Bucketed,
    GuardedImpl,
    Combine,
    AbstractFilter,
    implement)

def enumerate_impls(fields, queries, args, extra_structures=None):
    """
    Code generation entry point.
      fields    - dict of {field_name : type}
      queries   - list of queries.Query objects with .bestPlans set
    Sets q.all_impls for each q in queries
    Returns an iterator of [ConcreteImpl] (one entry per query)
    """

    if extra_structures is None:
        extra_structures = lambda f: f

    @extra_structures
    def concretize(aimpl):
        if type(aimpl) is Iterable:
            yield structures.LinkedList()
            if args.enable_arrays:
                yield structures.ArrayList()
        elif type(aimpl) is SortedIterable:
            yield structures.AugTree(structures.interface.NativeTy(aimpl.fields[aimpl.sortField]), aimpl.sortField, aimpl.predicate, aimpl.fields)
            # yield structures.SortedArray(aimpl.field_type, aimpl.field_name) # TODO
        elif type(aimpl) is BinarySearchable:
            for sortField in set(v.name for v in aimpl.predicate.vars()):
                if sortField in fields:
                    yield structures.AugTree(structures.interface.NativeTy(fields[sortField]), sortField, aimpl.predicate, aimpl.fields)
                    # yield structures.SortedArray(aimpl.field_type, sortField, aimpl.field_name) # TODO
            if args.enable_volume_trees:
                for v in structures.VolumeTree.infer_volume(aimpl.fields, aimpl.predicate):
                    yield structures.VolumeTree(v, aimpl.fields, aimpl.predicate, stack_iteration=False)
                    yield structures.VolumeTree(v, aimpl.fields, aimpl.predicate, stack_iteration=True)
        elif type(aimpl) is Bucketed:
            for impl in concretize(aimpl.value_impl):
                if aimpl.enum_p and aimpl.rest_p:
                    for m in concretize(aimpl.rest_p):
                        yield structures.VectorMap(aimpl.fields, predicates.conjunction(aimpl.enum_p), m)
                elif aimpl.enum_p:
                    yield structures.VectorMap(aimpl.fields, predicates.conjunction(aimpl.enum_p), impl)
                else: # aimpl.rest_p
                    yield structures.HashMap(aimpl.fields, predicates.conjunction(aimpl.rest_p), impl)
                    for load_factor in [0.50, 1.00, 1.50]:
                        yield structures.CozyHashMap(aimpl.fields, aimpl.qvars, predicates.conjunction(aimpl.rest_p), impl, load_factor)
                    if args.enable_hamt:
                        yield structures.Hamt(aimpl.fields, predicates.conjunction(aimpl.rest_p), impl)
        elif type(aimpl) is GuardedImpl:
            for impl in concretize(aimpl.impl):
                yield structures.Guarded(impl, aimpl.fields, aimpl.qvars, aimpl.predicate)
        elif type(aimpl) is Combine:
            for impl1 in concretize(aimpl.l):
                for impl2 in concretize(aimpl.r):
                    yield structures.Tuple(impl1, impl2, aimpl.op)
        elif type(aimpl) is AbstractFilter:
            for impl in concretize(aimpl.t):
                yield structures.Filtered(impl, aimpl.fields, aimpl.qvars, aimpl.predicate)
        else:
            raise Exception("not sure how to concretize {}".format(aimpl))

    for q in queries:
        vars = collections.OrderedDict(q.vars)
        resultTy = Iterable() if q.sort_field is None else SortedIterable(fields, q.sort_field, predicates.Bool(True))
        all_impls = []
        for plan in q.bestPlans:
            all_impls += list(concretize(implement(plan, fields, vars, resultTy)))
        q.all_impls = all_impls
    return _enumerate_impls(fields, queries, 0, [None]*len(queries))

def _enumerate_impls(fields, queries, i, impls):
    if i >= len(queries):
        yield list(impls)
    else:
        for impl in queries[i].all_impls:
            impls[i] = impl
            for result in _enumerate_impls(fields, queries, i+1, impls):
                yield result


class CodeGenerator(object):

    def map_type(self, kt, vt):
        raise NotImplementedError()

    def map_handle_type(self, kt, vt):
        raise NotImplementedError()

    def stack_type(self, t):
        raise NotImplementedError()

    def ref_type(self, ty):
        return ty.gen_type(self)

    def bool_type(self):
        return "boolean";

    def int_type(self):
        return "int";

    def ptr_type(self, t):
        return t.gen_type(self)

    def addr_of(self, x):
        return x

    def deref(self, x):
        return x

    def vector_type(self, ty, n):
        raise NotImplementedError()

    def array_type(self, ty):
        raise NotImplementedError()

    def new_array(self, ty, count):
        raise NotImplementedError()

    def array_get(self, a, n):
        raise NotImplementedError()

    def array_set(self, a, n, v):
        raise NotImplementedError()

    def array_size(self, a):
        raise NotImplementedError()

    def array_copy(self, ty, asrc, adst, src_start=0, dst_start=0, amt=None):
        raise NotImplementedError()

    def data_structure_size(self):
        raise NotImplementedError()

    def alloc(self, ty, args):
        raise NotImplementedError()

    def free(self, ty, x):
        raise NotImplementedError()

    def initialize(self, ty, lval):
        """Make lval into a usable object"""
        return ""

    def min(self, ty, x, y):
        return self.ternary(self.lt(ty, x, y), x, y)

    def max(self, ty, x, y):
        return self.ternary(self.lt(ty, x, y), y, x)

    def new_map(self, kt, vt):
        raise NotImplementedError()

    def map_find_handle(self, m, k, dst):
        raise NotImplementedError()

    def map_handle_exists(self, m, handle):
        raise NotImplementedError()

    def map_read_handle(self, handle):
        raise NotImplementedError()

    def map_write_handle(self, m, handle, k, v):
        raise NotImplementedError()

    def map_put(self, m, k, v):
        raise NotImplementedError()

    def for_each_map_entry(self, m, keyType, valType, body):
        raise NotImplementedError()

    def new_stack(self, t):
        raise NotImplementedError()

    def stack_size_hint(self, stk, n):
        raise NotImplementedError()

    def stack_is_empty(self, stk):
        raise NotImplementedError()

    def stack_push(self, stk, x):
        raise NotImplementedError()

    def stack_pop(self, stk):
        raise NotImplementedError()

    def stack_peek(self, stk):
        raise NotImplementedError()

    def new_vector(self, ty, n):
        raise NotImplementedError()

    def vector_init_elem(self, v, ty, i):
        raise NotImplementedError()

    def vector_get(self, v, i):
        raise NotImplementedError()

    def vector_set(self, v, i, x):
        raise NotImplementedError()

    def native_type(self, t):
        return t

    def record_type(self):
        return "Record"

    def predicate(self, fields, qvars, pred, target, remap=None):
        if remap is None:
            remap = {}
        if type(pred) is predicates.Var:
            return pred.name if pred.name in {v for v,ty in qvars} else remap.get(pred.name, self.get_field(target, pred.name))
        elif type(pred) is predicates.Bool:
            return self.true_value() if pred.val else self.false_value()
        elif type(pred) is predicates.Compare:
            ty = dict(fields + qvars)[pred.lhs.name]
            l = self.predicate(fields, qvars, pred.lhs, target, remap)
            r = self.predicate(fields, qvars, pred.rhs, target, remap)
            if   pred.op == predicates.Eq: return self.eq(ty, l, r)
            elif pred.op == predicates.Ne: return self.ne(ty, l, r)
            elif pred.op == predicates.Lt: return self.lt(ty, l, r)
            elif pred.op == predicates.Le: return self.le(ty, l, r)
            elif pred.op == predicates.Gt: return self.gt(ty, l, r)
            elif pred.op == predicates.Ge: return self.ge(ty, l, r)
        elif type(pred) is predicates.And:
            return self.both(
                self.predicate(fields, qvars, pred.lhs, target, remap),
                self.predicate(fields, qvars, pred.rhs, target, remap))
        elif type(pred) is predicates.Or:
            return self.either(
                self.predicate(fields, qvars, pred.lhs, target, remap),
                self.predicate(fields, qvars, pred.rhs, target, remap))
        elif type(pred) is predicates.Not:
            return self.not_true(self.predicate(fields, qvars, pred.p, target, remap))
        else:
            raise Exception("cannot handle {}".format(pred))

    def not_true(self, e):
        return "!({})".format(e)

    def is_null(self, e):
        return "({}) == {}".format(e, self.null_value())

    def ternary(self, cond, v1, v2):
        return "({}) ? ({}) : ({})".format(cond, v1, v2)

    def same(self, e1, e2):
        return "({}) == ({})".format(e1, e2)

    def eq(self, ty, e1, e2):
        return self.same(e1, e2)

    def ne(self, ty, e1, e2):
        return self.not_true(self.eq(ty, e1, e2))

    def lt(self, ty, e1, e2):
        return "({}) < ({})".format(e1, e2)

    def le(self, ty, e1, e2):
        return "({}) <= ({})".format(e1, e2)

    def gt(self, ty, e1, e2):
        return "({}) > ({})".format(e1, e2)

    def ge(self, ty, e1, e2):
        return "({}) >= ({})".format(e1, e2)

    def to_float(self, ty, e):
        return "(float)({})".format(e)

    def add(self, e1, e2):
        return "({}) + ({})".format(e1, e2)

    def sub(self, e1, e2):
        return "({}) - ({})".format(e1, e2)

    def mul(self, e1, e2):
        return "({}) * ({})".format(e1, e2)

    def div(self, e1, e2):
        return "({}) / ({})".format(e1, e2)

    def mod(self, e1, e2):
        return "({}) % ({})".format(e1, e2)

    def abs(self, e):
        raise NotImplementedError()

    def bit_xor(self, e1, e2):
        return "({}) ^ ({})".format(e1, e2)

    def bit_lshr(self, e1, e2):
        """logical right shift (zero-extend)"""
        return "({}) >>> ({})".format(e1, e2)

    def bit_ashr(self, e1, e2):
        """arithmetic right shift (sign-extend)"""
        return "({}) >> ({})".format(e1, e2)

    def init_new(self, target, ty):
        raise NotImplementedError()

    def null_value(self):
        return "null"

    def true_value(self):
        return "true";

    def false_value(self):
        return "false";

    def get_field(self, e, m):
        if e is None:
            return m
        return "({}).{}".format(e, m)

    def hash(self, values):
        """values is [(type, val)]; returns proc, result"""
        h = fresh_name("hash")
        return (self.decl(h, structures.interface.IntTy(), "0") + self._hash_into(values, h), h)

    def _hash_into(self, values, out):
        proc = ""
        first = True
        for t, v in values:
            if first:
                proc += self.set(out, self.hash1(t, v))
                first = False
            else:
                proc += self.set(out, self.add(self.mul(out, "31"), self.hash1(t, v)))
        return proc

    def hash1(self, ty, value):
        raise NotImplementedError()

    def both(self, e1, e2):
        return "({}) && ({})".format(e1, e2)

    def either(self, e1, e2):
        return "({}) || ({})".format(e1, e2)

    def decl(self, v, ty, e=None):
        if e is not None:
            return "{} {} = {};\n".format(ty.gen_type(self), v, e)
        return "{} {};\n".format(ty.gen_type(self), v)

    def set(self, lval, e):
        return "{} = {};\n".format(lval, e)

    def if_true(self, e):
        return "if ({}) {{\n".format(e)

    def else_if(self, e):
        return "}} else if ({}) {{\n".format(e)

    def else_true(self):
        return "} else {\n"

    def endif(self):
        return "}\n"

    def while_true(self, e):
        return "while ({}) {{\n".format(e)

    def endwhile(self):
        return "}\n"

    def do_while(self):
        return "do {\n"

    def end_do_while(self, e):
        return "}} while ({});\n".format(e)

    def break_loop(self):
        return "break;\n"

    def comment(self, text):
        return " /* {} */ ".format(text)

    def assert_true(self, e):
        return "assert({});\n".format(e)

    def write(self, fields, queries, java_package=None, java_class="DataStructure", java="-", **kwargs):
        raise NotImplementedError()

    def supports_cost_model_file(self, f):
        raise NotImplementedError()

    def dynamic_cost(self, fields, queries, impls, cost_model_file, args):
        raise NotImplementedError()

    def extensions(self, old):
        return old # no extensions
