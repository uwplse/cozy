import itertools
import collections

import plans
import predicates
from common import fresh_name

################################################################################
# Part 1: Type inference

class Ty(object):
    def gen_type(self, gen):
        raise Exception("not implemented for type: {}".format(type(self)))

class NativeTy(Ty):
    def __init__(self, ty):
        self.ty = ty
    def gen_type(self, gen):
        return gen.native_type(self.ty)

class IntTy(Ty):
    def gen_type(self, gen):
        return gen.int_type()

class RefTy(Ty):
    def __init__(self, ty):
        self.ty = ty
    def gen_type(self, gen):
        return gen.ref_type(self.ty)

class BoolTy(Ty):
    def gen_type(self, gen):
        return gen.bool_type()

class VecTy(Ty):
    def __init__(self, ty, count):
        self.ty = ty
        self.count = count
    def gen_type(self, gen):
        return gen.vector_type(self.ty, self.count)

class MapTy(Ty):
    def __init__(self, k, v):
        self.keyTy = k
        self.valTy = v
    def gen_type(self, gen):
        return gen.map_type(self.keyTy, self.valTy)

class RecordType(Ty):
    def gen_type(self, gen):
        return gen.record_type()
    def instance(self, e):
        return This()

class TupleInstance(object):
    def __init__(self, this):
        self.this = this
    def field(self, gen, f):
        return gen.get_field(self.this, f)

class This():
    def field(self, gen, f):
        return f

class TupleTy(Ty):
    def __init__(self, fields):
        self.name = fresh_name("Tuple")
        self.fields = fields
    def gen_type(self, gen):
        if len(self.fields) == 1:
            ty, = self.fields.values()
            return ty.gen_type(gen)
        return gen.native_type(self.name)
    def instance(self, e):
        class I(object):
            def field(_, gen, f):
                assert f in self.fields
                return e if len(self.fields) is 1 else gen.get_field(e, f)
        return I()

class AbstractImpl(object):
    def concretize(self):
        """Generator for ConcreteImpl objects"""
        raise Exception("not implemented for type: {}".format(type(self)))

class Iterable(AbstractImpl):
    def __init__(self, ty):
        self.ty = ty
    def concretize(self):
        yield LinkedList(self.ty)
        # yield Array() # TODO

class SortedIterable(AbstractImpl):
    def __init__(self, fields, sortField, predicate):
        self.fields = fields
        self.sortField = sortField
        self.predicate = predicate
    def concretize(self):
        yield AugTree(NativeTy(self.fields[self.sortField]), self.sortField, self.predicate, self.fields)
        # yield SortedArray(self.field_type, self.field_name) # TODO

def is_enumerable(ty):
    return count_cases(ty) >= 1

def count_cases(ty):
    if ty.lower() in ["bool", "boolean"]:
        return 2
    if ty == "State": # TODO: HACK
        return 8
    return -1

class Bucketed(AbstractImpl):
    def __init__(self, fields, predicate, value_impl):
        self.fields = fields
        self.value_impl = value_impl

        key_fields = list(_make_key_args(fields, predicate).keys())
        self.enum_p = []
        self.rest_p = []
        for cmp in _break_conj(predicate):
            f = cmp.lhs if cmp.lhs.name in fields else cmp.rhs
            if is_enumerable(fields[f.name]):
                self.enum_p.append(cmp)
            else:
                self.rest_p.append(cmp)

    def concretize(self):
        for impl in self.value_impl.concretize():
            if self.enum_p and self.rest_p:
                m = HashMap(self.fields, and_from_list(self.rest_p), impl)
                yield VectorMap(self.fields, and_from_list(self.enum_p), m)
            elif self.enum_p:
                yield VectorMap(self.fields, and_from_list(self.enum_p), impl)
            else: # self.rest_p
                yield HashMap(self.fields, and_from_list(self.rest_p), impl)

class GuardedImpl(AbstractImpl):
    def __init__(self, predicate, fields, qvars, impl):
        self.predicate = predicate
        self.fields = fields
        self.qvars = qvars
        self.impl = impl
    def concretize(self):
        for impl in self.impl.concretize():
            yield Guarded(impl, self.fields, self.qvars, self.predicate)

class Combine(AbstractImpl):
    def __init__(self, l, r, op):
        self.l = l
        self.r = r
        self.op = op
    def concretize(self):
        for impl1 in self.l.concretize():
            for impl2 in self.r.concretize():
                yield Tuple(impl1, impl2, self.op)

class AbstractFilter(AbstractImpl):
    def __init__(self, t, fields, qvars, predicate):
        self.t = t
        self.fields = fields
        self.qvars = qvars
        self.predicate = predicate
    def concretize(self):
        for impl in self.t.concretize():
            yield Filtered(impl, self.fields, self.qvars, self.predicate)

def implement(plan, fields, qvars, resultTy):
    """
    Args:
        plan           - plans.Plan to implement
        fields         - dict { field_name : type }
        qvars          - dict { var_name   : type }
        resultTy       - an AbstractImpl
    Returns:
        an AbstractImpl
    """

    if type(plan) is plans.AllWhere:
        if plan.predicate == predicates.Bool(True):
            return resultTy
        else:
            return GuardedImpl(plan.predicate, fields, qvars, resultTy)
    elif type(plan) is plans.HashLookup:
        t = Bucketed(fields, plan.predicate, resultTy)
        return implement(plan.plan, fields, qvars, t)
    elif type(plan) is plans.BinarySearch:
        assert type(resultTy) in [Iterable, SortedIterable]
        return implement(plan.plan, fields, qvars, SortedIterable(fields, plan.sortField, plan.predicate))
    elif type(plan) is plans.Intersect:
        t1 = implement(plan.plan1, fields, qvars, resultTy)
        t2 = implement(plan.plan2, fields, qvars, resultTy)
        return Combine(t1, t2, INTERSECT_OP)
    elif type(plan) is plans.Union:
        t1 = implement(plan.plan1, fields, qvars, resultTy)
        t2 = implement(plan.plan2, fields, qvars, resultTy)
        return Combine(t1, t2, UNION_OP)
    elif type(plan) is plans.Concat:
        t1 = implement(plan.plan1, fields, qvars, resultTy)
        t2 = implement(plan.plan2, fields, qvars, resultTy)
        return Combine(t1, t2, CONCAT_OP)
    elif type(plan) is plans.Filter:
        t = implement(plan.plan, fields, qvars, resultTy)
        return AbstractFilter(t, fields, qvars, plan.predicate)
    else:
        raise Exception("codegen not implemented for {}".format(type(plan)))

################################################################################
# Part 2: Implementation

class ConcreteImpl(object):
    def is_sorted_by(self, field):
        raise Exception("not implemented for type: {}".format(type(self)))
    def fields(self):
        """returns list of (name, ty)"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def construct(self, gen):
        """returns proc"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def needs_var(self, var):
        """returns True or False"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def state(self):
        """returns list of (name, ty)"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def private_members(self, gen, parent_structure=This()):
        """returns list of (name, ty, init)"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def gen_query(self, gen, qvars):
        """returns (proc, stateExps)"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def gen_empty(self, gen, qvars):
        """returns stateExps"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def gen_current(self, gen):
        """returns (proc, result)"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def gen_advance(self, gen):
        """returns proc"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def gen_next(self, gen):
        """returns (proc, result)"""
        proc, cur = self.gen_current(gen)
        oldcursor = fresh_name()
        proc += gen.decl(oldcursor, RecordType(), cur)
        proc += self.gen_advance(gen)
        return proc, oldcursor
    def gen_has_next(self, gen):
        """returns (proc, result)"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def gen_insert(self, gen, x):
        """returns proc"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def gen_remove(self, gen, x):
        """returns proc"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def gen_remove_in_place(self, gen, parent_structure):
        """returns proc, removed element"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def gen_update(self, gen, fields, f, x, v):
        """returns proc"""
        raise Exception("not implemented for type: {}".format(type(self)))
    def auxtypes(self):
        """generator of auxiliary types which need to be generated"""
        raise Exception("not implemented for type: {}".format(type(self)))

class HashMap(ConcreteImpl):
    def __init__(self, fields, predicate, valueImpl):
        self.name = fresh_name("map")
        self.valueTy = self._make_value_type(valueImpl)
        self.keyArgs = _make_key_args(fields, predicate)
        self.keyTy = _make_key_type(fields, self.keyArgs)
        self.valueImpl = valueImpl
    def _make_value_type(self, valueImpl):
        return TupleTy(collections.OrderedDict(valueImpl.fields()))
    def fields(self):
        return ((self.name, MapTy(self.keyTy, self.valueTy)),)
    def construct(self, gen, parent_structure=This()):
        name = parent_structure.field(gen, self.name)
        return gen.set(name, gen.new_map(self.keyTy, self.valueTy))
    def needs_var(self, v):
        return self.valueImpl.needs_var(v)
    def state(self):
        return self.valueImpl.state()
    def private_members(self, gen, parent_structure=This()):
        return self.valueImpl.private_members(gen, parent_structure)
    def make_key(self, gen, target):
        for f in self.keyArgs:
            assert len(self.keyArgs[f]) == 1, "cannot (yet) handle multiple values in lookup ({})".format(self.keyArgs)
        if len(self.keyTy.fields) == 1:
            return gen.set(target, self.keyArgs[list(self.keyTy.fields.keys())[0]][0])
        s = gen.init_new(target, self.keyTy)
        for f, v in self.keyTy.fields.items():
            s += gen.set(gen.get_field(target, f), self.keyArgs[f][0])
        return s
    def lookup(self, gen, m, k):
        """returns proc, handle"""
        handle = fresh_name("maphandle")
        proc  = gen.decl(handle, NativeTy(gen.map_handle_type(self.keyTy, self.valueTy)))
        proc += gen.map_find_handle(m, k, handle)
        return proc, handle
    def handle_exists(self, gen, m, handle):
        return gen.map_handle_exists(m, handle)
    def read_handle(self, gen, m, handle):
        return gen.map_read_handle(handle)
    def write_handle(self, gen, m, handle, k, v):
        return gen.map_write_handle(m, handle, k, v)
    def put(self, gen, m, k, v):
        return gen.map_put(m, k, v)
    def make_key_of_record(self, gen, x, target, remap=None):
        if remap is None:
            remap = dict()
        def fv(f):
            return remap.get(f) or gen.get_field(x, f)
        if len(self.keyTy.fields) == 1:
            return gen.set(target, fv(list(self.keyTy.fields.keys())[0]))
        s = gen.init_new(target, self.keyTy)
        for f, v in self.keyTy.fields.items():
            s += gen.set(gen.get_field(target, f), fv(f))
        return s
    def gen_query(self, gen, qvars, parent_structure=This()):
        name = parent_structure.field(gen, self.name)
        vs = collections.OrderedDict()
        proc = ""
        for f,t in self.state():
            n = fresh_name(f)
            vs[f] = n
            proc += gen.decl(n, t)
        k = fresh_name()
        proc += gen.decl(k, self.keyTy)
        proc += self.make_key(gen, k)
        p, handle = self.lookup(gen, name, k)
        proc += p
        proc += gen.if_true(self.handle_exists(gen, name, handle))
        sub = fresh_name("substructure")
        proc += gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, name, handle))
        p, r = self.valueImpl.gen_query(gen, qvars, self.valueTy.instance(sub))
        proc += p
        for lhs, rhs in zip(vs.values(), r):
            proc += gen.set(lhs, rhs)
        proc += gen.else_true()
        r = self.valueImpl.gen_empty(gen, self.valueTy.instance(sub))
        for lhs, rhs in zip(vs.values(), r):
            proc += gen.set(lhs, rhs)
        proc += gen.endif()
        return (proc, list(vs.values()))
    def gen_empty(self, gen, qvars):
        return self.valueImpl.gen_empty(gen, qvars)
    def gen_current(self, gen):
        return self.valueImpl.gen_current(gen)
    def gen_advance(self, gen):
        return self.valueImpl.gen_advance(gen)
    def gen_next(self, gen):
        return self.valueImpl.gen_next(gen)
    def gen_has_next(self, gen):
        return self.valueImpl.gen_has_next(gen)
    def create_substructure_at_key(self, gen, m, k):
        name = fresh_name()
        proc  = gen.decl(name, self.valueTy)
        proc += self.valueImpl.construct(gen, parent_structure=self.valueTy.instance(name))
        proc += gen.map_put(m, k, name)
        return proc
    def gen_insert(self, gen, x, parent_structure=This(), k=None):
        name = parent_structure.field(gen, self.name)
        proc = ""
        if k is None:
            k = fresh_name("key")
            proc += gen.decl(k, self.keyTy)
            proc += self.make_key_of_record(gen, x, k)
        p, handle = self.lookup(gen, name, k)
        proc += p
        proc += gen.if_true(gen.not_true(self.handle_exists(gen, name, handle)))
        proc += self.create_substructure_at_key(gen, name, k)
        p, handle2 = self.lookup(gen, name, k)
        proc += p
        proc += gen.set(handle, handle2)
        proc += gen.endif()

        sub = fresh_name("substructure")
        proc += gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, name, handle))
        proc += self.valueImpl.gen_insert(gen, x, self.valueTy.instance(sub))
        proc += self.write_handle(gen, name, handle, k, sub)
        return proc
    def gen_remove(self, gen, x, parent_structure=This(), k=None):
        name = parent_structure.field(gen, self.name)
        proc = ""
        if k is None:
            k = fresh_name("key")
            proc += gen.decl(k, self.keyTy)
            proc += self.make_key_of_record(gen, x, k)

        p, handle = self.lookup(gen, name, k)
        proc += p
        proc += gen.if_true(self.handle_exists(gen, name, handle))
        sub = fresh_name("substructure")
        proc += gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, name, handle))
        proc += self.valueImpl.gen_remove(gen, x, self.valueTy.instance(sub))
        proc += self.write_handle(gen, name, handle, k, sub)
        proc += gen.endif()
        return proc
    def gen_remove_in_place(self, gen, parent_structure=This()):
        name = parent_structure.field(gen, self.name)
        k = fresh_name("key")
        proc, x = self.valueImpl.gen_current(gen)
        proc += gen.decl(k, self.keyTy)
        proc += self.make_key_of_record(gen, x, k)
        p, handle = self.lookup(gen, name, k)
        proc += p
        sub = fresh_name("substructure")
        proc += gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, name, handle))
        p, removed = self.valueImpl.gen_remove_in_place(gen, parent_structure=self.valueTy.instance(sub))
        proc += p
        proc += self.write_handle(gen, name, handle, k, sub)
        return removed
    def gen_update(self, gen, fields, f, x, v, parent_structure=This()):
        name = parent_structure.field(gen, self.name)
        affects_key = f in self.keyArgs
        k1 = fresh_name("oldkey")
        proc  = gen.decl(k1, self.keyTy)
        proc += self.make_key_of_record(gen, x, k1)
        if affects_key:
            # remove from old loc
            proc += self.gen_remove(gen, x, parent_structure=parent_structure, k=k1)

            # add to new loc
            k2 = fresh_name("newkey")
            proc += gen.decl(k2, self.keyTy)
            proc += self.make_key_of_record(gen, x, k2, remap={f:v})
            proc += self.gen_insert(gen, x, parent_structure=parent_structure, k=k2)
        else:
            p, handle = self.lookup(gen, name, k1)
            proc += p
            sub = fresh_name("substructure")
            proc += gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, name, handle))
            subproc = self.valueImpl.gen_update(gen, fields, f, x, v, parent_structure=self.valueTy.instance(sub))
            if subproc:
                proc += subproc
                proc += self.write_handle(gen, name, handle, k1, sub)
            else:
                proc = ""
        return proc
    def auxtypes(self):
        yield self.keyTy
        yield self.valueTy
        for t in self.valueImpl.auxtypes():
            yield t

class VectorMap(HashMap):
    def __init__(self, fields, predicate, valueImpl):
        super(VectorMap, self).__init__(fields, predicate, valueImpl)
        self.field_types = fields
        self.key_fields = list(self.keyArgs.keys())
        self.enum_counts = { f:count_cases(fields[f]) for f in self.key_fields }
        self.count = 1
        for f in self.key_fields:
            self.count *= self.enum_counts[f]
        self.keyTy = IntTy()
    def construct(self, gen, parent_structure=This()):
        name = parent_structure.field(gen, self.name)
        proc = gen.set(name, gen.new_vector(self.valueTy, self.count))
        for i in xrange(self.count):
            proc += self.valueImpl.construct(gen, self.valueTy.instance(gen.vector_get(name, i)))
        return proc
    def lookup(self, gen, m, k):
        """returns proc, handle"""
        return "", k
    def put(self, gen, m, k, v):
        return gen.vector_set(m, k, v)
    def handle_exists(self, gen, m, handle):
        return gen.true_value()
    def read_handle(self, gen, m, handle):
        return gen.vector_get(m, handle)
    def write_handle(self, gen, m, handle, k, v):
        return gen.vector_set(m, handle, v)
    def fields(self):
        return ((self.name, VecTy(self.valueTy, self.count)),)
    def enum_to_int(self, gen, v, t):
        return gen.ternary(v, "1", "0") if t.lower() in ["bool", "boolean"] else "(int){}".format(v) # TODO: HACK
    def create_substructure_at_key(self, gen, m, k):
        return ""
    def make_key(self, gen, target):
        for f in self.keyArgs:
            assert len(self.keyArgs[f]) == 1, "cannot (yet) handle multiple values in lookup ({})".format(self.keyArgs)
        proc = gen.set(target, "0")
        for f in self.key_fields:
            proc += gen.set(target, gen.mul(target, self.enum_counts[f]))
            proc += gen.set(target, gen.add(target, self.enum_to_int(gen, self.keyArgs[f][0], self.field_types[f])))
        return proc
    def make_key_of_record(self, gen, x, target, remap=None):
        if remap is None:
            remap = dict()
        def fv(f):
            return remap.get(f) or gen.get_field(x, f)
        proc = gen.set(target, "0")
        for f in self.key_fields:
            proc += gen.set(target, gen.mul(target, self.enum_counts[f]))
            proc += gen.set(target, gen.add(target, self.enum_to_int(gen, fv(f), self.field_types[f])))
        return proc

def _make_key_args(fields, predicate):
    """returns an OrderedDict mapping field->[var]"""
    d = collections.OrderedDict()
    for f, v in predicate.comparisons():
        if f not in fields:
            f, v = v, f
        if f in d:
            d[f].append(v)
        else:
            d[f] = [v]
    return d

def _make_key_type(fields, key_fields):
    return TupleTy(collections.OrderedDict((k, NativeTy(fields[k])) for k in key_fields))

AUG_MIN = "min"
AUG_MAX = "max"

INCLUSIVE = "inclusive"
EXCLUSIVE = "exclusive"

def _break_conj(p):
    if type(p) is predicates.And:
        return itertools.chain(_break_conj(p.lhs), _break_conj(p.rhs))
    elif type(p) is predicates.Bool and p.val:
        return ()
    else:
        return (p,)

def and_from_list(ps):
    p = ps[0]
    i = 1
    while i < len(ps):
        p = predicates.And(p, ps[i])
        i += 1
    return p

AugData = collections.namedtuple("AugData", [
    "type", "real_field", "orig_field", "qvar", "mode", "inclusive"])

def _make_augdata(field_name, predicate, fields):
    """returns a generator of (field_name, var_name, min/max, inclusive)"""
    comparisons = list(_break_conj(predicate))
    for c in comparisons:
        if c.rhs.name in fields:
            c = c.flip()
        f = c.lhs.name
        v = c.rhs.name
        t = NativeTy(fields[f])
        if f == field_name:
            continue
        if   c.op == predicates.Lt: yield AugData(t, fresh_name(), f, v, AUG_MAX, False)
        elif c.op == predicates.Le: yield AugData(t, fresh_name(), f, v, AUG_MAX, True)
        elif c.op == predicates.Gt: yield AugData(t, fresh_name(), f, v, AUG_MIN, False)
        elif c.op == predicates.Ge: yield AugData(t, fresh_name(), f, v, AUG_MIN, True)

class AugTree(ConcreteImpl):
    def __init__(self, fieldTy, fieldName, predicate, fields):
        self.name = fresh_name("root")
        self.fieldTy = fieldTy
        self.fieldName = fieldName
        self.ty = RecordType()
        self.predicate = predicate
        self._fields = fields
        clauses = list(_break_conj(predicate))

        # put field names on LHS of clauses
        for i in xrange(len(clauses)):
            if clauses[i].rhs.name in fields:
                clauses[i] = clauses[i].flip()

        self.mins = []
        self.maxes = []
        for c in clauses:
            if c.lhs.name == fieldName:
                if   c.op == predicates.Gt: self.mins.append((EXCLUSIVE, c.rhs))
                elif c.op == predicates.Ge: self.mins.append((INCLUSIVE, c.rhs))
                elif c.op == predicates.Lt: self.maxes.append((EXCLUSIVE, c.rhs))
                elif c.op == predicates.Le: self.maxes.append((INCLUSIVE, c.rhs))

        self.augData = list(_make_augdata(fieldName, predicate, fields)) if predicate else ()

        self.prev_cursor_name = fresh_name("prev_cursor")
        self.cursor_name = fresh_name("cursor")
        self.left_ptr = fresh_name("left")
        self.right_ptr = fresh_name("right")
        self.parent_ptr = fresh_name("parent")
    def fields(self):
        return [(self.name, self.ty)]
    def construct(self, gen, parent_structure=This()):
        name = parent_structure.field(gen, self.name)
        return gen.set(name, gen.null_value())
    def needs_var(self, v):
        return v in (x.name for x in self.predicate.vars())
    def state(self):
        return [(self.prev_cursor_name, self.ty), (self.cursor_name, self.ty)]
    def gen_empty(self, gen, qvars):
        return [gen.null_value()]
    def private_members(self, gen, parent_structure=This()):
        return [
            (self.left_ptr,   RecordType(), gen.null_value()),
            (self.right_ptr,  RecordType(), gen.null_value()),
            (self.parent_ptr, RecordType(), gen.null_value())] + [
                (ad.real_field, ad.type, parent_structure.field(gen, ad.orig_field)) for ad in self.augData]
    def _too_small(self, gen, node, clip=True):
        if not clip:
            return gen.false_value()
        e = gen.false_value()
        for (mode, bound) in self.mins:
            compare = gen.le if mode == EXCLUSIVE else gen.lt
            ee = compare(self.fieldTy, gen.get_field(node, self.fieldName), bound.name)
            e = gen.either(e, ee)
        return e
    def _too_large(self, gen, node, clip=True):
        if not clip:
            return gen.false_value()
        e = gen.false_value()
        for (mode, bound) in self.maxes:
            compare = gen.le if mode == EXCLUSIVE else gen.lt
            ee = compare(self.fieldTy, bound.name, gen.get_field(node, self.fieldName))
            e = gen.either(e, ee)
        return e
    def _subtree_ok(self, gen, root, clip=True):
        """could ANY node in the subtree be valid? only checks augdata."""
        if not clip:
            return gen.true_value()
        return gen.true_value()
    def _node_ok(self, gen, node, clip=True):
        """Does this subnode agree with the augdata?"""
        if not clip:
            return gen.true_value()
        e = gen.true_value()
        for aug in self.augData:
            if aug.mode == AUG_MIN and     aug.inclusive: op = gen.ge
            if aug.mode == AUG_MIN and not aug.inclusive: op = gen.gt
            if aug.mode == AUG_MAX and     aug.inclusive: op = gen.le
            if aug.mode == AUG_MAX and not aug.inclusive: op = gen.lt
            e = gen.both(e,
                op(aug.type, gen.get_field(node, aug.real_field), aug.qvar))
        return e
    def _has_parent(self, gen, node):
        return gen.not_true(gen.is_null(gen.get_field(node, self.parent_ptr)))
    def _is_left_child(self, gen, node):
        return gen.both(self._has_parent(gen, node), gen.same(node, gen.get_field(gen.get_field(node, self.parent_ptr), self.left_ptr)))
    def _is_right_child(self, gen, node):
        return gen.both(self._has_parent(gen, node), gen.same(node, gen.get_field(gen.get_field(node, self.parent_ptr), self.right_ptr)))
    def _find_min(self, gen, root, clip=True):
        """precond: _subtree_ok(root)"""
        root2 = fresh_name("root")
        proc  = gen.decl(root2, self.ty, root)
        root = root2

        x = fresh_name("x")
        proc += gen.decl(x, self.ty, root)

        # recursive alg:
        # if x is too small
        #     if x has right child: return _find_min(right)
        #     else return NULL
        # else if has left child
        #     n <- _find_min(left)
        #     if n is not NULL: return n
        #     else return x too large ? NULL : x
        # else if x is too large, return NULL
        # else return x

        # linearization:
        # mode = DESCEND
        # while True
        # if mode == DESCEND
        #     if x is too small:
        #         if x has right child:
        #             if x is root: root = right
        #             x = right
        #         else if x is not root: x = parent; mode = ASCEND // too small, no right child, not the root... back out!
        #         else: return NULL // x too small, no right child... no answer!
        #     else if x has left child:
        #         x = left
        #     else if x is too large:
        #         if x is not root: x = parent; mode = ASCEND // no left child, x too big: back out!
        #         else: return NULL; // x is root, is too large, and has no left
        #     else if _node_ok(x): return x; // x is not too small or large, and has no left child
        #     else if x is root: x = root = right; // if there is an answer, it lies to the right
        #     else: x = parent; mode = ASCEND
        # else if mode == ASCEND_FROM_LEFT
        #     // x is not too small, or we would be in ASCEND_FROM_RIGHT
        #     // there is no answer in X.left
        #     if x is too large:
        #         return NULL; // if our parent was smaller and ok, it would have returned itself!
        #     else:
        #         // x is not too large but there is no answer in left tree
        #         if _node_ok(x): return x // got it!
        #         else if x has right child:
        #             if x is root: root = right
        #             x = right; mode = DESCEND
        #         else if x is root: return NULL // it isn't X, it isn't in X.left, it isn't in X.right
        #         else: x = x.parent; mode = ASCEND // it isn't X, it isn't in X.left, it isn't in X.right
        # else if mode == ASCEND_FROM_RIGHT:
        #     // no answer is left subtree, x is not answer, no answer in right subtree
        #     if x is root: return NULL // x is not ok, or we would have returned it
        #     else: x = x.parent; mode = ASCEND // no answer in this subtree

        descend = fresh_name("descend")
        from_left = fresh_name("from_left")
        bool_type = NativeTy(gen.bool_type())
        proc += gen.decl(descend, bool_type, gen.true_value())
        proc += gen.decl(from_left, bool_type, gen.true_value())

        parent = gen.get_field(x, self.parent_ptr)
        right  = gen.get_field(x, self.right_ptr)
        left   = gen.get_field(x, self.left_ptr)
        null   = gen.null_value()

        ascend = (
            gen.set(descend, gen.false_value()) +
            gen.set(from_left, self._is_left_child(gen, x)) +
            gen.set(x, parent))

        return_null = (
            gen.set(x, null) +
            gen.break_loop())

        return_x = gen.break_loop()

        descend_right = (
            gen.if_true(gen.same(x, root)) +
            gen.set(root, right) +
            gen.endif() +
            gen.set(x, right))

        proc += gen.while_true(gen.true_value())

        proc += gen.if_true(gen.is_null(x))
        proc += return_null
        proc += gen.endif()

        proc += gen.if_true(descend) # descending

        proc += gen.comment("too small?")
        proc += gen.if_true(self._too_small(gen, x, clip))
        proc += gen.if_true(self._has_right(gen, x, clip))
        proc += descend_right
        proc += gen.else_if(gen.same(x, root))
        proc += return_null
        proc += gen.else_true()
        proc += ascend
        proc += gen.endif()
        proc += gen.else_if(self._has_left(gen, x, clip))
        proc += gen.set(x, left)
        proc += gen.comment("too large?")
        proc += gen.else_if(self._too_large(gen, x, clip))
        proc += gen.if_true(gen.same(x, root))
        proc += return_null
        proc += gen.else_true()
        proc += ascend
        proc += gen.endif()
        proc += gen.comment("node ok?")
        proc += gen.else_if(self._node_ok(gen, x, clip))
        proc += return_x
        proc += gen.else_if(gen.same(x, root))
        proc += gen.set(root, right) + gen.set(x, right) # descend_right
        proc += gen.else_true()
        proc += ascend
        proc += gen.endif()

        proc += gen.else_if(from_left) # ascending from left

        proc += gen.if_true(self._too_large(gen, x, clip))
        proc += return_null
        proc += gen.else_if(self._node_ok(gen, x, clip))
        proc += return_x
        proc += gen.else_if(self._has_right(gen, x, clip))
        proc += gen.set(descend, gen.true_value())
        proc += descend_right
        proc += gen.else_if(gen.same(x, root))
        proc += return_null
        proc += gen.else_true()
        proc += ascend
        proc += gen.endif()

        proc += gen.else_true() # ascending from right

        proc += gen.if_true(gen.same(x, root))
        proc += return_null
        proc += gen.else_true()
        proc += ascend
        proc += gen.endif()

        proc += gen.endif()

        proc += gen.endwhile()
        return proc, x

    def _has_left(self, gen, node, clip=True):
        return gen.both(
            gen.not_true(gen.is_null(gen.get_field(node, self.left_ptr))),
            self._subtree_ok(gen, gen.get_field(node, self.left_ptr), clip))
    def _has_right(self, gen, node, clip=True):
        return gen.both(
            gen.not_true(gen.is_null(gen.get_field(node, self.right_ptr))),
            self._subtree_ok(gen, gen.get_field(node, self.right_ptr), clip))
    def gen_query(self, gen, qvars, this=This()):
        p, m = self._find_min(gen, this.field(gen, self.name))
        return p, [gen.null_value(), m]
    def gen_current(self, gen):
        return "", self.cursor_name
    def gen_advance(self, gen, target=None):
        proc = gen.comment("ADVANCE")
        if target is None:
            target = self.cursor_name
        else:
            proc += gen.set(target, self.cursor_name)

        descend = fresh_name("descend") # are we allowed to descend?
        right_min = fresh_name("right_min")

        proc += gen.decl(descend, NativeTy(gen.bool_type()), gen.true_value())
        proc += gen.do_while()

        # successor of any node with a right child is the min node to the right
        proc += gen.decl(right_min, self.ty, gen.null_value())
        proc += gen.if_true(gen.both(descend, self._has_right(gen, target)))
        p, m = self._find_min(gen, gen.get_field(target, self.right_ptr))
        proc += p
        proc += gen.set(right_min, m)
        proc += gen.endif()

        proc += gen.if_true(gen.not_true(gen.is_null(right_min)))
        proc += gen.set(target, right_min)
        proc += gen.break_loop()

        # If there is no matching node to the right, then successor is
        # elsewhere in the tree.
        proc += gen.else_true()

        # Ascend until we get to a left child (or root)
        proc += gen.while_true(self._is_right_child(gen, target))
        proc += gen.set(target, gen.get_field(target, self.parent_ptr))
        proc += gen.endwhile()

        # Parent of this node *might* be successor, if all the augdata matches.
        proc += gen.set(target, gen.get_field(target, self.parent_ptr))

        proc += gen.endif()

        proc += gen.end_do_while(gen.both(
            gen.not_true(gen.is_null(target)),
            gen.not_true(self._node_ok(gen, target))))

        return proc
    def gen_next(self, gen):
        oldcursor = fresh_name()
        proc  = gen.decl(oldcursor, RecordType(), self.cursor_name)
        proc += self.gen_advance(gen)
        proc += gen.set(self.prev_cursor_name, oldcursor)
        return proc, oldcursor
    def gen_has_next(self, gen):
        return "", gen.not_true(gen.is_null(self.cursor_name))
    def gen_insert(self, gen, x, parent_structure=This(), indexval=None):
        if indexval is None:
            indexval = gen.get_field(x, self.fieldName)

        name = parent_structure.field(gen, self.name)

        prev = fresh_name("previous")
        curr = fresh_name("current")
        is_left = fresh_name("is_left")

        proc  = gen.decl(prev, self.ty, gen.null_value())
        proc += gen.decl(curr, self.ty, name)
        proc += gen.decl(is_left, NativeTy(gen.bool_type()), gen.false_value())

        # find insertion point
        proc += gen.while_true(gen.not_true(gen.is_null(curr)))
        proc += gen.set(prev, curr)
        proc += gen.if_true(gen.lt(self.fieldTy, indexval, gen.get_field(curr, self.fieldName)))
        proc += gen.set(curr, gen.get_field(curr, self.left_ptr))
        proc += gen.set(is_left, gen.true_value())
        proc += gen.else_true()
        proc += gen.set(curr, gen.get_field(curr, self.right_ptr))
        proc += gen.set(is_left, gen.false_value())
        proc += gen.endif()
        proc += gen.endwhile()

        # insert
        proc += gen.if_true(gen.is_null(prev))
        proc += gen.set(name, x)
        proc += gen.else_true()
        proc += gen.set(gen.get_field(x, self.parent_ptr), prev)
        proc += gen.if_true(is_left)
        proc += gen.set(gen.get_field(prev, self.left_ptr), x)
        proc += gen.else_true()
        proc += gen.set(gen.get_field(prev, self.right_ptr), x)
        proc += gen.endif()
        proc += gen.endif()

        return proc
    def replace_node_in_parent(self, gen, parent, old_node, new_node):
        # parent.[L|R] = new_node
        proc  = gen.comment("replace {} with {} in {}".format(old_node, new_node, parent))
        proc += gen.if_true(gen.not_true(gen.is_null(parent)))
        proc += gen.if_true(gen.same(gen.get_field(parent, self.left_ptr), old_node))
        proc += gen.set(gen.get_field(parent, self.left_ptr), new_node)
        proc += gen.else_true()
        proc += gen.set(gen.get_field(parent, self.right_ptr), new_node)
        proc += gen.endif()
        proc += gen.endif()
        # new_node.parent = parent
        proc += gen.if_true(gen.not_true(gen.is_null(new_node)))
        proc += gen.set(gen.get_field(new_node, self.parent_ptr), parent)
        proc += gen.endif()
        return proc
    def gen_remove(self, gen, x, parent_structure=This()):
        root = parent_structure.field(gen, self.name)

        p = fresh_name("parent")
        l = fresh_name("left")
        r = fresh_name("right")
        proc  = gen.decl(p, self.ty, gen.get_field(x, self.parent_ptr))
        proc += gen.decl(l, self.ty, gen.get_field(x, self.left_ptr))
        proc += gen.decl(r, self.ty, gen.get_field(x, self.right_ptr))

        new_x = fresh_name("new_x")
        proc += gen.decl(new_x, self.ty)

        # case1: no children
        proc += gen.if_true(gen.both(
            gen.is_null(l),
            gen.is_null(r)))

        proc += gen.set(new_x, gen.null_value())
        proc += self.replace_node_in_parent(gen, p, x, new_x)

        # case2: only has left child
        proc += gen.else_if(gen.both(
            gen.not_true(gen.is_null(l)),
            gen.is_null(r)))

        proc += gen.set(new_x, l)
        proc += self.replace_node_in_parent(gen, p, x, new_x)

        # case3: only has right child
        proc += gen.else_if(gen.both(
            gen.is_null(l),
            gen.not_true(gen.is_null(r))))

        proc += gen.set(new_x, r)
        proc += self.replace_node_in_parent(gen, p, x, new_x)

        # case4: two children
        proc += gen.else_true()
        find_min, m = self._find_min(gen, gen.get_field(x, self.right_ptr), clip=False) # m = smallest node greater than x
        proc += find_min
        proc += gen.set(new_x, m)

        # capture m's pointers
        mp = fresh_name("mp")
        proc += gen.decl(mp, self.ty, gen.get_field(m, self.parent_ptr))
        ml = gen.null_value() # NOTE: m.L is always null!
        mr = fresh_name("mr")
        proc += gen.decl(mr, self.ty, gen.get_field(m, self.right_ptr))

        # remove m
        # NOTE: if x.R == m, this modifies x.R! Be careful not to mention "r" below here.
        proc += self.replace_node_in_parent(gen, mp, m, mr)

        # put m in x's place
        proc += self.replace_node_in_parent(gen, p, x, m)
        proc += self.replace_node_in_parent(gen, m, ml, l)
        proc += self.replace_node_in_parent(gen, m, mr, gen.get_field(x, self.right_ptr))

        # x is root?
        proc += gen.if_true(gen.same(root, x))
        proc += gen.set(root, m)
        proc += gen.endif()

        proc += gen.endif()

        # x is root?
        proc += gen.if_true(gen.same(root, x))
        proc += gen.set(root, new_x)
        proc += gen.endif()

        # TODO: recompute augdata. :(

        return proc
    def gen_remove_in_place(self, gen, parent_structure):
        to_remove = fresh_name("to_remove")
        proc  = gen.decl(to_remove, self.ty, self.prev_cursor_name)
        proc += self.gen_remove(gen, to_remove, parent_structure=parent_structure)
        proc += gen.set(self.prev_cursor_name, gen.null_value())
        return proc, to_remove
    def gen_update(self, gen, fields, f, x, v, parent_structure=This()):
        if f == self.fieldName:
            proc  = self.gen_remove(gen, x, parent_structure=parent_structure)
            proc += self.gen_insert(gen, x, parent_structure=parent_structure, indexval=v)
        elif any(aug.orig_field == f for aug in self.augData):
            proc = gen.comment("TODO: AugTree aug update\n")
        else:
            proc = ""
        return proc
    def auxtypes(self):
        return ()

class LinkedList(ConcreteImpl):
    def __init__(self, ty):
        self.name = self.head_ptr = fresh_name("head")
        self.next_ptr = fresh_name("next")
        self.prev_ptr = fresh_name("prev")
        self.prev_cursor_name = fresh_name("prev_cursor")
        self.cursor_name = fresh_name("cursor")
        self.ty = RecordType()
    def fields(self):
        return ((self.head_ptr, self.ty),)
    def construct(self, gen, parent_structure=This()):
        return gen.set(parent_structure.field(gen, self.head_ptr), gen.null_value())
    def needs_var(self, v):
        return False
    def state(self):
        return [
            (self.prev_cursor_name, self.ty),
            (self.cursor_name, self.ty)]
    def private_members(self, gen, parent_structure=This()):
        return [
            (self.next_ptr, self.ty, gen.null_value()),
            (self.prev_ptr, self.ty, gen.null_value())]
    def gen_query(self, gen, qvars):
        return "", [gen.null_value(), self.head_ptr]
    def gen_empty(self, gen, qvars):
        return [gen.null_value(), gen.null_value()]
    def gen_advance(self, gen):
        proc  = gen.set(self.prev_cursor_name, self.cursor_name)
        proc += gen.set(self.cursor_name, gen.get_field(self.cursor_name, self.next_ptr))
        return proc
    def gen_current(self, gen):
        return "", self.cursor_name
    def gen_has_next(self, gen):
        return "", gen.not_true(gen.is_null(self.cursor_name))
    def gen_next(self, gen):
        proc = self.gen_advance(gen)
        return proc, self.prev_cursor_name
    def gen_query(self, gen, qvars, this=This()):
        return "", [gen.null_value(), this.field(gen, self.head_ptr)]
    def gen_insert(self, gen, x, parent_structure=This()):
        name = parent_structure.field(gen, self.head_ptr)
        proc  = gen.set(gen.get_field(x, self.prev_ptr), gen.null_value())
        proc += gen.set(gen.get_field(x, self.next_ptr), name)

        proc += gen.if_true(gen.not_true(gen.is_null(name)))
        proc += gen.set(gen.get_field(name, self.prev_ptr), x)
        proc += gen.endif()

        proc += gen.set(name, x)
        return proc
    def gen_remove(self, gen, x, parent_structure=This()):
        head = parent_structure.field(gen, self.head_ptr)

        proc  = gen.if_true(gen.same(x, head))
        proc += gen.set(head, gen.get_field(x, self.next_ptr))
        proc += gen.endif()

        proc += gen.if_true(gen.not_true(gen.is_null(gen.get_field(x, self.next_ptr))))
        proc += gen.set(
            gen.get_field(gen.get_field(x, self.next_ptr), self.prev_ptr),
            gen.get_field(x, self.prev_ptr))
        proc += gen.endif()

        proc += gen.if_true(gen.not_true(gen.is_null(gen.get_field(x, self.prev_ptr))))
        proc += gen.set(
            gen.get_field(gen.get_field(x, self.prev_ptr), self.next_ptr),
            gen.get_field(x, self.next_ptr))
        proc += gen.endif()

        proc += gen.set(gen.get_field(x, self.prev_ptr), gen.null_value())
        proc += gen.set(gen.get_field(x, self.next_ptr), gen.null_value())
        return proc
    def gen_remove_in_place(self, gen, parent_structure):
        old_prev = fresh_name("old_prev")
        proc  = gen.decl(old_prev, self.ty, self.prev_cursor_name)
        proc += self.gen_remove(gen, self.prev_cursor_name, parent_structure=parent_structure)
        proc += gen.set(self.prev_cursor_name, gen.null_value())
        return proc, old_prev
    def gen_update(self, gen, fields, f, x, v, parent_structure=This()):
        return ""
    def auxtypes(self):
        return ()

class Guarded(ConcreteImpl):
    def __init__(self, ty, fields, qvars, predicate):
        self.ty = ty
        self._fields = fields
        self.qvars = qvars
        self.predicate = predicate
    def fields(self):
        return self.ty.fields()
    def construct(self, gen):
        return self.ty.construct(gen)
    def needs_var(self, v):
        return self.ty.needs_var(v)
    def state(self):
        return self.ty.state()
    def private_members(self, gen, parent_structure=This()):
        return self.ty.private_members(gen, parent_structure)
    def gen_query(self, gen, qvars):
        return self.ty.gen_query(gen, qvars)
    def gen_current(self, gen):
        return self.ty.gen_current(gen)
    def gen_next(self, gen):
        return self.ty.gen_next(gen)
    def gen_has_next(self, gen):
        return self.ty.gen_has_next(gen)
    def gen_insert(self, gen, x):
        proc = self.ty.gen_insert(gen, x)
        return gen.if_true(gen.predicate(list(self._fields.items()), list(self.qvars.items()), self.predicate, x)) + proc + gen.endif()
    def gen_remove(self, gen, x, parent_structure=This()):
        proc = self.ty.gen_remove(gen, x)
        return gen.if_true(gen.predicate(list(self._fields.items()), list(self.qvars.items()), self.predicate, x)) + proc + gen.endif()
    def gen_remove_in_place(self, gen, parent_structure):
        return self.ty.gen_remove_in_place(gen, parent_structure)
    def auxtypes(self):
        return self.ty.auxtypes()

class Filtered(ConcreteImpl):
    def __init__(self, ty, fields, qvars, predicate):
        self.ty = ty
        self._fields = fields
        self.qvars = qvars
        self.predicate = predicate
    def fields(self):
        return self.ty.fields()
    def construct(self, gen):
        return self.ty.construct(gen)
    def needs_var(self, v):
        return self.ty.needs_var(v) or any(vv.name == v for vv in self.predicate.vars() if vv.name in self.qvars)
    def state(self):
        return self.ty.state()
    def private_members(self, gen, parent_structure=This()):
        return self.ty.private_members(gen, parent_structure)
    def gen_query(self, gen, qvars):
        proc, es = self.ty.gen_query(gen, qvars)
        for (v, t), e in itertools.izip(self.ty.state(), es):
            proc += gen.decl(v, t, e)
        proc += gen.while_true(gen.true_value())
        p1, hn = self.ty.gen_has_next(gen)
        proc += p1
        proc += gen.if_true(gen.not_true(hn))
        proc += gen.break_loop()
        proc += gen.endif()
        p2, cur = self.ty.gen_current(gen)
        proc += p2
        curN = fresh_name("current")
        proc += gen.decl(curN, RecordType(), cur)
        proc += gen.if_true(gen.predicate(list(self._fields.items()), list(self.qvars.items()), self.predicate, curN))
        proc += gen.break_loop()
        proc += gen.endif()
        proc += self.ty.gen_advance(gen)
        proc += gen.endwhile()
        return proc, [v for (v, t) in self.ty.state()]
    def gen_current(self, gen):
        return self.ty.gen_current(gen)
    def gen_advance(self, gen):
        proc  = gen.do_while()
        p1, hn = self.ty.gen_has_next(gen)
        proc += p1
        proc += gen.if_true(gen.not_true(hn))
        proc += gen.break_loop()
        proc += gen.endif()
        p2, n = self.ty.gen_next(gen)
        proc += p2
        proc += gen.if_true(gen.predicate(list(self._fields.items()), list(self.qvars.items()), self.predicate, n))
        proc += gen.break_loop()
        proc += gen.endif()
        proc += gen.end_do_while(gen.true_value())
        return proc
    def gen_has_next(self, gen):
        return self.ty.gen_has_next(gen)
    def gen_insert(self, gen, x):
        return self.ty.gen_insert(gen, x)
    def gen_remove(self, gen, x, parent_structure=This()):
        return self.ty.gen_remove(gen, x)
    def gen_remove_in_place(self, gen, parent_structure):
        return self.ty.gen_remove_in_place(gen, parent_structure)
    def auxtypes(self):
        return self.ty.auxtypes()

INTERSECT_OP = "intersect"
UNION_OP     = "union"
CONCAT_OP    = "concat"

class Tuple(ConcreteImpl):
    def __init__(self, ty1, ty2, op):
        self.ty1 = ty1
        self.ty2 = ty2
        self.op = op
    def fields(self):
        return self.ty1.fields() + self.ty2.fields()
    def construct(self, gen):
        return self.ty1.construct(gen) + self.ty2.construct(gen)
    def needs_var(self, v):
        return self.ty1.needs_var(v) or self.ty2.needs_var(v)
    def state(self):
        return self.ty1.state() + self.ty2.state()
    def private_members(self, gen, parent_structure=This()):
        return self.ty1.private_members(gen, parent_structure) + self.ty2.private_members(gen, parent_structure)
    def gen_query(self, gen, qvars):
        if self.op == CONCAT_OP:
            proc1, es1 = self.ty1.gen_query(gen, qvars)
            proc2, es2 = self.ty2.gen_query(gen, qvars)
            return (proc1 + proc2, es1 + es2)
        else:
            raise Exception("unknown op {}".format(self.op))
    def gen_current(self, gen):
        if self.op == CONCAT_OP:
            proc1, r1 = self.ty1.gen_has_next(gen)
            r = fresh_name()
            proc  = gen.decl(r, RecordType())
            proc += proc1
            proc += gen.if_true(r1)
            next1, r1 = self.ty1.gen_current(gen)
            proc += next1
            proc += gen.set(r, r1)
            proc += gen.else_true()
            next2, r2 = self.ty2.gen_current(gen)
            proc += next2
            proc += gen.set(r, r2)
            proc += gen.endif()
            return proc, r
        else:
            raise Exception("unknown op {}".format(self.op))
    def gen_next(self, gen):
        if self.op == CONCAT_OP:
            proc1, r1 = self.ty1.gen_has_next(gen)
            r = fresh_name()
            proc  = gen.decl(r, RecordType())
            proc += proc1
            proc += gen.if_true(r1)
            next1, r1 = self.ty1.gen_next(gen)
            proc += next1
            proc += gen.set(r, r1)
            proc += gen.else_true()
            next2, r2 = self.ty2.gen_next(gen)
            proc += next2
            proc += gen.set(r, r2)
            proc += gen.endif()
            return proc, r
        else:
            raise Exception("unknown op {}".format(self.op))
    def gen_has_next(self, gen):
        if self.op == CONCAT_OP:
            proc1, r1 = self.ty1.gen_has_next(gen)
            proc2, r2 = self.ty2.gen_has_next(gen)
            r = fresh_name()
            proc  = proc1
            proc += gen.decl(r, NativeTy(gen.bool_type()), r1)
            proc += gen.if_true(gen.not_true(r))
            proc += proc2
            proc += gen.set(r, r2)
            proc += gen.endif()
            return proc, r
        else:
            raise Exception("unknown op {}".format(self.op))
    def gen_insert(self, gen, x):
        if self.op == CONCAT_OP:
            return self.ty1.gen_insert(gen, x) + self.ty2.gen_insert(gen, x)
        else:
            raise Exception("unknown op {}".format(self.op))
    def gen_remove(self, gen, x):
        if self.op == CONCAT_OP:
            return self.ty1.gen_remove(gen, x) + self.ty2.gen_remove(gen, x)
        else:
            raise Exception("unknown op {}".format(self.op))
    def gen_update(self, gen, fields, f, x, v):
        proc  = self.ty1.gen_update(gen, fields, f, x, v)
        proc += self.ty2.gen_update(gen, fields, f, x, v)
        return proc
    def auxtypes(self):
        for t in self.ty1.auxtypes(): yield t
        for t in self.ty2.auxtypes(): yield t

def enumerate_impls(fields, queries):
    """
    Code generation entry point.
      fields    - list of (field_name, type)
      queries   - list of queries.Query objects with .bestPlans set
    Sets q.all_impls for each q in queries
    Returns an iterator of [ConcreteImpl] (one entry per query)
    """
    for q in queries:
        vars = collections.OrderedDict(q.vars)
        resultTy = Iterable(RecordType()) if q.sort_field is None else SortedIterable(fields, q.sort_field, predicates.Bool(True))
        all_impls = []
        for plan in q.bestPlans:
            all_impls += list(implement(plan, fields, vars, resultTy).concretize())
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
