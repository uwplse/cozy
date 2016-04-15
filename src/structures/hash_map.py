import collections

from .interface import ConcreteImpl, TupleTy, NativeTy, MapTy, MapHandleType, RefTy, RecordType, BoolTy
from common import fresh_name

def make_key_args(fields, predicate):
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

def make_key_type(fields, key_fields):
    return TupleTy(collections.OrderedDict((k, NativeTy(fields[k])) for k in key_fields))

class HashMap(ConcreteImpl):
    def __init__(self, fields, predicate, valueImpl):
        self.name = fresh_name("map")
        self.valueTy = self._make_value_type(valueImpl)
        self.keyArgs = make_key_args(fields, predicate)
        self.keyTy = make_key_type(fields, self.keyArgs) # value in the Tuple
        self.iterator_key_name = fresh_name("key")
        self.iterator_handle_name = fresh_name("handle")
        self.valueImpl = valueImpl # LinkedList, usually
    def __str__(self):
        return "HashMap({})".format(self.valueImpl)
    def __repr__(self):
        return self.__str__()
    def handle_type(self):
        return MapHandleType(self.keyTy, self.valueTy)
    def _make_value_type(self, valueImpl):
        return TupleTy(collections.OrderedDict(valueImpl.fields()))
    def fields(self):
        return ((self.name, MapTy(self.keyTy, self.valueTy)),)
    def construct(self, gen, parent_structure):
        name = parent_structure.field(gen, self.name)
        return gen.set(name, gen.new_map(self.keyTy, self.valueTy))
    def needs_var(self, v):
        return self.valueImpl.needs_var(v)
    def state(self):
        return list(self.valueImpl.state()) + [
            (self.iterator_key_name, self.keyTy),
            (self.iterator_handle_name, self.handle_type())]
    def private_members(self):
        return self.valueImpl.private_members() # private memebers in Record class(e.g. next, prev)
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
        proc  = gen.decl(handle, self.handle_type())
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
    def gen_query(self, gen, qvars, parent_structure):
        name = parent_structure.field(gen, self.name)
        vs = collections.OrderedDict()
        proc = ""
        for f,t in self.valueImpl.state():
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
        return (proc, list(vs.values()) + [k, handle])
    def gen_query_one(self, gen, qvars, parent_structure):
        name = parent_structure.field(gen, self.name)
        vs = collections.OrderedDict()
        proc = ""
        k = fresh_name()
        proc += gen.decl(k, self.keyTy)
        proc += self.make_key(gen, k)
        p, handle = self.lookup(gen, name, k)
        proc += p
        result = fresh_name("result")
        proc += gen.decl(result, RecordType())
        proc += gen.if_true(self.handle_exists(gen, name, handle))
        sub = fresh_name("substructure")
        proc += gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, name, handle))
        p, r = self.valueImpl.gen_query_one(gen, qvars, self.valueTy.instance(sub))
        proc += p
        proc += gen.set(result, r)
        proc += gen.else_true()
        proc += gen.set(result, gen.null_value())
        proc += gen.endif()
        return (proc, result)
    def gen_find_any(self, gen, parent_structure):
        name = parent_structure.field(gen, self.name)
        valueImpl = self.valueImpl
        result = fresh_name("result")
        proc  = gen.decl(result, RecordType(), gen.null_value())
        def f(handle, val, break_loop):
            p, r = valueImpl.gen_find_any(gen, val)
            p += gen.set(result, r)
            p += gen.if_true(gen.not_true(gen.is_null(result)))
            p += break_loop()
            p += gen.endif()
            return p
        proc += gen.for_each_map_entry(name, self.keyTy, self.valueTy, f)
        return (proc, result)
    def gen_empty(self, gen, qvars):
        return self.valueImpl.gen_empty(gen, qvars)
    def iterator_current_substructure(self, gen, parent_structure, iterator):
        m = parent_structure.field(gen, self.name)
        handle = iterator.field(gen, self.iterator_handle_name)
        sub = fresh_name("substructure")
        proc = gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, m, handle))
        return proc, sub
    def gen_current(self, gen, parent_structure, iterator):
        p1, sub = self.iterator_current_substructure(gen, parent_structure, iterator)
        p2, n = self.valueImpl.gen_current(gen, self.valueTy.instance(sub), iterator)
        return p1 + p2, n
    def gen_advance(self, gen, parent_structure, iterator):
        p1, sub = self.iterator_current_substructure(gen, parent_structure, iterator)
        p2 = self.valueImpl.gen_advance(gen, self.valueTy.instance(sub), iterator)
        return p1 + p2
    def gen_next(self, gen, parent_structure, iterator):
        p1, sub = self.iterator_current_substructure(gen, parent_structure, iterator)
        p2, n = self.valueImpl.gen_next(gen, self.valueTy.instance(sub), iterator)
        return p1 + p2, n
    def gen_has_next(self, gen, parent_structure, iterator):
        p1, sub = self.iterator_current_substructure(gen, parent_structure, iterator)
        result = fresh_name()
        proc  = gen.decl(result, BoolTy())
        proc += p1
        proc += gen.if_true(gen.is_null(sub))
        proc += gen.set(result, gen.false_value())
        proc += gen.else_true()
        p2, n = self.valueImpl.gen_has_next(gen, self.valueTy.instance(sub), iterator)
        proc += p2
        proc += gen.set(result, n)
        proc += gen.endif()
        return proc, result
    def create_substructure_at_key(self, gen, m, k):
        name = fresh_name()
        proc  = gen.decl(name, self.valueTy)
        proc += gen.initialize(self.valueTy, name)
        proc += self.valueImpl.construct(gen, parent_structure=self.valueTy.instance(name))
        proc += gen.map_put(m, k, name)
        return proc
    def gen_insert_at_key(self, gen, x, parent_structure, k):
        name = parent_structure.field(gen, self.name)
        proc, handle = self.lookup(gen, name, k)
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
    def gen_insert(self, gen, x, parent_structure):
        name = parent_structure.field(gen, self.name)
        proc = ""
        k = fresh_name("key")
        proc += gen.decl(k, self.keyTy)
        proc += self.make_key_of_record(gen, x, k)
        proc += self.gen_insert_at_key(gen, x, parent_structure, k)
        return proc
    def gen_remove_at_key(self, gen, x, parent_structure, k=None):
        name = parent_structure.field(gen, self.name)
        proc, handle = self.lookup(gen, name, k)
        proc += gen.if_true(self.handle_exists(gen, name, handle))
        sub = fresh_name("substructure")
        proc += gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, name, handle))
        proc += self.valueImpl.gen_remove(gen, x, self.valueTy.instance(sub))
        proc += self.write_handle(gen, name, handle, k, sub)
        proc += gen.endif()
        return proc
    def gen_remove(self, gen, x, parent_structure):
        name = parent_structure.field(gen, self.name)
        proc = ""
        k = fresh_name("key")
        proc += gen.decl(k, self.keyTy)
        proc += self.make_key_of_record(gen, x, k)
        proc += self.gen_remove_at_key(gen, x, parent_structure, k)
        return proc
    def gen_remove_in_place(self, gen, parent_structure, iterator):
        name = parent_structure.field(gen, self.name)
        sub = fresh_name("substructure")
        proc  = gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, name, iterator.field(gen, self.iterator_handle_name)))
        p, removed = self.valueImpl.gen_remove_in_place(gen, parent_structure=self.valueTy.instance(sub), iterator=iterator)
        proc += p
        proc += self.write_handle(gen, name, iterator.field(gen, self.iterator_handle_name), iterator.field(gen, self.iterator_key_name), sub)
        return proc, removed
    def gen_update(self, gen, fields, x, remap, parent_structure):
        name = parent_structure.field(gen, self.name)
        affects_key = any(f in self.keyArgs for f in remap)
        k1 = fresh_name("oldkey")
        proc  = gen.decl(k1, self.keyTy)
        proc += self.make_key_of_record(gen, x, k1)
        if affects_key:
            # remove from old loc
            proc += self.gen_remove_at_key(gen, x, parent_structure=parent_structure, k=k1)

            # add to new loc
            k2 = fresh_name("newkey")
            proc += gen.decl(k2, self.keyTy)
            proc += self.make_key_of_record(gen, x, k2, remap=remap)
            proc += self.gen_insert_at_key(gen, x, parent_structure=parent_structure, k=k2)
        else:
            p, handle = self.lookup(gen, name, k1)
            proc += p
            sub = fresh_name("substructure")
            proc += gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, name, handle))
            subproc = self.valueImpl.gen_update(gen, fields, x, remap, parent_structure=self.valueTy.instance(sub))
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
