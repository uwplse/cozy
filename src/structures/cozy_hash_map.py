from .interface import IntTy, FloatTy, ArrayTy, NativeTy, RecordType
from .hash_map import HashMap
from .filtered import Filtered
from common import fresh_name

INIT_SIZE = 10

class CozyHashMap(HashMap):
    def __init__(self, fields, qvars, predicate, valueImpl, load_factor):
        super(CozyHashMap, self).__init__(fields, predicate, Filtered(valueImpl, fields, qvars, predicate))
        self.field_types = fields
        self.load_factor = load_factor
        self.keyTy = IntTy()
    def __str__(self):
        return "CozyMap[lf={}]({})".format(self.load_factor, self.valueImpl)
    def handle_type(self):
        return IntTy()
    def construct(self, gen, parent_structure):
        name = parent_structure.field(gen, self.name)
        i = fresh_name("i")
        proc  = gen.set(name, gen.new_array(self.valueTy, str(INIT_SIZE)))
        proc += gen.decl(i, IntTy(), "0")
        proc += gen.while_true(gen.lt(IntTy(), i, gen.array_size(name)))
        proc += gen.initialize(self.valueTy, gen.array_get(name, i))
        proc += self.valueImpl.construct(gen, self.valueTy.instance(gen.array_get(name, i)))
        proc += gen.set(i, gen.add(i, 1))
        proc += gen.endwhile()
        return proc
    def lookup(self, gen, m, k):
        """returns proc, handle"""
        return "", k
    def put(self, gen, m, k, v):
        return gen.array_set(m, k, v)
    def handle_exists(self, gen, m, handle):
        return gen.true_value()
    def read_handle(self, gen, m, handle):
        return gen.array_get(m, gen.mod(handle, gen.array_size(m)))
    def write_handle(self, gen, m, handle, k, v):
        return gen.array_set(m, gen.mod(handle, gen.array_size(m)), v)
    def fields(self):
        return ((self.name, ArrayTy(self.valueTy)),)
    def state(self):
        return list(self.valueImpl.state()) + [(self.iterator_handle_name, IntTy())]
    def make_key_of_record(self, gen, x, target, remap=None):
        if remap is None:
            remap = dict()
        def fv(f):
            return remap.get(f) or gen.get_field(x, f)
        proc, h = gen.hash([(NativeTy(self.field_types[f]), fv(f)) for f in self.keyArgs])
        proc += gen.set(target, h)
        return proc
    # def enum_to_int(self, gen, v, t):
    #     return gen.ternary(v, "1", "0") if t.lower() in ["bool", "boolean"] else "(int){}".format(v) # TODO: HACK
    def create_substructure_at_key(self, gen, m, k):
        return ""
    def make_key(self, gen, target):
        for f in self.keyArgs:
            assert len(self.keyArgs[f]) == 1, "cannot (yet) handle multiple values in lookup ({})".format(self.keyArgs)
        proc, h = gen.hash([(NativeTy(self.field_types[f]), f) for f in self.keyArgs])
        proc += gen.set(target, h)
        return proc
    def current_load(self, gen, parent_structure):
        size = gen.data_structure_size()
        a = parent_structure.field(gen, self.name)
        return gen.div(gen.to_float(IntTy(), size), gen.to_float(IntTy(), gen.array_size(a)))
    def gen_insert_no_autobalance(self, gen, x, parent_structure):
        return super(CozyHashMap, self).gen_insert(gen, x, parent_structure)
    def gen_insert(self, gen, x, parent_structure):
        name = parent_structure.field(gen, self.name)
        newa = fresh_name("newarray")
        proc  = gen.if_true(gen.gt(FloatTy(), self.current_load(gen, parent_structure), self.load_factor))
        proc += gen.decl(newa, ArrayTy(self.valueTy), gen.new_array(self.valueTy, gen.mul(gen.array_size(name), "2")))

        class FakeParent(object):
            def field(self, gen, f):
                return newa

        i = fresh_name("i")
        proc += gen.decl(i, IntTy(), "0")

        proc += gen.while_true(gen.lt(IntTy(), i, gen.array_size(newa)))
        proc += gen.initialize(self.valueTy, gen.array_get(newa, i))
        proc += self.valueImpl.construct(gen, self.valueTy.instance(gen.array_get(newa, i)))
        proc += gen.set(i, gen.add(i, 1))
        proc += gen.endwhile()

        proc += gen.set(i, "0")
        proc += gen.while_true(gen.lt(IntTy(), i, gen.array_size(name)))
        sub = fresh_name("substructure")
        proc += gen.decl(sub, self.valueTy, gen.array_get(name, i))
        proc += gen.while_true(gen.true_value())
        p, y = self.valueImpl.gen_find_any(gen, self.valueTy.instance(sub))
        proc += p
        saved = fresh_name("record")
        proc += gen.decl(saved, RecordType(), y)
        proc += gen.if_true(gen.is_null(saved))
        proc += gen.break_loop()
        proc += gen.endif()
        proc += self.valueImpl.gen_remove(gen, saved, self.valueTy.instance(sub))
        proc += self.gen_insert_no_autobalance(gen, saved, FakeParent())
        proc += gen.endwhile()
        proc += gen.set(i, gen.add(i, 1))
        proc += gen.endwhile()

        proc += gen.free(ArrayTy(self.valueTy), name)
        proc += gen.set(name, newa)
        proc += gen.endif()
        proc += self.gen_insert_no_autobalance(gen, x, parent_structure)
        return proc
    def gen_query(self, gen, qvars, parent_structure):
        name = parent_structure.field(gen, self.name)
        p, h = gen.hash([(NativeTy(self.field_types[k]), v) for (k,(v,)) in self.keyArgs.items()])
        proc  = p
        sub = fresh_name("substructure")
        proc += gen.decl(sub, self.valueTy, gen.array_get(name, gen.mod(h, gen.array_size(name))))
        p, vs = self.valueImpl.gen_query(gen, qvars, self.valueTy.instance(sub))
        proc += p
        return (proc, list(vs) + [h])
    def gen_query_one(self, gen, qvars, parent_structure):
        name = parent_structure.field(gen, self.name)
        p, h = gen.hash([(NativeTy(self.field_types[k]), v) for (k,(v,)) in self.keyArgs.items()])
        proc  = p
        sub = fresh_name("substructure")
        proc += gen.decl(sub, self.valueTy, gen.array_get(name, gen.mod(h, gen.array_size(name))))
        p, r = self.valueImpl.gen_query_one(gen, qvars, self.valueTy.instance(sub))
        proc += p
        return (proc, r)
    def auxtypes(self):
        yield self.valueTy
        for t in self.valueImpl.auxtypes():
            yield t
