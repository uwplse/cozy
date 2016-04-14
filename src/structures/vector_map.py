from .interface import IntTy, VecTy
from .hash_map import HashMap
from common import fresh_name

def is_enumerable(ty):
    return count_cases(ty) >= 1

def count_cases(ty):
    if ty.lower() in ["bool", "boolean"]:
        return 2
    if ty == "State": # TODO: HACK
        return 8
    return -1

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
    def __str__(self):
        return "VectorMap[{}]({})".format(self.count, self.valueImpl)
    def handle_type(self):
        return IntTy()
    def construct(self, gen, parent_structure):
        name = parent_structure.field(gen, self.name)
        proc  = gen.set(name, gen.new_vector(self.valueTy, self.count))
        i = fresh_name("i")
        proc += gen.decl(i, IntTy(), "0")
        proc += gen.while_true(gen.lt(IntTy(), i, self.count))
        proc += gen.vector_init_elem(name, self.valueTy, i)
        proc += self.valueImpl.construct(gen, self.valueTy.instance(gen.vector_get(name, i)))
        proc += gen.set(i, gen.add(i, 1))
        proc += gen.endwhile()
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
    def auxtypes(self):
        yield self.valueTy
        for t in self.valueImpl.auxtypes():
            yield t
