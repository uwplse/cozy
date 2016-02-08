from .interface import ConcreteImpl, BoolTy, NativeTy
from common import fresh_name

class Guarded(ConcreteImpl):
    def __init__(self, ty, fields, qvars, predicate):
        self.ty = ty
        self._fields = { f : NativeTy(t) for f, t in fields }
        self.qvars = qvars
        self.predicate = predicate
    def fields(self):
        return self.ty.fields()
    def construct(self, gen, parent_structure):
        return self.ty.construct(gen, parent_structure)
    def needs_var(self, v):
        return self.ty.needs_var(v)
    def state(self):
        return self.ty.state()
    def private_members(self):
        return self.ty.private_members()
    def gen_query(self, gen, qvars, parent_structure):
        return self.ty.gen_query(gen, qvars, parent_structure)
    def gen_query_one(self, gen, qvars, parent_structure):
        return self.ty.gen_query_one(gen, qvars, parent_structure)
    def gen_empty(self, gen, qvars):
        return self.ty.gen_empty(gen, qvars)
    def gen_find_any(self, gen, parent_structure):
        return self.ty.gen_find_any(gen, parent_structure)
    def gen_current(self, gen):
        return self.ty.gen_current(gen)
    def gen_advance(self, gen):
        return self.ty.gen_advance(gen)
    def belongs(self, gen, x, remap=None):
        return gen.predicate(list(self._fields.items()), [], self.predicate, x, remap=remap)
    def gen_update(self, gen, fields, x, remap, parent_structure):
        currently_in = fresh_name("currently_in")
        belongs_in = fresh_name("belongs_in")
        proc  = gen.decl(currently_in, BoolTy(), self.belongs(gen, x))
        proc += gen.decl(belongs_in, BoolTy(), self.belongs(gen, x, remap))
        proc += gen.if_true(gen.both(currently_in, belongs_in))
        proc += self.ty.gen_update(gen, fields, x, remap, parent_structure)
        proc += gen.else_if(gen.both(currently_in, gen.not_true(belongs_in)))
        proc += self.ty.gen_remove(gen, x, parent_structure)
        proc += gen.else_if(gen.both(gen.not_true(currently_in), belongs_in))
        proc += self.ty.gen_insert(gen, x, parent_structure)
        proc += gen.endif()
        return proc
    def gen_next(self, gen):
        return self.ty.gen_next(gen)
    def gen_has_next(self, gen):
        return self.ty.gen_has_next(gen)
    def gen_insert(self, gen, x, parent_structure):
        proc = self.ty.gen_insert(gen, x, parent_structure)
        return gen.if_true(self.belongs(gen, x)) + proc + gen.endif()
    def gen_remove(self, gen, x, parent_structure):
        proc = self.ty.gen_remove(gen, x, parent_structure)
        return gen.if_true(self.belongs(gen, x)) + proc + gen.endif()
    def gen_remove_in_place(self, gen, parent_structure):
        return self.ty.gen_remove_in_place(gen, parent_structure)
    def auxtypes(self):
        return self.ty.auxtypes()
