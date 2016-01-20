from .interface import ConcreteImpl

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
    def private_members(self):
        return self.ty.private_members()
    def gen_query(self, gen, qvars):
        return self.ty.gen_query(gen, qvars)
    def gen_current(self, gen):
        return self.ty.gen_current(gen)
    def gen_advance(self, gen):
        return self.ty.gen_advance(gen)
    def gen_next(self, gen):
        return self.ty.gen_next(gen)
    def gen_has_next(self, gen):
        return self.ty.gen_has_next(gen)
    def gen_insert(self, gen, x):
        proc = self.ty.gen_insert(gen, x)
        return gen.if_true(gen.predicate(list(self._fields.items()), list(self.qvars.items()), self.predicate, x)) + proc + gen.endif()
    def gen_remove(self, gen, x, parent_structure):
        proc = self.ty.gen_remove(gen, x)
        return gen.if_true(gen.predicate(list(self._fields.items()), list(self.qvars.items()), self.predicate, x)) + proc + gen.endif()
    def gen_remove_in_place(self, gen, parent_structure):
        return self.ty.gen_remove_in_place(gen, parent_structure)
    def auxtypes(self):
        return self.ty.auxtypes()
