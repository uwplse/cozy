from .interface import ConcreteImpl
from common import fresh_name

class Filtered(ConcreteImpl):
    def __init__(self, ty, fields, qvars, predicate):
        self.ty = ty
        self._fields = fields
        self.qvars = qvars
        self.predicate = predicate
    def fields(self):
        return self.ty.fields()
    def construct(self, gen, parent_structure):
        return self.ty.construct(gen, parent_structure)
    def needs_var(self, v):
        return self.ty.needs_var(v) or any(vv.name == v for vv in self.predicate.vars() if vv.name in self.qvars)
    def state(self):
        return self.ty.state()
    def private_members(self):
        return self.ty.private_members()
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
    def gen_remove(self, gen, x, parent_structure):
        return self.ty.gen_remove(gen, x)
    def gen_remove_in_place(self, gen, parent_structure):
        return self.ty.gen_remove_in_place(gen, parent_structure)
    def auxtypes(self):
        return self.ty.auxtypes()
