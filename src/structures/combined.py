from .interface import ConcreteImpl, BoolTy, RecordType
from common import fresh_name

INTERSECT_OP = "intersect"
UNION_OP     = "union"
CONCAT_OP    = "concat"

class Tuple(ConcreteImpl):
    def __init__(self, ty1, ty2, op):
        self.ty1 = ty1
        self.ty2 = ty2
        self.prev1 = fresh_name("prev1")
        self.op = op
    def __str__(self):
        return "({}, {})".format(self.ty1, self.ty2)
    def __repr__(self):
        return self.__str__()
    def fields(self):
        return self.ty1.fields() + self.ty2.fields()
    def construct(self, gen, parent_structure):
        return self.ty1.construct(gen, parent_structure) + self.ty2.construct(gen, parent_structure)
    def needs_var(self, v):
        return self.ty1.needs_var(v) or self.ty2.needs_var(v)
    def state(self):
        return self.ty1.state() + self.ty2.state() + [(self.prev1, BoolTy())]
    def private_members(self):
        return self.ty1.private_members() + self.ty2.private_members()
    def gen_query(self, gen, qvars, parent_structure):
        if self.op == CONCAT_OP:
            proc1, es1 = self.ty1.gen_query(gen, qvars, parent_structure)
            proc2, es2 = self.ty2.gen_query(gen, qvars, parent_structure)
            return (proc1 + proc2, es1 + es2 + [gen.true_value()])
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
            proc += gen.set(self.prev1, gen.false_value())
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
            proc += gen.decl(r, BoolTy(), r1)
            proc += gen.if_true(gen.not_true(r))
            proc += proc2
            proc += gen.set(r, r2)
            proc += gen.endif()
            return proc, r
        else:
            raise Exception("unknown op {}".format(self.op))
    def gen_insert(self, gen, x, parent_structure):
        if self.op == CONCAT_OP:
            return self.ty1.gen_insert(gen, x, parent_structure) + self.ty2.gen_insert(gen, x, parent_structure)
        else:
            raise Exception("unknown op {}".format(self.op))
    def gen_remove_in_place(self, gen, parent_structure):
        removed = fresh_name("removed")
        proc  = gen.decl(removed, RecordType())
        proc += gen.if_true(self.prev1)
        p, ret = self.ty1.gen_remove_in_place(gen, parent_structure)
        proc += p
        proc += gen.set(removed, ret)
        proc += gen.else_true()
        p, ret = self.ty2.gen_remove_in_place(gen, parent_structure)
        proc += p
        proc += gen.set(removed, ret)
        proc += gen.endif()
        return proc, removed
    def gen_remove(self, gen, x, parent_structure):
        if self.op == CONCAT_OP:
            return self.ty1.gen_remove(gen, x, parent_structure) + self.ty2.gen_remove(gen, x, parent_structure)
        else:
            raise Exception("unknown op {}".format(self.op))
    def gen_update(self, gen, fields, x, remap, parent_structure):
        proc  = self.ty1.gen_update(gen, fields, x, remap, parent_structure)
        proc += self.ty2.gen_update(gen, fields, x, remap, parent_structure)
        return proc
    def auxtypes(self):
        for t in self.ty1.auxtypes(): yield t
        for t in self.ty2.auxtypes(): yield t
