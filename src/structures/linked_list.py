from .interface import ConcreteImpl, RecordType
from common import fresh_name

class LinkedList(ConcreteImpl):
    def __init__(self):
        self.name = self.head_ptr = fresh_name("head")
        self.next_ptr = fresh_name("next")
        self.prev_ptr = fresh_name("prev")
        self.prev_cursor_name = fresh_name("prev_cursor")
        self.cursor_name = fresh_name("cursor")
        self.ty = RecordType()
    def __str__(self):
        return "LinkedList"
    def __repr__(self):
        return self.__str__()
    def fields(self):
        return ((self.head_ptr, self.ty),)
    def construct(self, gen, parent_structure):
        return gen.set(parent_structure.field(gen, self.head_ptr), gen.null_value())
    def needs_var(self, v):
        return False
    def state(self):
        return [
            (self.prev_cursor_name, self.ty),
            (self.cursor_name, self.ty)]
    def private_members(self):
        return [
            (self.next_ptr, self.ty),
            (self.prev_ptr, self.ty)]
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
    def gen_query(self, gen, qvars, this):
        return "", [gen.null_value(), this.field(gen, self.head_ptr)]
    def gen_insert(self, gen, x, parent_structure):
        name = parent_structure.field(gen, self.head_ptr)
        proc  = gen.set(gen.get_field(x, self.prev_ptr), gen.null_value())
        proc += gen.set(gen.get_field(x, self.next_ptr), name)

        proc += gen.if_true(gen.not_true(gen.is_null(name)))
        proc += gen.set(gen.get_field(name, self.prev_ptr), x)
        proc += gen.endif()

        proc += gen.set(name, x)
        return proc
    def gen_remove(self, gen, x, parent_structure):
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
    def gen_update(self, gen, fields, x, remap, parent_structure):
        return ""
    def auxtypes(self):
        return ()
