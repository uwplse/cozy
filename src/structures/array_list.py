from .interface import ConcreteImpl, ArrayTy, RecordType, IntTy, PointerTy
from common import fresh_name

INIT_CAPACITY = 8

class ArrayList(ConcreteImpl):
    """
    Common interface for generated data structures
    """

    def __str__(self):
        return "ArrayList"
    def __repr__(self):
        return self.__str__()

    def __init__(self):
        # Data structure
        self.length = fresh_name("length")
        self.array = fresh_name("array")

        # Iterator
        self.idx = fresh_name("index")

    def fields(self):
        return [(self.array, ArrayTy(RecordType())), (self.length, IntTy())]
    def construct(self, gen, parent_structure):
        proc  = gen.set(parent_structure.field(gen, self.length), 0)
        proc += gen.set(parent_structure.field(gen, self.array), gen.new_array(RecordType(), INIT_CAPACITY))
        return proc
    def needs_var(self, var):
        return False
    def state(self):
        return [(self.idx, IntTy())]
    def private_members(self):
        return []
    def gen_query(self, gen, qvars, parent_structure):
        return "", [0]
    def gen_query_one(self, gen, qvars, parent_structure):
        return "", gen.ternary(
            gen.same(parent_structure.field(gen, self.length), 0),
            gen.null_value(),
            gen.array_get(parent_structure.field(gen, self.array), 0))
    def gen_empty(self, gen, qvars):
        return [0] # TODO: this is wrong!
    def gen_find_any(self, gen, parent_structure):
        return self.gen_query_one(gen, [], parent_structure)
    def gen_current(self, gen, parent_structure, iterator):
        return "", "{}[{}]".format(gen.deref(parent_structure.field(gen, self.array)), iterator.field(gen, self.idx))
    def gen_advance(self, gen, parent_structure, iterator):
        return gen.set(iterator.field(gen, self.idx), gen.add(iterator.field(gen, self.idx), 1))
    def gen_has_next(self, gen, parent_structure, iterator):
        return "", gen.lt(IntTy(), iterator.field(gen, self.idx), parent_structure.field(gen, self.length))
    def gen_insert(self, gen, x, parent_structure):
        # if length == array.length:
        #    array = realloc(array, array.length*2)
        # array[length] = x
        # ++length
        array = parent_structure.field(gen, self.array)
        length = parent_structure.field(gen, self.length)

        proc  = gen.if_true(gen.same(length, gen.array_size(array)))
        a2 = fresh_name("new_array")
        proc += gen.decl(a2, ArrayTy(RecordType()), gen.new_array(RecordType(), gen.mul(length, 2)))
        proc += gen.array_copy(RecordType(), asrc=array, adst=a2)
        proc += gen.free(ArrayTy(RecordType()), array)
        proc += gen.set(array, a2)
        proc += gen.endif()

        proc += gen.array_set(array, length, x)
        proc += gen.set(length, gen.add(length, 1))
        return proc
    def index_of(self, gen, x, parent_structure):
        idx = fresh_name("index")
        array = parent_structure.field(gen, self.array)
        length = parent_structure.field(gen, self.length)
        proc  = gen.decl(idx, IntTy(), 0)
        proc += gen.while_true(gen.lt(IntTy(), idx, length))
        proc += gen.if_true(gen.same(gen.array_get(array, idx), x))
        proc += gen.break_loop()
        proc += gen.endif()
        proc += gen.set(idx, gen.add(idx, 1))
        proc += gen.endwhile()
        return proc, idx
    def rm(self, gen, idx, parent_structure):
        rmidx = fresh_name("removal_idx")
        removed = fresh_name("removed")
        array = parent_structure.field(gen, self.array)
        length = parent_structure.field(gen, self.length)
        proc  = gen.decl(rmidx, IntTy(), idx)
        proc += gen.decl(removed, RecordType(), gen.array_get(array, rmidx))
        proc += gen.set(length, gen.sub(length, 1))
        proc += gen.array_copy(RecordType(), array, array, src_start=gen.add(rmidx, 1), dst_start=rmidx, amt=gen.sub(length, rmidx))
        return (proc, removed)
    def gen_remove(self, gen, x, parent_structure):
        p1, rmidx = self.index_of(gen, x, parent_structure)
        p2, removed = self.rm(gen, rmidx, parent_structure)
        return p1 + p2
    def gen_remove_in_place(self, gen, parent_structure, iterator):
        return self.rm(gen, gen.sub(iterator.field(gen, self.idx), 1), parent_structure)
    def gen_update(self, gen, fields, x, remap, parent_structure):
        return ""
    def auxtypes(self):
        return []
