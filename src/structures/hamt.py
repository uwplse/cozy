import collections

from .interface import IntTy, VecTy, NodeTy, TupleTy, NativeTy, BoolTy, ListTy, MapTy, RecordType, RefTy
from .hash_map import HashMap
from common import fresh_name

class Hamt(HashMap):
    def __init__(self, fields, predicate, valueImpl):
        super(Hamt, self).__init__(fields, predicate, valueImpl)
        self.node_ty = TupleTy(dict())
        self.node_ty.fields = {'signature': IntTy()}
        self.node_ty.fields['isLeaf'] = BoolTy()
        self.node_ty.fields['next'] = ListTy(self.node_ty.name)
        self.node_ty.fields['values'] = ListTy("Record") # need to be fixed
        self.node_name = fresh_name("node")
        self.length_name = fresh_name("length")

    def construct(self, gen, parent_structure):
    	proc = self.node_construct(gen, self.node_name, False)
        proc += gen.set(self.length_name, 4); # Bad style
        return proc;

    def fields(self):
        return [(self.node_name, NodeTy(self.node_ty.name)), (self.length_name, IntTy())]

    def state(self):
        return list(self.valueImpl.state()) + [
            (self.iterator_key_name, self.keyTy),
            (self.iterator_handle_name, self.handle_type())]

    def node_construct(self, gen, node, is_leaf):
        proc = gen.init_new(node, self.node_ty)
        if is_leaf:
            proc += gen.set(gen.get_node_is_leaf_value(node), gen.true_value())
            proc += gen.set(gen.get_node_values(node), gen.new_list(gen.record_type()))
        else:
            proc += gen.set(gen.get_node_is_leaf_value(node), gen.false_value())
            proc += gen.set(gen.get_node_next(node), gen.new_list(self.node_ty.name))
            index = fresh_name("index")
            proc += gen.decl(index, IntTy(), 0)
            proc += gen.while_true(gen.lt(IntTy(), index, 16))
            proc += gen.list_add(gen.get_node_next(node), gen.null_value())
            proc += gen.plus_one(index)
            proc += gen.endwhile()
        proc += gen.set(gen.get_node_signature(node), 0)
        return proc

    def add_signature(self, gen, node, new_node, bits, hashcode, startIndex, length):
        is_match = fresh_name("isMatch")
        proc = ""
        proc += gen.if_true(gen.get_node_is_leaf_value(node))
        proc += gen.end_return()
        proc += gen.endif()
        proc += gen.decl(is_match, BoolTy())
        proc += self.match(gen, node, bits, is_match, hashcode, startIndex, length)
        proc += gen.if_true(is_match)
        proc += gen.end_return()
        proc += gen.endif()
        proc += gen.set(gen.get_node_signature(node), gen.bitwise_or(gen.get_node_signature(node), gen.left_shift(1, bits)))
        proc += gen.list_set(gen.get_node_next(node), bits, new_node)
        return proc

    def get_match_node(self, gen, match, node, bits, hashcode, startIndex, length):
        is_match = fresh_name("isMatch")
        proc = gen.decl(is_match, BoolTy())
        proc += self.match(gen, node, bits, is_match, hashcode, startIndex, length)
        proc += gen.if_true(gen.not_true(is_match))
        proc += gen.set(match, gen.null_value())
        proc += gen.else_true()
        proc += gen.map_find_handle(gen.get_node_next(node), bits, match)
        proc += gen.endif()
        return proc

    def match(self, gen, node, bits, is_match, hashcode, startIndex, length):
        proc = gen.if_true(gen.get_node_is_leaf_value(node))
        proc += gen.set(is_match, "false")
        proc += gen.else_true()
        proc += self.get_match_bits(gen, bits, hashcode, startIndex, length)
        proc += gen.set(is_match, gen.same(1, gen.bitwise_and(gen.right_logic_shift(gen.get_node_signature(node), bits), 1)))
        proc += gen.endif()
        return proc

    def get_match_bits(self, gen, bits, hashcode, startIndex, length):
        return gen.set(bits, gen.right_logic_shift(gen.left_shift(hashcode, startIndex),("(32 - {})".format(length))))

    def handle_lookup(self, gen, node, k):
        handle = fresh_name("handle")
        index = fresh_name("index")
        proc = gen.decl(handle, RecordType(), gen.null_value())
        proc += gen.decl(index, IntTy(), 0)
        proc += gen.while_true(gen.lt(IntTy(), index, gen.list_size(gen.get_node_values(node))))
        sub = fresh_name("sub")
        proc += gen.decl(sub, RecordType(), gen.list_get(gen.get_node_values(node), index))
        proc += gen.if_true(gen.equals(gen.record_name(sub), k))
        proc += gen.set(handle, sub)
        is_removed = fresh_name()
        proc += gen.decl(is_removed, BoolTy(), gen.list_remove(gen.get_node_values(node), sub))
        proc += gen.break_loop()
        proc += gen.endif()
        proc += gen.endwhile()
        return proc, handle

    def find_match(self, gen, hashcode, node, level):
        proc = gen.while_true(gen.le(IntTy(), level, 8)) # Bad style
        match = fresh_name("match")
        bits = fresh_name("bits")
        proc += gen.decl(match, NodeTy(self.node_ty.name))
        proc += gen.decl(bits, IntTy(), 0)
        proc += self.get_match_node(gen, match, node, bits, hashcode, gen.mul(self.length_name, level), self.length_name)    
        # if
        proc += gen.if_true(gen.is_null(match))
        proc += gen.break_loop();
        proc += gen.endif()
        # end if
        proc += gen.set(node, match)
        proc += gen.plus_one(level)
        proc += gen.endwhile()
        return proc

    def gen_insert_at_key(self, gen, x, parent_structure, k=None):
    	proc = ""
        if k is None:
            k = fresh_name("key")
            proc += gen.decl(k, self.keyTy)
            proc += self.make_key_of_record(gen, x, k)
        hashcode = fresh_name("hashcode")
        proc += gen.decl(hashcode, IntTy(), gen.hash_code(self.keyTy, k))
        node = fresh_name("node")
        proc += gen.decl(node, NodeTy(self.node_ty.name), self.node_name)
        level = fresh_name("level")
        proc += gen.decl(level, IntTy(), 0)
        proc += self.find_match(gen, hashcode, node, level)
        # while
        proc += gen.while_true(gen.le(IntTy(), level, 8))
        new_node = fresh_name("node")
        bits = fresh_name("bit")
        proc += gen.decl(bits, IntTy(), 0)
        proc += gen.decl(new_node, NodeTy(self.node_ty.name))
        # if
        proc += gen.if_true(gen.lt(IntTy(), level, 8))
        proc += self.node_construct(gen, new_node, False)
        proc += gen.else_true()
        proc += self.node_construct(gen, new_node, True)
        proc += gen.endif()
        # end if      
        proc += self.add_signature(gen, node, new_node, bits, hashcode, gen.mul(self.length_name, level), self.length_name)
        proc += gen.list_add(gen.get_node_next(node), new_node)
        proc += gen.set(node, new_node)
        proc += gen.plus_one(level)
        proc += gen.endwhile()
        # end while
        p, handle = self.handle_lookup(gen, node, k)
        proc += p
        proc += self.valueImpl.gen_insert(gen, x, self.valueTy.instance(handle))

        proc += gen.list_add(gen.get_node_values(node), x)
        return proc

    def gen_insert(self, gen, x, parent_structure):
        return self.gen_insert_at_key(gen, x, parent_structure)

    def gen_remove_at_key(self, gen, x, parent_structure, k=None):
        proc = ""
        hashcode = fresh_name("hashcode")
        proc += gen.decl(hashcode, IntTy())
        if k is None:
            k = fresh_name("key")
            proc += gen.decl(k, self.keyTy)
            proc += self.make_key_of_record(gen, x, k)
        proc += gen.set(hashcode, gen.hash_code(self.keyTy, k))
        node = fresh_name("node")
        proc += gen.decl(node, NodeTy(self.node_ty.name), self.node_name)
        level = fresh_name("level")
        proc += gen.decl(level, IntTy(), 0)
        proc += self.find_match(gen, hashcode, node, level)
        proc += gen.if_true(gen.same(level, 9))
        remove_result = fresh_name()
        proc += gen.decl(remove_result, BoolTy())
        p, handle = self.handle_lookup(gen, node, k)
        proc += p
        proc += self.valueImpl.gen_remove(gen, x, self.valueTy.instance(handle))
        proc += gen.list_add(gen.get_node_values(node), handle)
        proc += gen.endif()
        return proc

    def gen_remove(self, gen, x, parent_structure):
        return self.gen_remove_at_key(gen, x, parent_structure)

    def gen_remove_in_place(self, gen, parent_structure):
        proc = ""
        proc += gen.set(self.iterator_handle_name, self.valueImpl.prev_cursor_name)
        proc += gen.list_remove(parent_structure.this, self.iterator_handle_name) + ";\n" # Bad
        p, removed = self.valueImpl.gen_remove_in_place(gen, parent_structure=self.valueTy.instance(self.iterator_handle_name))
        proc += p
        return proc, removed

    def gen_query(self, gen, qvars, parent_structure):
        proc = ""
        vs = collections.OrderedDict()
        k = fresh_name("key")
        hashcode = fresh_name("hashcode")
        handle_to_be_returned = fresh_name("handle")
        proc += gen.decl(k, NativeTy("String"))
        proc += gen.decl(hashcode, IntTy())
        proc += gen.decl(handle_to_be_returned, RecordType(), gen.null_value())
        for f,t in self.valueImpl.state():
            n = fresh_name(f)
            vs[f] = n
            proc += gen.decl(n, t, gen.null_value())
        proc += self.make_key(gen, k)
        proc += gen.set(hashcode, gen.hash_code(self.keyTy, k))
        node = fresh_name("node")
        proc += gen.decl(node, NodeTy(self.node_ty.name), self.node_name)
        level = fresh_name("level")
        proc += gen.decl(level, IntTy(), 0)
        proc += self.find_match(gen, hashcode, node, level)
        proc += gen.if_true(gen.logical_and(gen.not_true(gen.is_null(node)), gen.same(level, 9)))
        node_value = gen.get_node_values(node)
        p, handle = self.handle_lookup(gen, node, k)
        proc += p
        proc += gen.if_true(self.handle_exists(gen, node_value, handle))
        sub = fresh_name("substructure")
        proc += gen.decl(sub, RefTy(self.valueTy), self.read_handle(gen, node_value, handle))
        p, r = self.valueImpl.gen_query(gen, qvars, self.valueTy.instance(sub))
        proc += p
        for lhs, rhs in zip(vs.values(), r):
            proc += gen.set(lhs, rhs)
        proc += gen.list_add(gen.get_node_values(node), handle)
        proc += gen.else_true()
        r = self.valueImpl.gen_empty(gen, self.valueTy.instance(sub))
        for lhs, rhs in zip(vs.values(), r):
            proc += gen.set(lhs, rhs)
        proc += gen.endif()
        proc += gen.set(handle_to_be_returned, handle)
        proc += gen.endif()
        return (proc, list(vs.values()) + [k, handle_to_be_returned])

    def gen_query_one(self, gen, qvars, parent_structure):
        return super(HashMap, self).gen_query_one(gen, qvars, parent_structure)

    def gen_query_one(self, gen, qvars, parent_structure):
        return super(HashMap, self).gen_query_one(gen, qvars, parent_structure)

    def auxtypes(self):
        yield self.node_ty

    def gen_update(self, gen, fields, x, remap, parent_structure):
        return ""










