import collections

from .interface import IntTy, VecTy, NodeTy
from .hash_map import HashMap
from common import fresh_name

class Hamt(HashMap):
    def __init__(self, fields, predicate, valueImpl):
        super(Hamt, self).__init__(fields, predicate, valueImpl)
        self.fields = {''}
        self.node_name = fresh_name("node")
        self.length_name = fresh_name("length")

    def construct(self, gen, parent_structure):
    	proc = gen.node_set(self.node_name, False)
        proc += gen.set(self.length_name, 4); # Bad style
        return proc;

    def fields(self):
        return [(self.node_name, NodeTy()), (self.length_name, IntTy())]

    def gen_insert(self, gen, x, parent_structure, k=None):
    	proc = ""
        if k is None:
            k = fresh_name("key")
            proc += gen.decl(k, self.keyTy)
            proc += self.make_key_of_record(gen, x, k)
        hashcode = fresh_name("hashcode")
        proc += gen.decl(hashcode, IntTy(), gen.hash_code(self.keyTy, k))
        node = fresh_name("node")
        proc += gen.decl(node, NodeTy(), self.node_name)
        level = fresh_name("level")
        proc += gen.decl(level, IntTy(), 0)
        # while
        proc += gen.while_true(gen.le(IntTy(), level, 8)) # Bad style
        match = fresh_name("match")
        proc += gen.decl(match, NodeTy(), "{}.getMatchNode({}, length * i, length)".format(match, hashcode))
        # if
        proc += gen.if_true(gen.is_null(match))
        proc += gen.break_loop();
        proc += gen.endif()
        # end if
        proc += gen.set(node, match)
        proc += gen.plus_one(level)
        proc += gen.endwhile()
        # end while

        # while
        proc += gen.while_true(gen.le(IntTy(), level, 8))
        new_node = fresh_name("node")
        proc += gen.decl(new_node, NodeTy())
        # if
        proc += gen.if_true("INTEGER_BIT_LENGTH % length == 0 && i == INTEGER_BIT_LENGTH / length")
        proc += gen.node_set(new_node, True)
        proc += gen.else_true()
        proc += gen.node_set(new_node, False)
        proc += gen.endif()
        # end if
        proc += "{}.addSignature({}, i * length, length);\n".format(node, hashcode)
        proc += "{}.next.add({});\n".format(node, new_node)
        proc += gen.set(node, new_node)
        proc += gen.plus_one(level)
        proc += gen.endwhile()
        # end while
        proc += "{}.add({})\n".format(node, x)
        return proc

    def gen_remove(self, gen, x, parent_structure, k=None):
        proc = ""
        hashcode = fresh_name("hashcode")
        if k is None:
            k = fresh_name("key")
            proc += gen.decl(k, self.keyTy)
            proc += self.make_key_of_record(gen, x, k)
        proc += gen.set(hashcode, gen.hash_code(self.keyTy, k))
        node = fresh_name("node")
        proc += gen.decl(node, NodeTy(), self.node_name)
        level = fresh_name("level")
        proc += gen.decl(level, IntTy(), 0)
        # while
        proc += gen.while_true(gen.le(IntTy(), level, 8)) # Bad style
        match = fresh_name("match")
        proc += gen.decl(match, NodeTy(), "{}.getMatchNode({}, length * i, length)".format(match, hashcode))
        # if
        proc += gen.if_true(gen.is_null(match))
        proc += gen.end_return()
        proc += gen.endif()
        # end if
        proc += gen.set(node, match)
        proc += gen.plus_one(level)
        proc += gen.endwhile()
        proc += "{}.remove({})\n".format(node, k)
        # end while
        return proc

    def gen_query(self, gen, qvars, parent_structure):
        proc = ""
        vs = collections.OrderedDict()
        k = fresh_name("key")
        hashcode = fresh_name("hashcode")
        for f,t in self.state():
            n = fresh_name(f)
            vs[f] = n
            proc += gen.decl(n, t)
        proc += self.make_key(gen, k)
        proc += gen.set(hashcode, gen.hash_code(self.keyTy, k))
        node = fresh_name("node")
        proc += gen.decl(node, NodeTy(), self.node_name)
        level = fresh_name("level")
        proc += gen.decl(level, IntTy(), 0)
        # while
        proc += gen.while_true(gen.le(IntTy(), level, 8)) # Bad style
        match = fresh_name("match")
        proc += gen.decl(match, NodeTy(), "{}.getMatchNode({}, length * i, length)".format(match, hashcode))
        # if
        proc += gen.if_true(gen.is_null(match))
        for val in vs:
            proc += gen.set(val, gen.null_value())
        proc += gen.endif()
        # end if
        proc += gen.set(node, match)
        proc += gen.plus_one(level)
        proc += gen.endwhile()
        # end while
        return (proc, list(vs.values()))










