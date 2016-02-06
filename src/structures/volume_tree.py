import collections

from .interface import ConcreteImpl, TupleTy, RecordType, NativeTy, PointerTy, StackTy, BoolTy
from common import fresh_name
import predicates

def is_numeric(ty):
    return ty.lower() in ("int", "integer", "long", "short", "float", "double", "btscalar")

class VolumeTree(ConcreteImpl):

    class VolumeSpec(object):
        def __init__(self, lts, gts):
            self.lts = lts
            self.gts = gts

    @staticmethod
    def infer_volume(fields, predicate):
        clauses = list(predicates.break_conj(predicate))
        lts = []
        gts = []
        types = set()
        for c in clauses:
            if (c.lhs.name in fields) == (c.rhs.name in fields):
                return
            if c.rhs.name in fields:
                c = c.flip()
            if not is_numeric(fields[c.lhs.name]):
                return
            types.add(fields[c.lhs.name])
            if c.op in (predicates.Lt, predicates.Le):
                lts.append((c.lhs.name, c.rhs.name))
            if c.op in (predicates.Gt, predicates.Ge):
                gts.append((c.lhs.name, c.rhs.name))
        # print("; ".join(str(c) for c in clauses))
        # print(lts)
        # print(gts)
        if len(lts) != len(gts):
            return
        if len(types) != 1:
            return
        yield VolumeTree.VolumeSpec(lts, gts) # todo: permutations?

    def __init__(self, spec, fields, predicate, stack_iteration=False):
        self.stack_iteration = stack_iteration
        self.spec = spec
        self.field_types = fields
        self.the_type = NativeTy(fields[spec.lts[0][0]])
        self.predicate = predicate
        self.root = fresh_name("root")
        self.left_ptr = fresh_name("left")
        self.right_ptr = fresh_name("right")
        self.leaf_ptr = fresh_name("leaf")
        self.stack_name = fresh_name("stack")
        self.prev_name = fresh_name("prev")
        self.cursor_name = fresh_name("cursor")
        self.parent_ptr = fresh_name("parent")
        self.record_parent_ptr = fresh_name("parent")
        self.remap = { f : fresh_name(f) for f, _ in (self.spec.lts + self.spec.gts) }

        myfields = [f for f, _ in spec.lts] + [f for f, _ in spec.gts]
        self.node_type = TupleTy(collections.OrderedDict(
            [(self.remap[f], NativeTy(fields[f])) for f in myfields]))
        self.node_type.fields[self.left_ptr]   = PointerTy(self.node_type)
        self.node_type.fields[self.right_ptr]  = PointerTy(self.node_type)
        self.node_type.fields[self.parent_ptr] = PointerTy(self.node_type)
        self.node_type.fields[self.leaf_ptr]   = RecordType()
        self.node_type = PointerTy(self.node_type)

    def __str__(self):
        return "VolumeTree({}, si={})".format(", ".join("{}-{}".format(f1, f2) for (f1, _), (f2, _) in zip(self.spec.lts, self.spec.gts)), self.stack_iteration)
    def __repr__(self):
        return self.__str__()

    def fields(self):
        return ((self.root, self.node_type),)
    def construct(self, gen, parent_structure):
        return gen.set(parent_structure.field(gen, self.root), gen.null_value())
    def needs_var(self, v):
        return v in ([v for _, v in self.spec.lts] + [v for _, v in self.spec.gts])
    def state(self):
        if self.stack_iteration:
            return [
                (self.stack_name, StackTy(self.node_type)),
                (self.prev_name, RecordType()),
                (self.cursor_name, RecordType())]
        return [(self.prev_name, RecordType()), (self.cursor_name, RecordType())]
    def private_members(self):
        return [(self.record_parent_ptr, self.node_type)]
    def gen_query(self, gen, qvars, parent_structure):
        field = parent_structure.field
        if self.stack_iteration:
            stk = fresh_name("stack")
            proc  = gen.decl(stk, StackTy(self.node_type), gen.new_stack(self.node_type))
            proc += gen.stack_size_hint(stk, "100")
            proc += gen.if_true(gen.not_true(gen.is_null(field(gen, self.root))))
            proc += gen.stack_push(stk, field(gen, self.root))
            proc += gen.endif()
            cursor = fresh_name("cursor")
            prev = fresh_name("prev")
            proc += gen.decl(cursor, RecordType(), gen.null_value())
            proc += gen.decl(prev, RecordType(), gen.null_value())
            proc += self._gen_advance(gen, stk, cursor, prev)
            return proc, [stk, gen.null_value(), cursor]
        cursor = fresh_name("cursor")
        proc  = gen.decl(cursor, RecordType(), gen.null_value())
        proc += gen.if_true(gen.not_true(gen.is_null(field(gen, self.root))))
        p, m = self.find_first(gen, field(gen, self.root))
        proc += p
        proc += gen.set(cursor, m)
        proc += gen.endif()
        return proc, [gen.null_value(), cursor]
    def gen_empty(self, gen, qvars):
        if self.stack_iteration:
            return [gen.new_stack(self.node_type), gen.null_value(), gen.null_value()]
        return [gen.null_value(), gen.null_value()]
    def gen_find_any(self, gen, parent_structure):
        cursor = fresh_name("cursor")
        proc  = gen.decl(cursor, self.node_type, parent_structure.field(gen, self.root))
        proc += gen.while_true(self.is_leaf(gen, cursor))
        proc += gen.set(cursor, gen.get_field(cursor, self.left_ptr))
        proc += gen.endif()
        return proc, gen.get_field(cursor, self.leaf_ptr)
    def auxtypes(self):
        return (self.node_type.ty,)
    def distance(self, gen, record, node, remap={}):
        e = "0"
        for (f1, _), (f2, _) in zip(self.spec.lts, self.spec.gts):
            e = gen.add(e,
                gen.abs(gen.sub(
                    gen.add(gen.get_field(node, self.remap[f1]), gen.get_field(node, self.remap[f2])),
                    gen.add(remap.get(f1, gen.get_field(record, f1)), remap.get(f2, gen.get_field(record, f2))))))
        return e
    def select_child(self, gen, parent, record, remap={}):
        return gen.ternary(
            gen.lt(self.the_type,
                self.distance(gen, record, gen.get_field(parent, self.right_ptr), remap=remap),
                self.distance(gen, record, gen.get_field(parent, self.left_ptr),  remap=remap)),
            gen.get_field(parent, self.right_ptr),
            gen.get_field(parent, self.left_ptr))
    def merge_volumes(self, gen, n1, n2, into):
        changed = fresh_name("changed")
        new_value = fresh_name("new_value")
        t = self.the_type # TODO
        proc  = gen.decl(changed, BoolTy(), gen.false_value())
        proc += gen.decl(new_value, t)
        for f, _ in self.spec.lts:
            f = self.remap[f]
            proc += gen.set(new_value, gen.min(t, gen.get_field(n1, f), gen.get_field(n2, f)))
            proc += gen.set(changed, gen.either(changed, gen.not_true(gen.same(gen.get_field(into, f), new_value))))
            proc += gen.set(gen.get_field(into, f), new_value)
        for f, _ in self.spec.gts:
            f = self.remap[f]
            proc += gen.set(new_value, gen.max(t, gen.get_field(n1, f), gen.get_field(n2, f)))
            proc += gen.set(changed, gen.either(changed, gen.not_true(gen.same(gen.get_field(into, f), new_value))))
            proc += gen.set(gen.get_field(into, f), new_value)
        return proc, changed
    def replace_child(self, gen, parent, old_child, new_child):
        proc  = gen.if_true(gen.same(gen.get_field(parent, self.right_ptr), old_child))
        proc += gen.set(gen.get_field(parent, self.right_ptr), new_child)
        proc += gen.else_true()
        proc += gen.set(gen.get_field(parent, self.left_ptr), new_child)
        proc += gen.endif()
        return proc
    def volume_contains(self, gen, large, small):
        e = gen.true_value()
        for (f1, _), (f2, _) in zip(self.spec.lts, self.spec.gts):
            f1 = self.remap[f1]
            f2 = self.remap[f2]
            e = gen.both(e, gen.le(self.the_type, gen.get_field(large, f1), gen.get_field(small, f1)))
            e = gen.both(e, gen.ge(self.the_type, gen.get_field(large, f2), gen.get_field(small, f2)))
        return e
    def find_insertion_point(self, gen, x, root, remap={}):
        ip = fresh_name("insertion_point")
        proc  = gen.decl(ip, self.node_type, root)
        proc += gen.while_true(gen.not_true(gen.either(
            gen.is_null(ip),
            self.is_leaf(gen, ip))))
        proc += gen.set(ip, self.select_child(gen, ip, x, remap=remap))
        proc += gen.endwhile()
        return proc, ip
    def recompute_volume(self, gen, n):
        return self.merge_volumes(gen, gen.get_field(n, self.left_ptr), gen.get_field(n, self.right_ptr), into=n)
    def recompute_volumes_recursively(self, gen, n):
        cursor = fresh_name("cursor")
        proc  = gen.decl(cursor, self.node_type, n)
        proc += gen.while_true(gen.not_true(gen.is_null(cursor)))
        p, changed = self.recompute_volume(gen, cursor)
        proc += p
        proc += gen.if_true(gen.not_true(changed)) + gen.break_loop() + gen.endif()
        proc += gen.set(cursor, gen.get_field(cursor, self.parent_ptr))
        proc += gen.endwhile()
        return proc
    def gen_insert(self, gen, x, parent_structure):
        wrapper = fresh_name("leaf")
        proc  = gen.decl(wrapper, self.node_type, gen.alloc(self.node_type.ty, []))
        for f,v in self.spec.lts + self.spec.gts:
            proc += gen.set(gen.get_field(wrapper, self.remap[f]), gen.get_field(x, f))
        proc += gen.set(gen.get_field(wrapper, self.left_ptr), gen.null_value())
        proc += gen.set(gen.get_field(wrapper, self.right_ptr), gen.null_value())
        proc += gen.set(gen.get_field(wrapper, self.parent_ptr), gen.null_value())
        proc += gen.set(gen.get_field(wrapper, self.leaf_ptr), x)
        proc += gen.set(gen.get_field(x, self.record_parent_ptr), wrapper)

        # No root? Put it there.
        proc += gen.if_true(gen.is_null(parent_structure.field(gen, self.root)))
        proc += gen.set(parent_structure.field(gen, self.root), wrapper)
        proc += gen.else_true()

        # Descend to the right spot.
        p, sibling = self.find_insertion_point(gen, x, parent_structure.field(gen, self.root))
        proc += p

        # Create a new node to contain both wrapper and sibling
        node = fresh_name("newnode")
        proc += gen.decl(node, self.node_type, gen.alloc(self.node_type.ty, []))
        proc += gen.set(gen.get_field(node, self.left_ptr), wrapper)
        proc += gen.set(gen.get_field(node, self.right_ptr), sibling)
        proc += gen.set(gen.get_field(node, self.parent_ptr), gen.null_value())
        proc += gen.set(gen.get_field(node, self.leaf_ptr), gen.null_value())
        proc += gen.set(gen.get_field(wrapper, self.parent_ptr), node)
        p, _ = self.merge_volumes(gen, wrapper, sibling, into=node)
        proc += p

        parent = fresh_name("parent")
        proc += gen.decl(parent, self.node_type, gen.get_field(sibling, self.parent_ptr))
        proc += gen.set(gen.get_field(sibling, self.parent_ptr), node)

        # Sibling is a leaf and the root
        proc += gen.if_true(gen.is_null(parent))
        proc += gen.set(parent_structure.field(gen, self.root), node)

        # Sibling is a leaf and has a parent
        proc += gen.else_true()
        proc += gen.set(gen.get_field(node, self.parent_ptr), parent)
        proc += self.replace_child(gen, parent, old_child=sibling, new_child=node)
        proc += gen.while_true(gen.not_true(gen.is_null(parent)))
        p, changed = self.merge_volumes(gen, parent, node, into=parent)
        proc += p
        proc += gen.if_true(gen.not_true(changed)) + gen.break_loop() + gen.endif()
        proc += gen.set(parent, gen.get_field(parent, self.parent_ptr))
        proc += gen.endwhile()

        proc += gen.endif()
        proc += gen.endif()
        return proc

    def gen_remove(self, gen, x, parent_structure):
        x_node = fresh_name("x_node")
        x_parent = fresh_name("x_parent")
        x_grandparent = fresh_name("x_grandparent")

        # x is the root!
        proc  = gen.decl(x_node,   self.node_type, gen.get_field(x, self.record_parent_ptr))
        proc += gen.if_true(gen.same(x_node, parent_structure.field(gen, self.root)))
        proc += gen.free(x_node)
        proc += gen.set(parent_structure.field(gen, self.root), gen.null_value())
        proc += gen.else_true()

        proc += gen.decl(x_parent, self.node_type, gen.get_field(x_node, self.parent_ptr))
        sibling = fresh_name("sibling")
        proc += gen.decl(sibling, self.node_type, gen.ternary(
            gen.same(gen.get_field(x_parent, self.left_ptr), x_node),
            gen.get_field(x_parent, self.right_ptr),
            gen.get_field(x_parent, self.left_ptr)))

        # x's parent is the root!
        proc += gen.if_true(gen.same(x_parent, parent_structure.field(gen, self.root)))
        proc += gen.set(parent_structure.field(gen, self.root), sibling)
        proc += gen.set(gen.get_field(sibling, self.parent_ptr), gen.null_value())

        # x's parent is not the root!
        proc += gen.else_true()
        proc += gen.decl(x_grandparent, self.node_type, gen.get_field(x_parent, self.parent_ptr))
        proc += self.replace_child(gen, x_grandparent, x_parent, sibling)
        proc += gen.set(gen.get_field(sibling, self.parent_ptr), x_grandparent)
        proc += self.recompute_volumes_recursively(gen, x_grandparent)
        proc += gen.endif()

        proc += gen.free(x_node)
        proc += gen.free(x_parent)
        proc += gen.endif()
        return proc

    def gen_remove_in_place(self, gen, parent_structure):
        proc = self.gen_remove(gen, self.prev_name, parent_structure)
        return proc, self.prev_name
    def gen_update(self, gen, fields, x, remap, parent_structure):
        if not any(f in ([ff for ff,_ in self.spec.lts] + [ff for ff,_ in self.spec.gts]) for f in remap):
            return "" # no effect!

        x_node = fresh_name("x_node")
        x_parent = fresh_name("x_parent")

        proc  = gen.comment("update procedure for {}".format(remap))
        proc += gen.decl(x_node,   self.node_type, gen.get_field(x, self.record_parent_ptr))
        proc += gen.decl(x_parent, self.node_type, gen.get_field(x_node, self.parent_ptr))

        # copy values up into the wrapper node
        for f, v in remap.items():
            proc += gen.set(gen.get_field(x_node, self.remap[f]), v)

        # if x is the only thing in the tree, no problem! Otherwise...
        proc += gen.if_true(gen.not_true(gen.is_null(x_parent)))

        # save a reference to x_node's old sibling
        old_sibling = fresh_name("old_sibling")
        proc += gen.decl(old_sibling, self.node_type, gen.ternary(
            gen.same(gen.get_field(x_parent, self.left_ptr), x_node),
            gen.get_field(x_parent, self.right_ptr),
            gen.get_field(x_parent, self.left_ptr)))

        # Find the insertion point: the new sibling for x_node.
        # We will replace this node with x_parent, and move this as a child of
        # x_parent in the tree.
        p, new_sibling = self.find_insertion_point(gen, x, parent_structure.field(gen, self.root), remap=remap)
        proc += p

        new_grandparent = fresh_name("new_grandparent")
        proc += gen.decl(new_grandparent, self.node_type, gen.get_field(new_sibling, self.parent_ptr))

        # If the found location is not x_node or old_sibling, then we need to
        # actually do the transform.
        proc += gen.if_true(gen.not_true(gen.same(x_parent, new_grandparent)))
        x_grandparent = fresh_name("x_grandparent")
        proc += gen.decl(x_grandparent, self.node_type, gen.get_field(x_parent, self.parent_ptr))
        proc += gen.set(gen.get_field(old_sibling, self.parent_ptr), x_grandparent)
        proc += self.replace_child(gen, x_grandparent, x_parent, old_sibling)
        proc += gen.set(gen.get_field(x_parent, self.parent_ptr), new_grandparent)
        proc += self.replace_child(gen, new_grandparent, new_sibling, x_parent)
        proc += gen.set(gen.get_field(new_sibling, self.parent_ptr), x_parent)
        proc += self.replace_child(gen, x_parent, old_sibling, new_sibling)
        proc += self.recompute_volumes_recursively(gen, x_grandparent)
        p, _ = self.recompute_volume(gen, x_parent)
        proc += p
        proc += gen.endif()

        # Expand x's chain to include the new value
        proc += self.recompute_volumes_recursively(gen, new_grandparent)

        proc += gen.endif()
        return proc

    def is_leaf(self, gen, node):
        return gen.not_true(gen.is_null(gen.get_field(node, self.leaf_ptr)))
    def query_holds(self, gen, record):
        qvars = [(v, self.field_types[f]) for f, v in self.spec.lts] + [(v, self.field_types[f]) for f, v in self.spec.gts]
        return gen.predicate(list(self.field_types.items()), qvars, self.predicate, record)
    def intersects_query(self, gen, node):
        result = gen.true_value()
        for f, v in self.spec.lts:
            result = gen.both(result, gen.le(NativeTy(self.field_types[f]), gen.get_field(node, self.remap[f]), v))
        for f, v in self.spec.gts:
            result = gen.both(result, gen.ge(NativeTy(self.field_types[f]), gen.get_field(node, self.remap[f]), v))
        return result
    def find_first(self, gen, tree_root):
        cursor = fresh_name("cursor")
        out = fresh_name("first")

        proc  = gen.decl(cursor, self.node_type, tree_root)
        proc += gen.decl(out, RecordType(), gen.null_value())

        proc += gen.while_true(gen.true_value())

        # greedy descent until you find a leaf
        proc += gen.while_true(gen.not_true(self.is_leaf(gen, cursor)))
        proc += gen.if_true(self.intersects_query(gen, gen.get_field(cursor, self.left_ptr)))
        proc += gen.set(cursor, gen.get_field(cursor, self.left_ptr))
        proc += gen.else_if(self.intersects_query(gen, gen.get_field(cursor, self.right_ptr)))
        proc += gen.set(cursor, gen.get_field(cursor, self.right_ptr))
        proc += gen.else_true()
        proc += gen.break_loop()
        proc += gen.endif()
        proc += gen.endwhile()

        # if we are at a leaf AND the leaf matches, we're done!
        proc += gen.if_true(gen.both(
            self.is_leaf(gen, cursor),
            self.query_holds(gen, gen.get_field(cursor, self.leaf_ptr))))
        proc += gen.set(out, gen.get_field(cursor, self.leaf_ptr))
        proc += gen.break_loop()
        proc += gen.endif()

        # otherwise, ascend until we can descend to the right and then do so
        proc += gen.while_true(gen.not_true(gen.same(cursor, tree_root)))
        parent = fresh_name("parent")
        proc += gen.decl(parent, self.node_type, gen.get_field(cursor, self.parent_ptr))
        proc += gen.if_true(gen.both(
            gen.same(cursor, gen.get_field(parent, self.left_ptr)),
            self.intersects_query(gen, gen.get_field(parent, self.right_ptr))))
        proc += gen.set(cursor, gen.get_field(parent, self.right_ptr))
        proc += gen.break_loop()
        proc += gen.endif()
        proc += gen.set(cursor, parent)
        proc += gen.endwhile()

        # if we are stuck at the root, then we're done!
        proc += gen.if_true(gen.same(cursor, tree_root))
        proc += gen.break_loop()
        proc += gen.endif()

        proc += gen.endwhile()

        return proc, out
    def gen_has_next(self, gen):
        return "", gen.not_true(gen.is_null(self.cursor_name))
    def gen_current(self, gen):
        return "", self.cursor_name
    def _gen_advance(self, gen, stack, cursor, prev):
            node = fresh_name("node")
            proc  = gen.set(prev, cursor)
            proc += gen.set(cursor, gen.null_value())
            proc += gen.while_true(gen.not_true(gen.stack_is_empty(stack)))
            proc += gen.decl(node, self.node_type, gen.stack_peek(stack))
            proc += gen.stack_pop(stack)

            proc += gen.if_true(self.is_leaf(gen, node))

            # TODO: determine when this if-check is necessary! It isn't for
            # Bullet, but it _is_ in general.
            # proc += gen.if_true(self.query_holds(gen, gen.get_field(node, self.leaf_ptr)))
            proc += gen.set(cursor, gen.get_field(node, self.leaf_ptr))
            proc += gen.break_loop()
            # proc += gen.endif()

            proc += gen.else_true()

            if True:
                l = fresh_name("left")
                r = fresh_name("right")

                proc += gen.decl(l, self.node_type, gen.get_field(node, self.left_ptr))
                proc += gen.decl(r, self.node_type, gen.get_field(node, self.right_ptr))

                for n in (l, r):
                    proc += gen.if_true(self.intersects_query(gen, n))
                    proc += gen.stack_push(stack, n)
                    proc += gen.endif()
            else:

                proc += gen.if_true(self.intersects_query(gen, node))
                proc += gen.stack_push(stack, gen.get_field(node, self.left_ptr))
                proc += gen.stack_push(stack, gen.get_field(node, self.right_ptr))
                proc += gen.endif()

            proc += gen.endif()

            proc += gen.endwhile()
            return proc
    def gen_advance(self, gen):
        if self.stack_iteration:
            return self._gen_advance(gen, self.stack_name, self.cursor_name, self.prev_name)

        proc  = gen.comment("advance")
        proc += gen.set(self.prev_name, self.cursor_name)
        cursor = fresh_name("cursor")
        proc += gen.decl(cursor, self.node_type, gen.get_field(self.cursor_name, self.record_parent_ptr))
        proc += gen.while_true(gen.true_value())

        # ascend until we can descend to the right and then do so
        proc += gen.while_true(gen.not_true(gen.is_null(gen.get_field(cursor, self.parent_ptr))))
        parent = fresh_name("parent")
        proc += gen.decl(parent, self.node_type, gen.get_field(cursor, self.parent_ptr))
        proc += gen.if_true(gen.both(
            gen.same(cursor, gen.get_field(parent, self.left_ptr)),
            self.intersects_query(gen, gen.get_field(parent, self.right_ptr))))
        proc += gen.set(cursor, gen.get_field(parent, self.right_ptr))
        proc += gen.break_loop()
        proc += gen.endif()
        proc += gen.set(cursor, parent)
        proc += gen.endwhile()

        # if we are stuck at the root, then we're done!
        proc += gen.if_true(gen.is_null(gen.get_field(cursor, self.parent_ptr)))
        proc += gen.set(self.cursor_name, gen.null_value())
        proc += gen.break_loop()
        proc += gen.endif()

        # find the first matching node in this subtree, if it exists
        p, m = self.find_first(gen, cursor)
        proc += p

        # we found the min!
        proc += gen.if_true(gen.not_true(gen.is_null(m)))
        proc += gen.set(self.cursor_name, m)
        proc += gen.break_loop()
        proc += gen.endif()

        proc += gen.endwhile()
        return proc
    def check_rep(self, gen, parent_structure):
        stk = fresh_name("stack")
        node = fresh_name("node")
        record = fresh_name("record")

        proc  = gen.decl(stk, StackTy(self.node_type), gen.new_stack(self.node_type))
        proc += gen.if_true(gen.not_true(gen.is_null(parent_structure.field(gen, self.root))))
        proc += gen.stack_push(stk, parent_structure.field(gen, self.root))
        proc += gen.endif()
        proc += gen.while_true(gen.not_true(gen.stack_is_empty(stk)))
        proc += gen.decl(node, self.node_type, gen.stack_peek(stk))
        proc += gen.stack_pop(stk)

        proc += gen.if_true(gen.is_null(gen.get_field(node, self.parent_ptr)))
        proc += gen.assert_true(gen.same(node, parent_structure.field(gen, self.root)))
        proc += gen.else_true()
        proc += gen.assert_true(gen.is_null(gen.get_field(gen.get_field(node, self.parent_ptr), self.leaf_ptr)))
        proc += gen.assert_true(gen.either(
            gen.same(node, gen.get_field(gen.get_field(node, self.parent_ptr), self.left_ptr)),
            gen.same(node, gen.get_field(gen.get_field(node, self.parent_ptr), self.right_ptr))))
        proc += gen.endif()

        proc += gen.if_true(gen.is_null(gen.get_field(node, self.leaf_ptr)))
        for ptr in (self.left_ptr, self.right_ptr):
            proc += gen.assert_true(gen.not_true(gen.is_null(gen.get_field(node, ptr))))
            proc += gen.assert_true(gen.same(node, gen.get_field(gen.get_field(node, ptr), self.parent_ptr)))
            proc += gen.stack_push(stk, gen.get_field(node, ptr))
        for f,_ in self.spec.lts:
            proc += gen.assert_true(gen.same(
                gen.get_field(node, self.remap[f]),
                gen.min(
                    self.the_type,
                    gen.get_field(gen.get_field(node, self.left_ptr), self.remap[f]),
                    gen.get_field(gen.get_field(node, self.right_ptr), self.remap[f]))))
        for f,_ in self.spec.gts:
            proc += gen.assert_true(gen.same(
                gen.get_field(node, self.remap[f]),
                gen.max(
                    self.the_type,
                    gen.get_field(gen.get_field(node, self.left_ptr), self.remap[f]),
                    gen.get_field(gen.get_field(node, self.right_ptr), self.remap[f]))))
        proc += gen.else_true()
        proc += gen.decl(record, RecordType(), gen.get_field(node, self.leaf_ptr))
        proc += gen.assert_true(gen.same(node, gen.get_field(record, self.record_parent_ptr)))
        for f,_ in (self.spec.lts + self.spec.gts):
            proc += gen.assert_true(gen.same(gen.get_field(node, self.remap[f]), gen.get_field(record, f)))
        proc += gen.endif()

        proc += gen.endwhile()
        return proc
