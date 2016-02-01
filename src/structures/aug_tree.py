import collections

from .interface import ConcreteImpl, RecordType, NativeTy, IntTy, BoolTy
from common import fresh_name
import predicates

AUG_MIN = "min"
AUG_MAX = "max"

INCLUSIVE = "inclusive"
EXCLUSIVE = "exclusive"

BALANCE_NONE = None
BALANCE_AVL  = "avl"

AugData = collections.namedtuple("AugData", [
    "type", "real_field", "orig_field", "qvar", "mode", "inclusive"])

def _make_augdata(field_name, predicate, fields):
    """yields AugData"""
    comparisons = list(predicates.break_conj(predicate))
    for c in comparisons:
        if c.rhs.name in fields:
            c = c.flip()
        f = c.lhs.name
        v = c.rhs.name
        t = NativeTy(fields[f])
        if f == field_name:
            continue
        if   c.op == predicates.Lt: yield AugData(t, fresh_name("min_{}".format(f)), f, v, AUG_MIN, False)
        elif c.op == predicates.Le: yield AugData(t, fresh_name("min_{}".format(f)), f, v, AUG_MIN, True)
        elif c.op == predicates.Gt: yield AugData(t, fresh_name("max_{}".format(f)), f, v, AUG_MAX, False)
        elif c.op == predicates.Ge: yield AugData(t, fresh_name("max_{}".format(f)), f, v, AUG_MAX, True)

class AugTree(ConcreteImpl):
    def __init__(self, fieldTy, fieldName, predicate, fields, balance=BALANCE_AVL):
        self.name = fresh_name("root")
        self.fieldTy = fieldTy
        self.fieldName = fieldName
        self.ty = RecordType()
        self.predicate = predicate
        self._fields = fields
        self.balance = balance
        clauses = list(predicates.break_conj(predicate))

        # put field names on LHS of clauses
        for i in xrange(len(clauses)):
            if clauses[i].rhs.name in fields:
                clauses[i] = clauses[i].flip()

        self.mins = []
        self.maxes = []
        for c in clauses:
            if c.lhs.name == fieldName:
                if   c.op == predicates.Gt: self.mins.append((EXCLUSIVE, c.rhs))
                elif c.op == predicates.Ge: self.mins.append((INCLUSIVE, c.rhs))
                elif c.op == predicates.Lt: self.maxes.append((EXCLUSIVE, c.rhs))
                elif c.op == predicates.Le: self.maxes.append((INCLUSIVE, c.rhs))

        self.augData = list(_make_augdata(fieldName, predicate, fields)) if predicate else ()

        self.prev_cursor_name = fresh_name("prev_cursor")
        self.cursor_name = fresh_name("cursor")
        self.left_ptr = fresh_name("left")
        self.right_ptr = fresh_name("right")
        self.parent_ptr = fresh_name("parent")
        if self.balance == BALANCE_AVL:
            self.height_name = fresh_name("height")

    def __str__(self):
        return "AugTree({})".format(self.fieldName)
    def __repr__(self):
        return self.__str__()

    def fields(self):
        return [(self.name, self.ty)]
    def construct(self, gen, parent_structure):
        name = parent_structure.field(gen, self.name)
        return gen.set(name, gen.null_value())
    def needs_var(self, v):
        return v in (x.name for x in self.predicate.vars())
    def state(self):
        return [(self.prev_cursor_name, self.ty), (self.cursor_name, self.ty)]
    def gen_empty(self, gen, qvars):
        return [gen.null_value(), gen.null_value()]
    def private_members(self):
        fields = [
            (self.left_ptr,   RecordType()),
            (self.right_ptr,  RecordType()),
            (self.parent_ptr, RecordType())]
        fields += [(ad.real_field, ad.type) for ad in self.augData]
        if self.balance == BALANCE_AVL:
            fields += [(self.height_name, IntTy())]
        return fields
    def _too_small(self, gen, node, clip=True):
        if not clip:
            return gen.false_value()
        e = gen.false_value()
        for (mode, bound) in self.mins:
            compare = gen.le if mode == EXCLUSIVE else gen.lt
            ee = compare(self.fieldTy, gen.get_field(node, self.fieldName), bound.name)
            e = gen.either(e, ee)
        return e
    def _too_large(self, gen, node, clip=True):
        if not clip:
            return gen.false_value()
        e = gen.false_value()
        for (mode, bound) in self.maxes:
            compare = gen.le if mode == EXCLUSIVE else gen.lt
            ee = compare(self.fieldTy, bound.name, gen.get_field(node, self.fieldName))
            e = gen.either(e, ee)
        return e
    def _subtree_ok(self, gen, root, clip=True):
        """could ANY node in the subtree be valid? only checks augdata."""
        if not clip:
            return gen.true_value()
        e = gen.true_value()
        for aug in self.augData:
            if aug.mode == AUG_MAX and     aug.inclusive: op = gen.ge
            if aug.mode == AUG_MAX and not aug.inclusive: op = gen.gt
            if aug.mode == AUG_MIN and     aug.inclusive: op = gen.le
            if aug.mode == AUG_MIN and not aug.inclusive: op = gen.lt
            e = gen.both(e,
                op(aug.type, gen.get_field(root, aug.real_field), aug.qvar))
        return e
    def _node_ok(self, gen, node, clip=True):
        """Does this subnode agree with the query? only checks augdata."""
        if not clip:
            return gen.true_value()
        e = gen.true_value()
        for aug in self.augData:
            if aug.mode == AUG_MAX and     aug.inclusive: op = gen.ge
            if aug.mode == AUG_MAX and not aug.inclusive: op = gen.gt
            if aug.mode == AUG_MIN and     aug.inclusive: op = gen.le
            if aug.mode == AUG_MIN and not aug.inclusive: op = gen.lt
            e = gen.both(e,
                op(aug.type, gen.get_field(node, aug.orig_field), aug.qvar))
        return e
    def _has_parent(self, gen, node):
        return gen.not_true(gen.is_null(gen.get_field(node, self.parent_ptr)))
    def _is_left_child(self, gen, node):
        return gen.both(self._has_parent(gen, node), gen.same(node, gen.get_field(gen.get_field(node, self.parent_ptr), self.left_ptr)))
    def _is_right_child(self, gen, node):
        return gen.both(self._has_parent(gen, node), gen.same(node, gen.get_field(gen.get_field(node, self.parent_ptr), self.right_ptr)))
    def _find_min(self, gen, root, clip=True):
        """precond: _subtree_ok(root)"""
        # capture the root in a fresh variable to avoid writing to it
        root2 = fresh_name("root")
        proc  = gen.decl(root2, self.ty, root)
        root  = root2

        x = fresh_name("x")
        proc += gen.decl(x, self.ty, root)

        # recursive alg:
        # if x is too small
        #     if x has right child: return _find_min(right)
        #     else return NULL
        # else if has left child
        #     n <- _find_min(left)
        #     if n is not NULL: return n
        #     else return x too large ? NULL : x
        # else if x is too large, return NULL
        # else return x

        # linearization:
        # mode = DESCEND
        # while True
        # if mode == DESCEND
        #     if x is too small:
        #         if x has right child:
        #             if x is root: root = right
        #             x = right
        #         else if x is not root: x = parent; mode = ASCEND // too small, no right child, not the root... back out!
        #         else: return NULL // x too small, no right child... no answer!
        #     else if x has left child:
        #         x = left
        #     else if x is too large:
        #         if x is not root: x = parent; mode = ASCEND // no left child, x too big: back out!
        #         else: return NULL; // x is root, is too large, and has no left
        #     else if _node_ok(x): return x; // x is not too small or large, and has no left child
        #     else if x is root: x = root = right; // if there is an answer, it lies to the right
        #     else: x = parent; mode = ASCEND
        # else if mode == ASCEND_FROM_LEFT
        #     // x is not too small, or we would be in ASCEND_FROM_RIGHT
        #     // there is no answer in X.left
        #     if x is too large:
        #         return NULL; // if our parent was smaller and ok, it would have returned itself!
        #     else:
        #         // x is not too large but there is no answer in left tree
        #         if _node_ok(x): return x // got it!
        #         else if x has right child:
        #             if x is root: root = right
        #             x = right; mode = DESCEND
        #         else if x is root: return NULL // it isn't X, it isn't in X.left, it isn't in X.right
        #         else: x = x.parent; mode = ASCEND // it isn't X, it isn't in X.left, it isn't in X.right
        # else if mode == ASCEND_FROM_RIGHT:
        #     // no answer is left subtree, x is not answer, no answer in right subtree
        #     if x is root: return NULL // x is not ok, or we would have returned it
        #     else: x = x.parent; mode = ASCEND // no answer in this subtree

        descend = fresh_name("descend")
        from_left = fresh_name("from_left")
        bool_type = BoolTy()
        proc += gen.decl(descend, bool_type, gen.true_value())
        proc += gen.decl(from_left, bool_type, gen.true_value())

        parent = gen.get_field(x, self.parent_ptr)
        right  = gen.get_field(x, self.right_ptr)
        left   = gen.get_field(x, self.left_ptr)
        null   = gen.null_value()

        ascend = (
            gen.set(descend, gen.false_value()) +
            gen.set(from_left, self._is_left_child(gen, x)) +
            gen.set(x, parent))

        return_null = (
            gen.set(x, null) +
            gen.break_loop())

        return_x = gen.break_loop()

        descend_right = (
            gen.if_true(gen.same(x, root)) +
            gen.set(root, right) +
            gen.endif() +
            gen.set(x, right))

        proc += gen.while_true(gen.true_value())

        proc += gen.if_true(gen.is_null(x))
        proc += return_null
        proc += gen.endif()

        proc += gen.if_true(descend) # descending
        # The min might be x, one of x's children, or anywhere above x

        proc += gen.comment("too small?")
        proc += gen.if_true(self._too_small(gen, x, clip))  # x too small
        proc += gen.if_true(self._has_right(gen, x, clip))  # x too small, has right
        proc += descend_right
        proc += gen.else_if(gen.same(x, root))              # x too small, has no right, is root
        proc += return_null
        proc += gen.else_true()                             # x too small, has no right, has parent
        proc += ascend
        proc += gen.endif()
        proc += gen.else_if(self._has_left(gen, x, clip))   # x not too small, has left
        proc += gen.set(x, left)
        proc += gen.comment("too large?")
        proc += gen.else_if(self._too_large(gen, x, clip))  # x not too small, has no left, x too large
        proc += gen.if_true(gen.same(x, root))              # x not too small, has no left, x too large, is root
        proc += return_null
        proc += gen.else_true()                             # x not too small, has no left, x too large, is not root
        proc += ascend
        proc += gen.endif()
        proc += gen.comment("node ok?")
        proc += gen.else_if(self._node_ok(gen, x, clip))    # x not too small, has no left, x not too large, other conditions check out
        proc += return_x
        proc += gen.else_if(gen.same(x, root))              # x not too small, has no left, x not too large, other conditions don't check out, x is root
        proc += gen.set(root, right) + gen.set(x, right)    # descend_right
        proc += gen.else_true()                             # x not too small, has no left, x not too large, other conditions don't check out, x is not root
        proc += gen.if_true(self._has_right(gen, x, clip))  # x not too small, has no left, x not too large, other conditions don't check out, x is not root, x has right
        proc += descend_right
        proc += gen.else_true()                             # x not too small, has no left, x not too large, other conditions don't check out, x is not root, x has no right
        proc += ascend
        proc += gen.endif()
        proc += gen.endif()

        proc += gen.else_if(from_left) # ascending from left
        # The min might be x, one of x's right children, or anywhere above x

        proc += gen.if_true(self._too_large(gen, x, clip))  # x too large
        proc += return_null
        proc += gen.else_if(self._node_ok(gen, x, clip))    # x not too large, other conditions check out
        proc += return_x
        proc += gen.else_if(self._has_right(gen, x, clip))  # x not too large, other conditions don't check out, has right
        proc += gen.set(descend, gen.true_value())
        proc += descend_right
        proc += gen.else_if(gen.same(x, root))              # x not too large, other conditions don't check out, has no right, is root
        proc += return_null
        proc += gen.else_true()                             # x not too large, other conditions don't check out, has no right, is not root
        proc += ascend
        proc += gen.endif()

        proc += gen.else_true() # ascending from right
        # The min must be above x

        proc += gen.if_true(gen.same(x, root))              # x is root
        proc += return_null
        proc += gen.else_true()                             # x is not root
        proc += ascend
        proc += gen.endif()

        proc += gen.endif()

        proc += gen.endwhile()
        return proc, x

    def _has_left(self, gen, node, clip=True):
        return gen.both(
            gen.not_true(gen.is_null(gen.get_field(node, self.left_ptr))),
            self._subtree_ok(gen, gen.get_field(node, self.left_ptr), clip))
    def _has_right(self, gen, node, clip=True):
        return gen.both(
            gen.not_true(gen.is_null(gen.get_field(node, self.right_ptr))),
            self._subtree_ok(gen, gen.get_field(node, self.right_ptr), clip))
    def gen_query(self, gen, qvars, this):
        p, m = self._find_min(gen, this.field(gen, self.name))
        return p, [gen.null_value(), m]
    def gen_current(self, gen):
        return "", self.cursor_name
    def gen_advance(self, gen):
        proc = gen.comment("ADVANCE")
        target = self.cursor_name

        right_min = fresh_name("right_min")

        proc += gen.do_while()

        # successor of any node with a right child is the min node to the right
        proc += gen.decl(right_min, self.ty, gen.null_value())
        proc += gen.if_true(self._has_right(gen, target))
        p, m = self._find_min(gen, gen.get_field(target, self.right_ptr))
        proc += p
        proc += gen.set(right_min, m)
        proc += gen.endif()

        proc += gen.if_true(gen.not_true(gen.is_null(right_min)))
        proc += gen.set(target, right_min)
        proc += gen.break_loop()

        # If there is no matching node to the right, then successor is
        # elsewhere in the tree.
        proc += gen.else_true()

        # Ascend until we get to a left child (or root)
        proc += gen.while_true(self._is_right_child(gen, target))
        proc += gen.set(target, gen.get_field(target, self.parent_ptr))
        proc += gen.endwhile()

        # Parent of this node *might* be successor, if all the augdata matches.
        proc += gen.set(target, gen.get_field(target, self.parent_ptr))

        # If the parent is too large, stop!
        proc += gen.if_true(gen.both(gen.not_true(gen.is_null(target)), self._too_large(gen, target)))
        proc += gen.set(target, gen.null_value())
        proc += gen.endif()

        proc += gen.endif()

        proc += gen.end_do_while(gen.both(
            gen.not_true(gen.is_null(target)),
            gen.not_true(self._node_ok(gen, target))))

        return proc
    def gen_next(self, gen):
        oldcursor = fresh_name()
        proc  = gen.decl(oldcursor, RecordType(), self.cursor_name)
        proc += self.gen_advance(gen)
        proc += gen.set(self.prev_cursor_name, oldcursor)
        return proc, oldcursor
    def gen_has_next(self, gen):
        return "", gen.not_true(gen.is_null(self.cursor_name))
    def _height(self, gen, x):
        assert self.balance == BALANCE_AVL
        return gen.ternary(gen.is_null(x), "-1", gen.get_field(x, self.height_name))
    def _rotate(self, gen, x, child, parent_structure):
        otherchild = self.left_ptr if child == self.right_ptr else self.right_ptr
        proc =  gen.comment("rotate {}".format(gen.get_field(x, child)))
        a = fresh_name("a")
        b = fresh_name("b")
        c = fresh_name("c")
        proc += gen.decl(a, RecordType(), x) # non-null
        # proc += "assert({}); //1\n".format(gen.not_true(gen.is_null(a)))
        proc += gen.decl(b, RecordType(), gen.get_field(a, child)) # non-null
        # proc += "assert({}); //2\n".format(gen.not_true(gen.is_null(b)))
        proc += gen.decl(c, RecordType(), gen.get_field(b, otherchild)) # maybe null
        proc += self.replace_node_in_parent(gen, gen.get_field(a, self.parent_ptr), a, b)
        proc += self.replace_node_in_parent(gen, b, c, a, otherchild)
        # proc += "assert({}); //3\n".format(gen.same(a, gen.get_field(b, otherchild)))
        proc += self.replace_node_in_parent(gen, a, b, c, child)
        # proc += "assert({}); //4\n".format(gen.same(gen.get_field(a, child), c))
        proc += self.recompute_all_augdata(gen, a)
        proc += self.recompute_all_augdata(gen, b)
        proc += gen.if_true(gen.not_true(gen.is_null(gen.get_field(b, self.parent_ptr))))
        proc += self.recompute_all_augdata(gen, gen.get_field(b, self.parent_ptr))
        proc += gen.else_true()
        proc += gen.set(parent_structure.field(gen, self.name), b)
        proc += gen.endif()
        # proc += "assert({}); //5\n".format(gen.same(a, gen.get_field(b, otherchild)))
        # proc += "assert({}); //6\n".format(gen.same(gen.get_field(a, child), c))
        return proc
    def _recompute_height(self, gen, x):
        h1 = self._height(gen, gen.get_field(x, self.left_ptr))
        h2 = self._height(gen, gen.get_field(x, self.right_ptr))
        return gen.set(gen.get_field(x, self.height_name), "1+({})".format(gen.ternary(gen.gt(IntTy(), h1, h2), h1, h2)))
    def gen_insert_with_index(self, gen, x, parent_structure, indexval):
        name = parent_structure.field(gen, self.name)

        prev = fresh_name("previous")
        curr = fresh_name("current")
        is_left = fresh_name("is_left")

        proc  = gen.set(gen.get_field(x, self.left_ptr), gen.null_value())
        proc += gen.set(gen.get_field(x, self.right_ptr), gen.null_value())
        for aug in self.augData:
            proc += gen.set(gen.get_field(x, aug.real_field), gen.get_field(x, aug.orig_field))
        if self.balance == BALANCE_AVL:
            proc += gen.set(gen.get_field(x, self.height_name), "0")

        proc += gen.decl(prev, self.ty, gen.null_value())
        proc += gen.decl(curr, self.ty, name)
        proc += gen.decl(is_left, BoolTy(), gen.false_value())

        # find insertion point
        proc += gen.while_true(gen.not_true(gen.is_null(curr)))
        proc += gen.set(prev, curr)
        proc += gen.if_true(gen.lt(self.fieldTy, indexval, gen.get_field(curr, self.fieldName)))
        proc += gen.set(curr, gen.get_field(curr, self.left_ptr))
        proc += gen.set(is_left, gen.true_value())
        proc += gen.else_true()
        proc += gen.set(curr, gen.get_field(curr, self.right_ptr))
        proc += gen.set(is_left, gen.false_value())
        proc += gen.endif()
        proc += gen.endwhile()

        # insert
        proc += gen.if_true(gen.is_null(prev))
        proc += gen.set(name, x)
        proc += gen.else_true()
        proc += gen.set(gen.get_field(x, self.parent_ptr), prev)
        proc += gen.if_true(is_left)
        proc += gen.set(gen.get_field(prev, self.left_ptr), x)
        proc += gen.else_true()
        proc += gen.set(gen.get_field(prev, self.right_ptr), x)
        proc += gen.endif()
        proc += gen.endif()

        # walk back up, updating augdata
        # TODO: we can be a bit more efficient if we do this on the way down
        proc += self.recompute_all_augdata_recursively(gen, gen.get_field(x, self.parent_ptr), gen.null_value())

        if self.balance == BALANCE_AVL:
            proc += gen.comment("rebalance AVL tree")
            cursor = fresh_name("cursor")
            proc += gen.decl(cursor, RecordType(), x)
            imbalance = fresh_name("imbalance")
            proc += gen.decl(imbalance, IntTy())
            proc += gen.while_true(gen.not_true(gen.is_null(gen.get_field(cursor, self.parent_ptr))))
            proc += gen.set(cursor, gen.get_field(cursor, self.parent_ptr))
            proc += self._recompute_height(gen, cursor)
            proc += gen.set(imbalance, gen.sub(self._height(gen, gen.get_field(cursor, self.left_ptr)), self._height(gen, gen.get_field(cursor, self.right_ptr))))

            proc += gen.if_true(gen.gt(IntTy(), imbalance, "1")) # left child too heavy (left is non-null)
            proc += gen.if_true(gen.lt(IntTy(), self._height(gen, gen.get_field(gen.get_field(cursor, self.left_ptr), self.left_ptr)), self._height(gen, gen.get_field(gen.get_field(cursor, self.left_ptr), self.right_ptr))))
            proc += self._rotate(gen, gen.get_field(cursor, self.left_ptr), self.right_ptr, parent_structure=parent_structure)
            proc += gen.endif()
            proc += self._rotate(gen, cursor, self.left_ptr, parent_structure=parent_structure)
            proc += gen.set(cursor, gen.get_field(cursor, self.parent_ptr))

            proc += gen.else_if(gen.lt(IntTy(), imbalance, "-1")) # right child too heavy (right is non-null)
            proc += gen.if_true(gen.gt(IntTy(), self._height(gen, gen.get_field(gen.get_field(cursor, self.right_ptr), self.left_ptr)), self._height(gen, gen.get_field(gen.get_field(cursor, self.right_ptr), self.right_ptr))))
            proc += self._rotate(gen, gen.get_field(cursor, self.right_ptr), self.left_ptr, parent_structure=parent_structure)
            proc += gen.endif()
            proc += self._rotate(gen, cursor, self.right_ptr, parent_structure=parent_structure)
            proc += gen.set(cursor, gen.get_field(cursor, self.parent_ptr))
            proc += gen.endif()
            proc += gen.endwhile()

        return proc
    def gen_insert(self, gen, x, parent_structure):
        idx = fresh_name("idx")
        proc  = gen.decl(idx, self.fieldTy, gen.get_field(x, self.fieldName))
        proc += self.gen_insert_with_index(gen, x, parent_structure, idx)
        return proc
    def recompute_augdata(self, gen, node, aug, remap=None):
        v = fresh_name("augval")
        proc  = gen.comment("{} is {} of {}".format(aug.real_field, aug.mode, aug.orig_field))
        proc += gen.decl(v, aug.type, remap or gen.get_field(node, aug.orig_field))

        for child in [gen.get_field(node, self.left_ptr), gen.get_field(node, self.right_ptr)]:
            n = fresh_name("child")
            proc += gen.decl(n, self.ty, child)
            proc += gen.if_true(gen.not_true(gen.is_null(n)))
            nv = fresh_name("val")
            proc += gen.decl(nv, aug.type, gen.get_field(n, aug.real_field))
            if aug.mode == AUG_MIN:
                proc += gen.set(v, gen.ternary(gen.lt(aug.type, v, nv), v, nv))
            else:
                proc += gen.set(v, gen.ternary(gen.lt(aug.type, v, nv), nv, v))
            proc += gen.endif()

        proc += gen.set(gen.get_field(node, aug.real_field), v)
        return proc
    def recompute_all_augdata(self, gen, node):
        proc = ""
        for aug in self.augData:
            proc += self.recompute_augdata(gen, node, aug)
        if self.balance == BALANCE_AVL:
            proc += self._recompute_height(gen, node)
        return proc
    def recompute_all_augdata_recursively(self, gen, node, stop, augData=None):
        """recomputes augdata for [node, node.parent, node.parent.parent, ... stop)"""
        if augData is None:
            augData = self.augData
        proc = ""
        cursor = fresh_name("cursor")
        changed = fresh_name("changed")
        proc += gen.decl(cursor, self.ty, node)
        proc += gen.decl(changed, BoolTy(), gen.true_value())
        proc += gen.while_true(gen.both(changed, gen.not_true(gen.same(cursor, stop))))
        oldies = [(fresh_name("old_{}".format(a.real_field)), a.type, a.real_field) for a in augData]
        if self.balance == BALANCE_AVL:
            oldies.append((fresh_name("old_height"), IntTy(), self.height_name))
        for (o, t, f) in oldies:
            proc += gen.decl(o, t, gen.get_field(cursor, f))
        for a in augData:
            proc += self.recompute_augdata(gen, cursor, a)
        proc += self._recompute_height(gen, cursor)
        proc += gen.set(changed, gen.false_value())
        for (o, t, f) in oldies:
            proc += gen.set(changed, gen.either(changed, gen.not_true(gen.same(o, gen.get_field(cursor, f)))))
        proc += gen.set(cursor, gen.get_field(cursor, self.parent_ptr))
        proc += gen.endwhile()
        return proc
    def replace_node_in_parent(self, gen, parent, old_node, new_node, child=None):
        proc  = gen.comment("replace {} with {} in {}".format(old_node, new_node, parent))
        if child is None:
            # parent.[L|R] = new_node
            proc += gen.if_true(gen.not_true(gen.is_null(parent)))
            proc += gen.if_true(gen.same(gen.get_field(parent, self.left_ptr), old_node))
            proc += gen.set(gen.get_field(parent, self.left_ptr), new_node)
            proc += gen.else_true()
            proc += gen.set(gen.get_field(parent, self.right_ptr), new_node)
            proc += gen.endif()
            proc += gen.endif()
        else:
            proc += gen.set(gen.get_field(parent, child), new_node)
        # new_node.parent = parent
        proc += gen.if_true(gen.not_true(gen.is_null(new_node)))
        proc += gen.set(gen.get_field(new_node, self.parent_ptr), parent)
        proc += gen.endif()
        return proc
    def gen_remove(self, gen, x, parent_structure):
        root = parent_structure.field(gen, self.name)

        p = fresh_name("parent")
        l = fresh_name("left")
        r = fresh_name("right")
        proc  = gen.decl(p, self.ty, gen.get_field(x, self.parent_ptr))
        proc += gen.decl(l, self.ty, gen.get_field(x, self.left_ptr))
        proc += gen.decl(r, self.ty, gen.get_field(x, self.right_ptr))

        new_x = fresh_name("new_x")
        proc += gen.decl(new_x, self.ty)

        # case1: no children
        proc += gen.if_true(gen.both(
            gen.is_null(l),
            gen.is_null(r)))

        proc += gen.set(new_x, gen.null_value())
        proc += self.replace_node_in_parent(gen, p, x, new_x)

        # case2: only has left child
        proc += gen.else_if(gen.both(
            gen.not_true(gen.is_null(l)),
            gen.is_null(r)))

        proc += gen.set(new_x, l)
        proc += self.replace_node_in_parent(gen, p, x, new_x)

        # case3: only has right child
        proc += gen.else_if(gen.both(
            gen.is_null(l),
            gen.not_true(gen.is_null(r))))

        proc += gen.set(new_x, r)
        proc += self.replace_node_in_parent(gen, p, x, new_x)

        # case4: two children
        proc += gen.else_true()
        find_min, m = self._find_min(gen, gen.get_field(x, self.right_ptr), clip=False) # m = smallest node greater than x
        proc += find_min
        proc += gen.set(new_x, m)

        # capture m's pointers
        mp = fresh_name("mp")
        proc += gen.decl(mp, self.ty, gen.get_field(m, self.parent_ptr))
        ml = gen.null_value() # NOTE: m.L is always null!
        mr = fresh_name("mr")
        proc += gen.decl(mr, self.ty, gen.get_field(m, self.right_ptr))

        # remove m
        # NOTE: if x.R == m, this modifies x.R! Be careful not to mention "r" below here.
        # NOTE: m.{L,R} still point to tree nodes!
        proc += self.replace_node_in_parent(gen, mp, m, mr)

        # put m in x's place
        proc += self.replace_node_in_parent(gen, p, x, m)
        proc += self.replace_node_in_parent(gen, m, ml, l, child=self.left_ptr)
        proc += self.replace_node_in_parent(gen, m, mr, gen.get_field(x, self.right_ptr), child=self.right_ptr)

        # update augdata at m
        proc += self.recompute_all_augdata(gen, m)

        # update augdata mp (incl) thru p (excl)
        proc += self.recompute_all_augdata_recursively(gen, mp, p)

        proc += gen.endif()

        # update augdata p (incl) thru root (incl)
        proc += self.recompute_all_augdata_recursively(gen, p, gen.null_value())

        # x is root?
        proc += gen.if_true(gen.same(root, x))
        proc += gen.set(root, new_x)
        proc += gen.endif()

        # TODO: rebalancing

        return proc
    def gen_remove_in_place(self, gen, parent_structure):
        to_remove = fresh_name("to_remove")
        proc  = gen.decl(to_remove, self.ty, self.prev_cursor_name)
        proc += self.gen_remove(gen, to_remove, parent_structure=parent_structure)
        proc += gen.set(self.prev_cursor_name, gen.null_value())
        return proc, to_remove
    def gen_update(self, gen, fields, x, remap, parent_structure):
        if any(f == self.fieldName for f in remap):
            proc  = self.gen_remove(gen, x, parent_structure=parent_structure)
            proc += self.gen_insert_with_index(gen, x, parent_structure=parent_structure, indexval=remap[self.fieldName])
        elif any(aug.orig_field == f for aug in self.augData for f in remap):
            needs_update = [aug for aug in self.augData if aug.orig_field in remap]
            proc = ""
            for aug in needs_update:
                proc += self.recompute_augdata(gen, x, aug, remap=remap[aug.orig_field])
            proc += self.recompute_all_augdata_recursively(gen,
                gen.get_field(x, self.parent_ptr), gen.null_value(),
                augData=needs_update)
        else:
            proc = ""
        return proc
    def auxtypes(self):
        return ()
