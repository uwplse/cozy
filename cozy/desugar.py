"""Functions to desguar higher-level constructs to lower-level ones."""

from cozy.common import ADT, typechecked
from cozy.target_syntax import *
from cozy.typecheck import retypecheck
from cozy.syntax_tools import BottomUpRewriter, subst, all_types, pprint

@typechecked
def desugar_list_comprehensions(syntax_tree : ADT) -> ADT:
    """Convert list comprehensions into filters, maps, and flatmaps."""

    class V(BottomUpRewriter):
        def visit_EListComprehension(self, e):
            res, _, _ = self.visit_clauses(e.clauses, self.visit(e.e), e.type)
            assert res.type == e.type, "desguar changed the type of an expression: {} ---> {} (e={!r})".format(pprint(e.type), pprint(res.type), e)
            return self.visit(res)
        def visit_clauses(self, clauses, final, res_type, i=0):
            if i >= len(clauses):
                return final, [], False
            clause = clauses[i]
            if isinstance(clause, CPull):
                bag = clause.e
                arg = EVar(clause.id).with_type(bag.type.elem_type)
                rest, guards, pulls = self.visit_clauses(clauses, final, res_type, i + 1)
                if guards:
                    guard = guards[0]
                    for g in guards[1:]:
                        guard = EBinOp(guard, "and", g).with_type(BOOL)
                    bag = EFilter(bag, ELambda(arg, guard)).with_type(bag.type)
                if pulls:
                    res = EFlatMap(bag, ELambda(arg, rest)).with_type(rest.type)
                else:
                    res = EMap(bag, ELambda(arg, rest)).with_type(res_type)
                return res, [], True
            elif isinstance(clause, CCond):
                rest, guards, pulls = self.visit_clauses(clauses, final, res_type, i + 1)
                return rest, guards + [clause.e], pulls
            else:
                raise NotImplementedError(clause)
    return V().visit(syntax_tree)

@typechecked
def inline_enum_constants(syntax_tree : ADT) -> ADT:
    """Convert variables that refer to enum constants into EEnumEntry nodes.

    Enum types introduce both a type name and a set of constants.  This
    function replaces variables that refer to those constants with a special
    kind of AST node representing the constant.  Most other functions in Cozy
    assume that this transformation has taken place, and that variables are not
    names for enum constants.
    """

    repl = {
        name : EEnumEntry(name).with_type(t)
        for t in all_types(syntax_tree)
        if isinstance(t, TEnum)
        for name in t.cases }
    return subst(syntax_tree, repl)

@typechecked
def convert_sets_to_bags(spec : Spec) -> Spec:
    """Convert set-type state variables to bag-type state variables.

    This function also adds invariants stating that all bags which used to be
    sets have distinct elements.
    """

    spec = Spec(
        spec.name,
        list(spec.types),
        list(spec.extern_funcs),
        list(spec.statevars),
        list(spec.assumptions),
        list(spec.methods),
        spec.header,
        spec.footer,
        spec.docstring)

    for i in range(len(spec.statevars)):
        v, t = spec.statevars[i]
        if isinstance(t, TSet):
            t = TBag(t.elem_type)
            spec.statevars[i] = (v, t)
            v = EVar(v).with_type(t)
            spec.assumptions.append(EUnaryOp(UOp.AreUnique, v).with_type(BOOL))

    if not retypecheck(spec, env={}):
        raise Exception("Set->Bag conversion failed")

    return spec

@typechecked
def desugar(spec : Spec) -> Spec:
    """Desguar a specification.

    This function applies these transformations:
        - inline enum constants
        - convert sets to bags
        - convert list comprehensions to filter, map, and flatmap expressions
    """

    spec = inline_enum_constants(spec)
    spec = convert_sets_to_bags(spec)
    spec = desugar_list_comprehensions(spec)
    return spec
