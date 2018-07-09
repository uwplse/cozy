"""Functions to desguar higher-level constructs to lower-level ones."""

from cozy.common import typechecked
from cozy.target_syntax import *
from cozy.typecheck import retypecheck
from cozy.syntax_tools import BottomUpRewriter, subst, all_types

@typechecked
def desugar_list_comprehensions(e : Exp) -> Exp:
    """Convert list comprehensions into filters, maps, and flatmaps."""

    class V(BottomUpRewriter):
        def visit_EListComprehension(self, e):
            res, _, _ = self.visit_clauses(e.clauses, self.visit(e.e))
            return self.visit(res)
        def visit_clauses(self, clauses, final, i=0):
            if i >= len(clauses):
                return final, [], False
            clause = clauses[i]
            if isinstance(clause, CPull):
                bag = clause.e
                arg = EVar(clause.id).with_type(bag.type.t)
                rest, guards, pulls = self.visit_clauses(clauses, final, i + 1)
                if guards:
                    guard = guards[0]
                    for g in guards[1:]:
                        guard = EBinOp(guard, "and", g).with_type(BOOL)
                    bag = EFilter(bag, ELambda(arg, guard)).with_type(bag.type)
                if pulls:
                    res = EFlatMap(bag, ELambda(arg, rest)).with_type(rest.type)
                else:
                    res = EMap(bag, ELambda(arg, rest)).with_type(TBag(rest.type))
                return res, [], True
            elif isinstance(clause, CCond):
                rest, guards, pulls = self.visit_clauses(clauses, final, i + 1)
                return rest, guards + [clause.e], pulls
            else:
                raise NotImplementedError(clause)
    return V().visit(e)

@typechecked
def desugar(spec : Spec) -> Spec:

    # rewrite enums
    repl = {
        name : EEnumEntry(name).with_type(t)
        for t in all_types(spec)
        if isinstance(t, TEnum)
        for name in t.cases }
    spec = subst(spec, repl)

    ## TODO: it wasn't clear where the bags are.  A list can have
    ## duplicates, so it can represent a bag.  Or, maybe this comment
    ## refers to more than just the very next statement?  If it refers to
    ## more, then change whitespace to either put a blank line after it or
    ## to remove all blank lines within the section of the function that
    ## the comment refers to.
    # convert all collection types to bags
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
            # Sets become bags w/ implicit unique assumptions.
            t = TBag(t.t)
            spec.statevars[i] = (v, t)
            v = EVar(v).with_type(t)
            spec.assumptions.append(EUnaryOp(UOp.AreUnique, v).with_type(BOOL))

    assert retypecheck(spec, env={})

    class V(BottomUpRewriter):
        def visit_Exp(self, e):
            return desugar_list_comprehensions(e)
    spec = V().visit(spec)

    assert retypecheck(spec, env={})

    return spec
