from collections import deque
import itertools

from cozy.common import typechecked
from cozy.typecheck import typecheck
from cozy.library import Library
from cozy.syntax import Spec, Exp, EVar, EAll, EEq, T
from cozy.syntax_tools import subst, deep_copy, all_types

def find_refinement(ast, state_map, lib, assumptions):
    assumptions = EAll(itertools.chain(
        assumptions,
        ast.assumptions,
        (EEq(EVar(v).with_type(e.type), e) for (v, e) in state_map.items())))
    for (v, t) in ast.statevars:
        refs = list(lib.impls(
            EVar(v).with_type(t),
            assumptions=assumptions))
        if not (len(refs) == 1 and refs[0] == t):
            return (v, refs)
    return None

def apply_rewrite(statevar, new_type, ast):
    new_ast = Spec(
        ast.name,
        ast.types,
        ast.extern_funcs,
        [v for v in ast.statevars if v[0] != statevar] + [(statevar, new_type)],
        deep_copy(ast.assumptions),
        deep_copy(ast.methods))
    errs = typecheck(new_ast)
    for e in errs:
        print(e)
    if errs:
        raise Exception("internal consistency violation: refined spec does not typecheck")
    return new_ast

@typechecked
def enumerate_impls(ast : Spec, state_map : { str : Exp }, lib : Library, assumptions : [Exp] = []):
    """
    Takes a specification as input and yields refined implementations.
    """

    wq = deque()
    wq.append(ast)

    while wq:
        ast = wq.popleft()
        refinement = find_refinement(ast, state_map, lib, assumptions)
        if refinement:
            statevar, rewrites = refinement
            for new_type in rewrites:
                wq.append(apply_rewrite(statevar, new_type, ast))
        else:
            yield ast
