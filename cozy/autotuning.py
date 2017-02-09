from collections import deque

from cozy.common import typechecked
from cozy.typecheck import typecheck
from cozy.library import Library
from cozy.target_syntax import Spec
from cozy.syntax_tools import subst, deep_copy, all_types

def find_refinement(ast, lib):
    for (v, t) in ast.statevars:
        refs = list(lib.impls(t))
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
def enumerate_impls(ast : Spec, lib : Library):
    """
    Takes a specification as input and yields refined implementations.
    """

    wq = deque()
    wq.append(ast)

    while wq:
        ast = wq.popleft()
        refinement = find_refinement(ast, lib)
        if refinement:
            statevar, rewrites = refinement
            for new_type in rewrites:
                wq.append(apply_rewrite(statevar, new_type, ast))
        else:
            yield ast
