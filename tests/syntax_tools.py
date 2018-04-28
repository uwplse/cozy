import unittest

from cozy.common import OrderedSet
from cozy.target_syntax import *
from cozy.syntax_tools import *
from cozy.typecheck import retypecheck
from cozy.solver import valid
from cozy.evaluation import eval
from cozy.parse import parse

def parse_spec(spec, types={}):
    class TypeInstaller(BottomUpRewriter):
        def visit_EVar(self, e):
            return e.with_type(types.get(e.id, INT))

    ast = parse(spec)
    return TypeInstaller().visit(ast)

def _parse_fragment(fragment, types={}, expr=False):
    """
    Can be used to obtain a parse tree for an arbitrary syntax fragment.
    Include a dictionary of var_name -> type object. By default, they're INTs.

    Doesn't work for things only in target_syntax, like (let x=3 in...).
    """
    spec = "Test: {} foo() {}".format("query" if expr else "op", fragment)
    ast = parse_spec(spec, types)
    return ast.methods[0].ret if expr else ast.methods[0].body

def parse_stm(frag, types={}):
    return _parse_fragment(frag, types, expr=False)

def parse_expr(frag, types={}):
    return _parse_fragment(frag, types, expr=True)

class TestSyntaxTools(unittest.TestCase):
    def test_eall(self):
        assert eval(EAll(()), {})
        for l in range(5):
            print(pprint(EAll([EVar("v{}".format(i)).with_type(BOOL) for i in range(l)])))

    def test_enumerate_fragments_strange_binder_behavior(self):
        xs = EVar("xs").with_type(TBag(INT))
        x = EVar("x").with_type(INT)
        xs_eq_zero = EFilter(xs, ELambda(x, equal(x, ZERO)))
        e = EFilter(xs_eq_zero, ELambda(x,
            equal(
                EFilter(xs, ELambda(x, T)),
                EEmptyList().with_type(xs.type))))
        assert retypecheck(e)
        for ctx in enumerate_fragments(e):
            e = ctx.e
            a = ctx.facts
            if e == T:
                assert not valid(implies(EAll(a), equal(x, ZERO)), validate_model=True), "assumptions at {}: {}".format(pprint(e), "; ".join(pprint(aa) for aa in a))

    def test_enumerate_fragments_bound(self):
        b = EVar("b").with_type(BOOL)
        e = ELet(ZERO, mk_lambda(INT, lambda x: b))
        assert retypecheck(e)
        for ctx in enumerate_fragments(e):
            x = ctx.e
            bound = ctx.bound_vars
            if x == b:
                assert bound == { e.f.arg }, "got {}".format(bound)
            elif x == ZERO:
                assert bound == set(), "got {}".format(bound)

    def test_enumerate_fragments_estatevar(self):
        b = EVar("b").with_type(BOOL)
        e = ELet(ZERO, mk_lambda(INT, lambda x: EStateVar(b)))
        assert retypecheck(e)
        for ctx in enumerate_fragments(e):
            if ctx.e == b:
                bound = ctx.bound_vars
                assert not bound, "EStateVar should reset bound variables, but got {}".format(bound)

    def test_enumerate_fragments_regression_1(self):
        e = EFilter(ESingleton(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))).with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))), ELambda(EVar('_var380').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), EBinOp(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'in', EStateVar(EVar('entries').with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))))).with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))))).with_type(TBool()))).with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))))
        for _ in enumerate_fragments(e):
            pass

    def _do_cse_check(self, e):
        for x in sorted(set(all_exps(e)), key=Exp.size):
            if isinstance(x, ELambda):
                continue
            print("checking {}...".format(pprint(x)))
            y = cse(x)
            if not valid(EBinOp(x, "===", y).with_type(BOOL), do_cse=False):
                print("Bad behavior!")
                print(pprint(x))
                print(pprint(y))
                return False
        return True

    def test_cse(self):
        x = EVar("x").with_type(INT)
        a = EBinOp(x, "+", ONE).with_type(INT)
        e = EBinOp(a, "+", a).with_type(INT)
        e = EBinOp(e, "+", ELet(ONE, ELambda(x, EBinOp(x, "+", x).with_type(INT))).with_type(INT)).with_type(INT)
        assert self._do_cse_check(e)

    def test_cse_regression1(self):
        e = EBinOp(EBinOp(EUnaryOp('unique', EVar('conns').with_type(TList(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))))).with_type(TBool()), 'and', EBinOp(EUnaryOp('unique', EMap(EVar('conns').with_type(TList(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))), ELambda(EVar('_var810294').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))), EGetField(EGetField(EVar('_var810294').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))), 'val').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('ConnectionPool::ConnectionInterface*')))).with_type(TList(TNative('ConnectionPool::ConnectionInterface*')))).with_type(TBool()), 'and', EUnaryOp('unique', EVar('reqs').with_type(TBag(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>')))))))).with_type(TBool())).with_type(TBool())).with_type(TBool()), 'and', EBinOp(EBinOp(EBinOp(EVar('rt').with_type(TNative('Milliseconds')), '==', EVar('refreshRequirement').with_type(TNative('Milliseconds'))).with_type(TBool()), 'and', EBinOp(EVar('c').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))), 'in', EVar('conns').with_type(TList(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))))).with_type(TBool())).with_type(TBool()), 'and', EBinOp(EUnaryOp('all', EMap(EBinOp(EFlatMap(EVar('conns').with_type(TList(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))), ELambda(EVar('_var810294').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))), ESingleton(EVar('_var810294').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))).with_type(TBag(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))))).with_type(TBag(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))), '+', ESingleton(EVar('c').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))).with_type(TBag(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))))).with_type(TBag(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))), ELambda(EVar('_var810294').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))), EUnaryOp('all', EMap(EBinOp(EFlatMap(EVar('conns').with_type(TList(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))), ELambda(EVar('_var810294').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))), ESingleton(EVar('_var810294').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))).with_type(TBag(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))))).with_type(TBag(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))), '+', ESingleton(EVar('c').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))).with_type(TBag(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))))).with_type(TBag(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))), ELambda(EVar('_var810295').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))), EBinOp(EUnaryOp('not', EBinOp(EVar('_var810294').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))), '==', EVar('_var810295').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))))).with_type(TBool())).with_type(TBool()), 'or', EBinOp(EGetField(EVar('_var810294').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))), 'val').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool())))), '==', EGetField(EVar('_var810295').with_type(THandle('Connection', TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))), 'val').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('HostAndPort')), ('conn_iface', TNative('ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('Date_t')), ('conn_returned', TNative('Date_t')), ('conn_dropped', TBool()))))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TBool()))).with_type(TBool()))).with_type(TBag(TBool()))).with_type(TBool()), 'and', EUnaryOp('all', EMap(EFlatMap(EVar('reqs').with_type(TBag(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>'))))))), ELambda(EVar('_var810300').with_type(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>')))))), ESingleton(EVar('_var810300').with_type(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>'))))))).with_type(TBag(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>'))))))))).with_type(TBag(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>'))))))), ELambda(EVar('_var810300').with_type(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>')))))), EUnaryOp('all', EMap(EFlatMap(EVar('reqs').with_type(TBag(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>'))))))), ELambda(EVar('_var810300').with_type(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>')))))), ESingleton(EVar('_var810300').with_type(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>'))))))).with_type(TBag(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>'))))))))).with_type(TBag(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>'))))))), ELambda(EVar('_var810301').with_type(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>')))))), EBinOp(EUnaryOp('not', EBinOp(EVar('_var810300').with_type(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>')))))), '==', EVar('_var810301').with_type(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>'))))))).with_type(TBool())).with_type(TBool()), 'or', EBinOp(EGetField(EVar('_var810300').with_type(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>')))))), 'val').with_type(TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>'))))), '==', EGetField(EVar('_var810301').with_type(THandle('Request', TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>')))))), 'val').with_type(TRecord((('rq_expiration', TNative('Date_t')), ('rq_host', TNative('HostAndPort')), ('rq_callback', TNative('std::unique_ptr<ConnectionPool::GetConnectionCallback>')))))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TBool()))).with_type(TBool()))).with_type(TBag(TBool()))).with_type(TBool())).with_type(TBool())).with_type(TBool())).with_type(TBool())
        assert self._do_cse_check(e)

    def test_fvs_depth(self):
        e = ZERO
        for i in range(500):
            e = ECond(EBinOp(e, "<=", ONE), ONE, ZERO).with_type(INT)
        res = free_vars(e)

    def test_fvs(self):
        e = EBinOp(EMapGet(EStateVar(EMakeMap2(EVar('l').with_type(TBag(INT)), ELambda(EVar('_var111').with_type(INT), EBinOp(EVar('_var111').with_type(INT), 'in', EVar('l').with_type(TBag(INT))).with_type(BOOL))).with_type(TMap(INT, BOOL))).with_type(TMap(INT, BOOL)), EVar('n').with_type(INT)).with_type(BOOL), '==', EBinOp(EVar('_var111').with_type(INT), 'in', EVar('l').with_type(TBag(INT))).with_type(BOOL)).with_type(BOOL)
        print(pprint(e))
        print(free_vars(e))
        assert free_vars(e) == OrderedSet([EVar('l').with_type(TBag(INT)), EVar('n').with_type(INT), EVar('_var111').with_type(INT)])

    def test_recursive_adt_repr(self):
        e = EStateVar(None)
        e.e = e
        print(repr(e))
        assert repr(e) == "EStateVar(<<recursive>>)"

    def test_var_under_estatevar(self):
        # wow, very tricky!
        # EStateVar(...) needs to be "separable" from the parent, so bound vars
        # get cleared.  Thus, if EStateVar(x) appears somewhere, then `x` is
        # is free, even if it appears in e.g. \x -> EStateVar(x).
        x = EVar("x").with_type(INT)
        e = EUnaryOp(UOp.Exists, EFilter(ESingleton(ONE), ELambda(x, EStateVar(EEq(x, ZERO)))))
        print(pprint(e))
        assert retypecheck(e)
        assert x in free_vars(e), free_vars(e)
        sub = subst(e, {"x":ZERO})
        assert sub == EUnaryOp(UOp.Exists, EFilter(ESingleton(ONE), ELambda(x, EStateVar(EEq(ZERO, ZERO))))), pprint(sub)

    def test_replace_works(self):
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        z = EVar("z").with_type(INT)
        e1 = ELambda(y, x)
        e2 = replace(e1, x, z)
        assert e2 == ELambda(y, z), pprint(e2)

    def test_replace_safety(self):
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        z = EVar("z").with_type(INT)
        e1 = ELambda(y, y)
        e2 = replace(e1, y, x)
        assert e1 == e2, pprint(e2)

    def test_replace_alpha_renaming(self):
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        z = EVar("z").with_type(INT)
        e1 = ELambda(y, x)
        e2 = replace(e1, x, y)
        assert alpha_equivalent(
            e2,
            ELambda(z, y)), pprint(e2)

    def test_query_fvs(self):
        fvs = free_vars(Query('__isDistinct', 'public', [('startOffset', TInt())], [], EBinOp(EVar('startOffset').with_type(TInt()), '>=', EArgMax(EMap(EMap(EFilter(EVar('tokens').with_type(TBag(TTuple((TInt(), TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool()))))))), ELambda(EVar('t').with_type(TTuple((TInt(), TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool())))))), EGetField(ETupleGet(EVar('t').with_type(TTuple((TInt(), TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool())))))), 1).with_type(TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool())))), 'important').with_type(TBool()))).with_type(TBag(TTuple((TInt(), TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool()))))))), ELambda(EVar('t').with_type(TTuple((TInt(), TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool())))))), EVar('t').with_type(TTuple((TInt(), TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool())))))))).with_type(TBag(TTuple((TInt(), TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool()))))))), ELambda(EVar('tok').with_type(TTuple((TInt(), TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool())))))), EGetField(ETupleGet(EVar('tok').with_type(TTuple((TInt(), TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool())))))), 1).with_type(TRecord((('score', TFloat()), ('startOffset', TInt()), ('endOffset', TInt()), ('important', TBool())))), 'endOffset').with_type(TInt()))).with_type(TBag(TInt())), ELambda(EVar('x').with_type(TInt()), EVar('x').with_type(TInt()))).with_type(TInt())).with_type(TBool()), ""))
        assert EVar("startOffset") not in fvs

    def test_pickling(self):
        import pickle
        e = EVar("foo").with_type(INT)
        orig_hash = hash(e)
        ee = pickle.loads(pickle.dumps(e))
        assert not hasattr(ee, "_hash") # hash code should not be saved, since it is different each time Python is invoked
        assert e == ee
        assert orig_hash == hash(ee)
        assert e.type == ee.type

    def test_stm_fvs(self):
        use_x = SCall(ONE, "f", (EVar("x"),))
        assert list(free_vars(SDecl("x", EVar("x")))) == [EVar("x")]
        assert list(free_vars(SSeq(
            SDecl("x", ONE),
            use_x))) == []
        assert list(free_vars(SIf(T, SDecl("x", ONE), SNoOp()))) == []
        assert list(free_vars(SSeq(
            SIf(T, SDecl("x", ONE), SNoOp()),
            use_x))) == [EVar("x")]
        assert list(free_vars(SForEach(EVar("x"), EEmptyList(), use_x))) == []
        assert list(free_vars(SSeq(SForEach(EVar("x"), EEmptyList(), use_x), use_x))) == [EVar("x")]
        assert list(free_vars(SEscapableBlock("label", SDecl("x", ONE)))) == []
        assert list(free_vars(SWhile(T, SDecl("x", ONE)))) == []
        assert list(free_vars(SMapUpdate(T, T, EVar("x"), SSeq(SDecl("y", ONE), use_x)))) == []

    def test_deep_copy(self):
        e1 = ETuple((EVar("x"), EBinOp(EVar("x"), "+", EVar("y"))))
        e2 = deep_copy(e1)
        assert e1 == e2
        assert e1 is not e2
        assert e1.es is not e2.es
        assert e1.es[0] is not e2.es[0]
        assert e1.es[1] is not e2.es[1]
        assert e1.es[1].e1 is not e2.es[1].e1
        assert e1.es[1].e2 is not e2.es[1].e2

    def test_shallow_copy(self):
        e1 = ETuple((EVar("x"), EBinOp(EVar("x"), "+", EVar("y"))))
        e2 = shallow_copy(e1)
        assert e1 == e2
        assert e1 is not e2
        assert e1.es is e2.es

    def test_double_bound(self):
        xs = EVar("xs").with_type(INT_BAG)
        ys = EVar("ys").with_type(INT_BAG)
        x = EVar("x").with_type(INT)
        e = EMap(xs, ELambda(x, EMap(ys, ELambda(x, x))))
        assert retypecheck(e)
        found = False
        for ctx in enumerate_fragments(e):
            facts = EAll(ctx.facts)
            print("{} | {}".format(pprint(ctx.e), pprint(facts)))
            if ctx.e == x:
                found = True
                assert valid(EImplies(facts, EIn(x, ys)))
                assert not valid(EImplies(facts, EIn(x, xs)))
        assert found

    def test_self_bound(self):
        xs1 = EVar("xs").with_type(INT_BAG)
        xs2 = EVar("xs").with_type(INT)
        e = EMap(xs1, ELambda(xs2, xs2))
        assert retypecheck(e)
        found = False
        for ctx in enumerate_fragments(e):
            found = found or ctx.e == xs2
            assert not ctx.facts
        assert found

    def test_break_conj(self):
        x, y, z = [fresh_var(BOOL) for i in range(3)]
        e = EBinOp(
            EBinOp(EBinOp(EBinOp(x, BOp.And, y), BOp.Or, z), BOp.And, x), BOp.And,
            EBinOp(x, BOp.And, y))
        assert list(break_conj(e)) == [EBinOp(EBinOp(x, BOp.And, y), BOp.Or, z), x, x, y]

    def test_break_seq(self):
        x, y, z = [SNoOp() for i in range(3)]
        e = SSeq(SSeq(x, y), SSeq(y, z))
        l = list(break_seq(e))
        assert len(l) == 4
        assert l[0] is x
        assert l[1] is y
        assert l[2] is y
        assert l[3] is z

    def test_get_modified_var(self):
        htype = THandle("IntPtr", INT)

        stm = parse_stm("h.val = 2;", dict(h=htype))
        assert retypecheck(stm)
        mod, handle_type = get_modified_var(stm)
        assert handle_type is not None
        assert isinstance(handle_type, THandle)

        # Reassigning a handle should not get a handle type back.

        stm = parse_stm("h = g;", dict(h=htype, g=htype))
        assert retypecheck(stm)
        mod, handle_type = get_modified_var(stm)
        assert handle_type is None

        stm = parse_stm("foo.bar.val = 2;",
            dict(
                foo=TRecord([("bar", THandle("IntPtr", INT))]),
                bar=htype))

        assert retypecheck(stm)
        mod, handle_type = get_modified_var(stm)
        print(mod)
        assert handle_type is not None
        assert isinstance(handle_type, THandle)

        stm = parse_stm("foo.bar = 2;",
            dict(foo=TRecord([("bar", INT)]), bar=INT))
        assert retypecheck(stm)
        mod, handle_type = get_modified_var(stm)
        print(mod)
        assert handle_type is None

"""
Elimination tests.
"""


class TestElimination(unittest.TestCase):
    def test_y_plus_1(self):
        e = parse_expr(
            """
            (y + 1)
            +
            (y + 1)
            """
        )

        assert retypecheck(e)
        print(pprint(e))

        e3 = cse_replace(e)
        newForm = pprint(e3)
        print(newForm)

        assert newForm.count("y + 1") == 1

    def test_y_plus_1_elambda(self):
        """
        (
            (y + 1) + (z + 1)
            +
            (let y = 9 in ( (y + 1) + (z + 1) + (y + 1) ))
        ) +
        (z + 1)
        """

        y = EVar("y").with_type(INT)
        yp1 = EBinOp(y, "+", ENum(1).with_type(INT))

        z = EVar("z").with_type(INT)
        zp1 = EBinOp(z, "+", ENum(1).with_type(INT))

        NINE = ENum(9).with_type(INT)

        e = EBinOp(
                EBinOp(
                    EBinOp(yp1, "+", zp1),
                    "+",
                    ELet(NINE,
                        ELambda(
                            EVar("y").with_type(INT),
                            EBinOp(
                                EBinOp(yp1, "+", zp1),
                                "+",
                                yp1
                            )
                        )
                    )
                ),
                "+",
                zp1)

        assert retypecheck(e)
        print(pprint(e))

        e3 = cse_replace(e)
        newForm = pprint(e3)
        print(newForm)

        assert newForm.count("y + 1") == 2
        assert newForm.count("z + 1") == 1

    def test_y_plus_1_elambda_z_post(self):
        """
        (
            (y + 1)
            +
            (let y = 9 in ( (y + 1) + (z + 1) + (y + 1) ))
        ) +
        (z + 1)
        """
        y = EVar("y").with_type(INT)
        yp1 = EBinOp(y, "+", ENum(1).with_type(INT))

        z = EVar("z").with_type(INT)
        zp1 = EBinOp(z, "+", ENum(1).with_type(INT))

        NINE = ENum(9).with_type(INT)

        e = EBinOp(
                EBinOp(
                    yp1,
                    "+",
                    ELet(NINE,
                        ELambda(
                            EVar("y").with_type(INT),
                            EBinOp(
                                EBinOp(yp1, "+", zp1),
                                "+",
                                yp1
                            )
                        )
                    )
                ),
                "+",
                zp1)

        assert retypecheck(e)
        print(pprint(e))

        e3 = cse_replace(e)
        newForm = pprint(e3)
        print(newForm)

        assert newForm.count("z + 1") == 1

    def test_y_plus_1_3x(self):
        e = parse_expr(
            """
            (
                (y + 1)
                +
                (z + 1)
            )
            +
                (y + 1)
            """
        )

        assert retypecheck(e)
        print(pprint(e))

        e3 = cse_replace(e)
        newForm = pprint(e3)
        print(newForm)

        assert newForm.count("y + 1") == 1
        assert newForm.count("z + 1") == 1

    def test_cse_2_expr(self):
        e2 = parse_expr(
            """
            (x < y)
                ? ((x < y) ? x + y : x + y)
                : ((x < y) ? x + y : x + y)
            """
        )

        assert retypecheck(e2)
        print(pprint(e2))

        e2 = cse_replace(e2)
        assert retypecheck(e2)
        print(pprint(e2))
        print(e2)

        newForm = pprint(e2)
        assert newForm.count("x < y") == 1
        assert newForm.count("x + y") == 1

    def test_cse_2_exp_letscope(self):
        """
        (y + 2)
        +
        (let y = 1 in (y + 2))
        +
        (y + 2)

        The expression in the let should not be CSE'd. The outer ones should.
        """

        y = EVar("y").with_type(INT)
        yp2 = EBinOp(y, "+", ENum(2).with_type(INT))

        s = EBinOp(
                EBinOp(
                    yp2,
                    "+",
                    ELet(ONE, ELambda(y, yp2))),
                "+",
                yp2
            )

        assert retypecheck(s)
        print(pprint(s))

        s = cse_replace(s)
        print(pprint(s))
        print(s)

        assert "let y = 1 in (y + 2)" in pprint(s)
        assert isinstance(s, ELet)

    def test_cse_2_no_elim_lambda(self):
        """
        Bunch of different expressions should not get their ELambdas separated from them.
        """
        INTLIST = TList(INT)

        e1 = EFilter(ESingleton(ONE), ELambda(EVar("x").with_type(INT), EBinOp(EVar("x"), ">", ENum(2).with_type(INT))))
        e = ECond(EBinOp(EVar("x").with_type(INT), "<", EVar("y").with_type(INT)), e1, e1)

        # TODO: get refreshed on the ELambda restrictions.
        """
        s = seq((
            SAssign(EVar("a").with_type(INTLIST), e),
        ))

        assert retypecheck(s)
        print(pprint(s))
        print("###")
        s = _cse(s)
        print(pprint(s))
        assert False
        """
        assert isinstance(e1.p, ELambda)

        e1 = ELet(EVar("y").with_type(INT), ELambda(EVar("x").with_type(INT), EBinOp(EVar("x"), "+", ENum(2).with_type(INT))))
        e = ECond(EBinOp(EVar("x").with_type(INT), "<", EVar("y").with_type(INT)), e1, e1)
        assert retypecheck(e)
        e = cse_replace(e)

        assert isinstance(e1.f, ELambda)

        for t in (EMap, EArgMax, EArgMin):
            e1 = t(ESingleton(ONE), ELambda(EVar("x").with_type(INT), EBinOp(EVar("x"), "+", ENum(2).with_type(INT))))
            e = ECond(EBinOp(EVar("x").with_type(INT), "<", EVar("y").with_type(INT)), e1, e1)
            assert retypecheck(e)
            e = cse_replace(e)
            assert isinstance(e1.f, ELambda)

    def test_cse_2_stm_simple(self):
        s = parse_stm(
            """
            x = y + 2;
            z = y + 2;
            """
        )

        assert retypecheck(s)

        print(pprint(s))
        s2 = cse_replace(s)
        new_form = pprint(s2)
        print(new_form)

        assert new_form.count("y + 2") == 1

    def test_cse_2_stm_long_exp(self):
        s = parse_stm(
            """
            x = a+1 + b+2 + c+3;
            z = a+1 + b+2 + c+3 + d+4;
            """,
            dict(a=INT, b=INT, c=INT, d=INT, x=INT, z=INT)
        )

        assert retypecheck(s)

        print(pprint(s))
        s2 = cse_replace(s)
        new_form = pprint(s2)
        print(new_form)

        assert new_form.count("var _tmp") == 1

    def test_cse_2_stm_expr_if(self):
        s = parse_stm(
            """
            if (x < y) {
                _var507 = (x < y) ? (x + y) : (x + y);
            }
            """
        )

        assert retypecheck(s)

        print(pprint(s))
        s2 = cse_replace(s)
        newForm = pprint(s2)
        print(newForm)

        assert newForm.count("x < y") == 1
        assert newForm.count("x + y") == 1

    def test_cse_2_stm_seq_assign_kill_basic(self):
        s = parse_stm(
            """
            x = y + 2;
            y = 1;
            z = y + 2;
            """
        )

        # The y=1 statement should cause a temp to not be created.

        assert retypecheck(s)
        print(pprint(s))

        s2 = cse_replace(s)
        newForm = pprint(s2)
        print(newForm)

        assert newForm.count("y + 2") == 2

    def test_cse_2_stm_seq_assign_kill_1(self):
        s = parse_stm(
            """
            b = z + 4;
            x = y + 2;
            y = x;
            g = y + 2;
            q = z + 4;
            """
        )

        # The y=x statement should cause a temp to not be created.

        assert retypecheck(s)
        print(pprint(s))

        s2 = cse_replace(s)
        newForm = pprint(s2)
        print(newForm)

        assert newForm.count("y + 2") == 2
        assert newForm.count("z + 4") == 1

    def test_cse_2_stm_seq_assign_kill_deep(self):
        s = parse_stm(
            """
            n = h + 5;
            q = y + 2;
            y = h + 5;
            x = y + 2;
            z = y + 2;
            """
        )

        assert retypecheck(s)
        print(pprint(s))

        s2 = cse_replace(s)
        newForm = pprint(s2)
        print("========")
        print(newForm)

        assert newForm.count("y + 2") == 2
        assert newForm.count("h + 5") == 1

    def test_cse_2_stm_if(self):
        s = parse_stm(
            """
            if (foo) {
                x = y + 2;
            } else {
                z = y + 2;
            }
            """,
            dict(foo=BOOL)
        )

        assert retypecheck(s)

        print(pprint(s))
        s2 = cse_replace(s)
        new_form = pprint(s2)

        print(new_form)
        assert new_form.count("y + 2") == 1

    def test_cse_2_stm_if_kill(self):
        s = parse_stm(
            """
            if (foo) {
                x = y + 2;
                y = 9;
                z = y + 2;
            }
            """,
            dict(foo=BOOL)
        )

        assert retypecheck(s)

        print(pprint(s))
        s2 = cse_replace(s)
        new_form = pprint(s2)

        print(new_form)
        assert new_form.count("y + 2") == 2

    def test_cse_2_stm_if_both_branches(self):
        s = parse_stm(
            """
            if (foo) {
                x = y + 2;
                g = y + 2;
            } else {
                z = y + 2;
            }
            """,
            dict(foo=BOOL)
        )

        assert retypecheck(s)

        print(pprint(s))
        s2 = cse_replace(s)
        new_form = pprint(s2)

        print(new_form)
        assert new_form.count("y + 2") == 1

    def test_cse_2_stm_foreach_scope(self):
        """
        x = y + 2

        for (y in [1,2]) {
            z = y + 2
        }

        q = y + 2

        The for-loop body scope should not get CSE'd. The outer two *should*.
        """
        yp2 = EBinOp(EVar("y").with_type(INT), "+", ENum(2).with_type(INT)).with_type(INT)

        s = seq((
            SAssign(EVar("x").with_type(INT), yp2),
            SForEach(EVar("y").with_type(INT), ESingleton(ONE),
                SAssign(EVar("z").with_type(INT), yp2),
                ),
            SAssign(EVar("q").with_type(INT), yp2),
        ))

        assert retypecheck(s)

        print(pprint(s))
        s2 = cse_replace(s)
        new_form = pprint(s2)
        print(new_form)
        print(s2)

        assert new_form.count("y + 2") == 2

    def test_cse_handle_sametype_changeval(self):
        spec = parse_spec(
            """
            Spec:
                handletype IntPtr = Int

                op foo()
                    /*
                    Assigning to a handle type should invalidate ALL other vars of the same handle type.
                    */
                    h.val = 0;

                    a = h.val + 7;
                    b = h.val + 7;

                    // Changing g.val should invalidate h since they have the same handle type.

                    g.val = 1;

                    c = h.val + 7;
                    d = h.val + 7;
            """,
            dict(a=INT, b=INT, c=INT, d=INT,
                h=THandle("IntPtr", INT), g=THandle("IntPtr", INT))
        )

        assert retypecheck(spec)

        print(pprint(spec))
        spec2 = cse_replace_spec(spec)
        new_form = pprint(spec2)
        print(new_form)
        assert new_form.count("+ 7") == 2

    def test_cse_handle_sametype_changeident(self):
        spec = parse_spec(
            """
            Spec:
                handletype IntPtr = Int

                op foo2()
                    /*
                    ...but reassigning the handle itself (not its val) should act
                    as just reassigning a non-handle var.
                    */

                    h.val = 0;

                    a = h.val + 7;
                    b = h.val + 7;
                    q = g.val + 6;
                    r = g.val + 6;

                    g = i;

                    c = h.val + 7;
                    d = h.val + 7;
                    s = g.val + 6;
                    t = g.val + 6;
            """,
            dict(a=INT, b=INT, c=INT, d=INT,
                q=INT, r=INT, s=INT, t=INT,
                h=THandle("IntPtr", INT),
                g=THandle("IntPtr", INT),
                i=THandle("IntPtr", INT))
        )

        assert retypecheck(spec)
        print(pprint(spec))

        spec2 = cse_replace_spec(spec)
        new_form = pprint(spec2)
        print(new_form)
        assert new_form.count("+ 7") == 1
        assert new_form.count("+ 6") == 2

    def test_cse_handle_difftype(self):
        spec = parse_spec(
            """
            Spec:
                handletype IntPtr = Int
                handletype IntPtr2 = Int // a diff't type.

                op foo()
                    h.val = 0;

                    a = h.val + 7;
                    b = h.val + 7;
                    c = h.val + 7;
                    d = h.val + 7;

                    // j is of a diff't handle type. Shouldn't bother h's eliminations.
                    j.val = 2;

                    e = h.val + 7;
                    f = h.val + 7;
            """,
            dict(a=INT, b=INT, c=INT, d=INT, e=INT, f=INT,
                h=THandle("IntPtr", INT),
                j=THandle("IntPtr2", INT))
        )

        assert retypecheck(spec)

        spec2 = cse_replace_spec(spec)
        new_form = pprint(spec2)
        print(new_form)
        assert new_form.count("+ 7") == 1

    def __test_cse_2(self):
        op = Op('addElement', [('x', TInt())], [], SSeq(SSeq(SSeq(SDecl('_name5771', ECond(EBinOp(EBinOp(EBinOp(EUnaryOp('len', EVar('_var2027').with_type(TBag(TInt()))).with_type(TInt()), '+', EUnaryOp('len', EVar('_var2027').with_type(TBag(TInt()))).with_type(TInt())).with_type(TInt()), '<', ENum(5).with_type(TInt())).with_type(TBool()), 'or', EBinOp(EBinOp(EUnaryOp('len', EVar('_var2027').with_type(TBag(TInt()))).with_type(TInt()), '+', EUnaryOp('len', EVar('_var2027').with_type(TBag(TInt()))).with_type(TInt())).with_type(TInt()), '>', ENum(7).with_type(TInt())).with_type(TBool())).with_type(TBool()), EBinOp(EVar('_var2027').with_type(TBag(TInt())), '-', EBinOp(EVar('_var2027').with_type(TBag(TInt())), '+', ESingleton(EVar('x').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt())), EBinOp(EVar('_var2027').with_type(TBag(TInt())), '-', EVar('_var2027').with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt()))), SDecl('_name5772', ECond(EBinOp(EBinOp(EBinOp(EUnaryOp('len', EVar('_var2027').with_type(TBag(TInt()))).with_type(TInt()), '+', EUnaryOp('len', EVar('_var2027').with_type(TBag(TInt()))).with_type(TInt())).with_type(TInt()),'<', ENum(5).with_type(TInt())).with_type(TBool()), 'or', EBinOp(EBinOp(EUnaryOp('len', EVar('_var2027').with_type(TBag(TInt()))).with_type(TInt()), '+', EUnaryOp('len', EVar('_var2027').with_type(TBag(TInt()))).with_type(TInt())).with_type(TInt()), '>', ENum(7).with_type(TInt())).with_type(TBool())).with_type(TBool()), EBinOp(EBinOp(EVar('_var2027').with_type(TBag(TInt())), '+', ESingleton(EVar('x').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', EVar('_var2027').with_type(TBag(TInt()))).with_type(TBag(TInt())), EBinOp(EVar('_var2027').with_type(TBag(TInt())), '-', EVar('_var2027').with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt())))), SAssign(EVar('_var507').with_type(TInt()), ECond(EBinOp(EBinOp(EBinOp(EUnaryOp('len', EEmptyList().with_type(TBag(TInt()))).with_type(TInt()), '+', EUnaryOp('len', EEmptyList().with_type(TBag(TInt()))).with_type(TInt())).with_type(TInt()), '<', ENum(5).with_type(TInt())).with_type(TBool()), 'or', EBinOp(ENum(5).with_type(TInt()), '>', ENum(7).with_type(TInt())).with_type(TBool())).with_type(TBool()), EBinOp(EUnaryOp('len', EVar('_var2027').with_type(TBag(TInt()))).with_type(TInt()), '+', ENum(1).with_type(TInt())).with_type(TInt()), EUnaryOp('len', EEmptyList().with_type(TBag(TInt()))).with_type(TInt())).with_type(TInt()))), SSeq(SForEach(EVar('_var2988').with_type(TInt()), EVar('_name5771').with_type(TBag(TInt())), SCall(EVar('_var2027').with_type(TBag(TInt())), 'remove', [EVar('_var2988').with_type(TInt())])), SForEach(EVar('_var2988').with_type(TInt()), EVar('_name5772').with_type(TBag(TInt())), SCall(EVar('_var2027').with_type(TBag(TInt())), 'add', [EVar('_var2988').with_type(TInt())])))), '')
        spec = Spec("foo", (), (), (), (), [op], "", "", "")

        assert retypecheck(spec)

        print(pprint(spec))
        print(pprint(cse_replace_spec(spec)))
        assert False

class TestConditionals(unittest.TestCase):
    def test_usage_finder(self):
        y = EVar("y").with_type(INT)
        f = ConditionalUseFinder(y)

        assert USED_ALWAYS == f.visit(parse_expr("y + 2"))
        assert USED_ALWAYS == f.visit(parse_expr("y"))
        assert USED_ALWAYS == f.visit(parse_expr("-y"))
        assert USED_ALWAYS == f.visit(parse_expr("-(-y)"))
        assert USED_ALWAYS == f.visit(parse_expr("y + y + 2"))
        assert USED_ALWAYS == f.visit(parse_expr("(x + y) + (x + 2)"))

        assert USED_ALWAYS == f.visit(parse_expr("y < 2 ? 2 : 3"))
        assert USED_ALWAYS == f.visit(parse_expr("z > x ? y : y+9"))
        assert USED_ALWAYS == f.visit(parse_expr("y > 0 ? y : y+1"))
        assert USED_ALWAYS == f.visit(parse_expr("y > 0 ? y : (y < 2 ? y : 0)"))

        assert USED_SOMETIMES == f.visit(parse_expr("z > x ? y : 3"))
        assert USED_SOMETIMES == f.visit(parse_expr("z > x ? 2 : y"))
        assert USED_SOMETIMES == f.visit(parse_expr("q + (z > x ? 2 : y)"))
        assert USED_SOMETIMES == f.visit(parse_expr("x > 0 ? y : (x < 2 ? y : 0)"))
        assert USED_SOMETIMES == f.visit(parse_expr("x > 0 ? 1 : (x < 2 ? y : 0)"))
        assert USED_SOMETIMES == f.visit(parse_expr("x > 0 ? 1 : (x < 2 ? 2 : y)"))
        assert USED_SOMETIMES == f.visit(parse_expr("(x>0?x:y) > 0 ? 1 : 2"))

        assert USED_NEVER == f.visit(parse_expr("z > x ? z : x"))
        assert USED_NEVER == f.visit(parse_expr("q + (z > x ? z : x)"))
        assert USED_NEVER == f.visit(parse_expr("(x + z) + (x + z)"))
        assert USED_NEVER == f.visit(parse_expr("6"))
        assert USED_NEVER == f.visit(parse_expr("x"))

    def test_let_rewrite(self):
        """
        let y = 1 in ( (x > z) ? (y + 2) : (z + 2) )
        """
        y = EVar("y").with_type(INT)
        x = EVar("x").with_type(INT)
        z = EVar("z").with_type(INT)

        yp2 = EBinOp(y, "+", ENum(2).with_type(INT))
        zp2 = EBinOp(z, "+", ENum(2).with_type(INT))

        cond = ECond(EGt(x, z), yp2, zp2)
        s = ELet(ONE, ELambda(y, cond))

        assert retypecheck(s)
        print(pprint(s))
        s = fix_conditionals(s)
        new_form = pprint(s)
        print(new_form)
        assert isinstance(s, ECond)
        assert "let y = 1 in (y + 2)" in new_form

        # now in the else block

        cond = ECond(EGt(x, z), zp2, yp2)
        s = ELet(ONE, ELambda(y, cond))

        assert retypecheck(s)
        print(pprint(s))
        s = fix_conditionals(s)
        new_form = pprint(s)
        print(new_form)
        assert isinstance(s, ECond)
        assert "let y = 1 in (y + 2)" in new_form

    def test_let_rewrite_into_binop(self):
        """
        let y = 1 in f + (x > z) ? (y + 2) : (z + 2)
        """
        f = EVar("f").with_type(INT)
        y = EVar("y").with_type(INT)
        x = EVar("x").with_type(INT)
        z = EVar("z").with_type(INT)

        yp2 = EBinOp(y, "+", ENum(2).with_type(INT))
        zp2 = EBinOp(z, "+", ENum(2).with_type(INT))

        cond = ECond(EGt(x, z), yp2, zp2)
        f_plus_cond = EBinOp(f, "+", cond)
        s = ELet(ONE, ELambda(y, f_plus_cond))

        assert retypecheck(s)
        print(pprint(s))
        s = fix_conditionals(s)
        new_form = pprint(s)
        print(new_form)
        assert isinstance(s, type(f_plus_cond))
        assert "let y = 1 in (y + 2)" in new_form

    def __test_let_rewrite_past_let(self):
        """
        let y = 1 in (
            let x = (z>0?y+2:z+2) in (
                (x > z) ? (y + 2) : (z + 2)
            )
        )
        """
        y = EVar("y").with_type(INT)
        x = EVar("x").with_type(INT)
        z = EVar("z").with_type(INT)

        yp2 = EBinOp(y, "+", ENum(2).with_type(INT))
        zp2 = EBinOp(z, "+", ENum(2).with_type(INT))
        ypz = EBinOp(TWO, "+", z)

        cond_zy = ECond(EGt(z, ZERO), yp2, zp2)
        cond2 = ECond(EGt(x, z), yp2, zp2)
        let_inner = ELet(cond_zy, ELambda(x, cond2))
        s = ELet(ONE, ELambda(y, let_inner))

        assert retypecheck(s)
        print(pprint(s))
        s = fix_conditionals(s)
        new_form = pprint(s)
        print(new_form)
        assert False

    def test_let_unused(self):
        """
        let y = 1 in ( (x > z) ? (z + 3) : (z + 2) )
        """
        y = EVar("y").with_type(INT)
        x = EVar("x").with_type(INT)
        z = EVar("z").with_type(INT)

        zp3 = EBinOp(z, "+", ENum(3).with_type(INT))
        zp2 = EBinOp(z, "+", ENum(2).with_type(INT))

        cond = ECond(EGt(x, z), zp3, zp2)
        s = ELet(ONE, ELambda(y, cond))

        assert retypecheck(s)
        print(pprint(s))

        s = fix_conditionals(s)
        new_form = pprint(s)
        print(new_form)
        print(s)

        assert isinstance(s, ECond)
        assert "let y" not in new_form

    def __test_localize_if_(self):
        s = parse_stm(
            """
            a = 2;

            if (foo) {
                // <--- a=2 should get moved here.
                b = a;
            } else {
                b = g;
            }
            """
        )

        assert retypecheck(s)
        print(pprint(s))

        #s = cse_replace(s)
        print(pprint(s))
        print(s)

        # assert "let y = 1 in (y + 2)" in pprint(s)

        assert isinstance(s, EBinOp)
