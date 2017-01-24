import unittest

from cozy.solver import satisfy
from cozy.typecheck import typecheck
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, equal

zero = ENum(0).with_type(TInt())
one  = ENum(1).with_type(TInt())

class TestSolver(unittest.TestCase):

    def test_the_empty(self):
        x = EEmptyList().with_type(TBag(TInt()))
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TMaybe(TInt())), "==", EJust(one)).with_type(TBool())) is None
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TMaybe(TInt())), "==", EJust(zero)).with_type(TBool())) is None

    def test_the(self):
        x = ESingleton(zero).with_type(TBag(TInt()))
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TMaybe(TInt())), "==", EJust(zero)).with_type(TBool())) is not None
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TMaybe(TInt())), "==", EJust(one)).with_type(TBool())) is None

    def test_the_acts_like_first(self):
        x = EBinOp(ESingleton(zero).with_type(TBag(TInt())), "+", ESingleton(one).with_type(TBag(TInt()))).with_type(TBag(TInt()))
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TMaybe(TInt())), "==", EJust(zero)).with_type(TBool())) is not None
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TMaybe(TInt())), "==", EJust(one)).with_type(TBool())) is None

    def test_the(self):
        tgroup = TRecord((('name', TString()), ('description', TString()), ('rosterMode', TEnum(('NOBODY', 'ONLY_GROUP', 'EVERYBODY'))), ('groupList', TBag(TString())), ('members', TBag(TNative('org.xmpp.packet.JID'))), ('administrators', TBag(TNative('org.xmpp.packet.JID')))))
        groups = EVar('groups').with_type(TBag(THandle('groups', tgroup)))
        e = EUnaryOp('not', EBinOp(EUnaryOp('the', groups).with_type(TMaybe(THandle('groups', tgroup))), '==', EUnaryOp('the', EMap(EFilter(groups, ELambda(EVar('g').with_type(THandle('groups', tgroup)), EBinOp(EGetField(EGetField(EVar('g').with_type(THandle('groups', tgroup)), 'val').with_type(tgroup), 'name').with_type(TString()), '==', EVar('name').with_type(TString())).with_type(TBool()))).with_type(TBag(THandle('groups', tgroup))), ELambda(EVar('g').with_type(THandle('groups', tgroup)), EVar('g').with_type(THandle('groups', tgroup)))).with_type(TBag(THandle('groups', tgroup)))).with_type(TMaybe(THandle('groups', tgroup)))).with_type(TBool())).with_type(TBool())
        vars = [EVar('users').with_type(TBag(THandle('users', TRecord((('username', TString()), ('salt', TString()), ('storedKey', TString()), ('serverKey', TString()), ('iterations', TInt()), ('name', TString()), ('email', TString()), ('creationDate', TNative('java.util.Date')), ('modificationDate', TNative('java.util.Date'))))))), EVar('rosterItems').with_type(TBag(THandle('rosterItems', TRecord((('backendId', TLong()), ('user', TString()), ('target', TNative('org.xmpp.packet.JID')), ('nickname', TString()), ('askStatus', TNative('org.jivesoftware.openfire.roster.RosterItem.AskType')), ('recvStatus', TNative('org.jivesoftware.openfire.roster.RosterItem.RecvType'))))))), groups, EVar('name').with_type(TString())]
        errs = typecheck(e, env={ v.id:v.type for v in vars })
        assert not errs
        assert satisfy(e, vars=vars, validate_model=True) is not None

    def test_empty_sum(self):
        x = EVar("x").with_type(TInt())
        model = satisfy(equal(x, EUnaryOp("sum", EEmptyList().with_type(TBag(TInt())))))
        assert model is not None
        assert model[x.id] == 0

    def test_weird_map_get(self):
        employee_type = TRecord((('employee_name', TInt()), ('employer_id', TInt())))
        employer_type = TRecord((('employer_name', TInt()), ('employer_id', TInt())))
        s = EUnaryOp('sum', EMap(EMapGet(EMakeMap(EVar('employers').with_type(TBag(THandle('employers', employer_type))), ELambda(EVar('_var49').with_type(THandle('employers', employer_type)), EGetField(EGetField(EVar('_var49').with_type(THandle('employers', employer_type)), 'val').with_type(employer_type), 'employer_id').with_type(TInt())), ELambda(EVar('_var57').with_type(TBag(THandle('employers', employer_type))), EVar('_var57').with_type(TBag(THandle('employers', employer_type))))).with_type(TMap(TInt(), TBag(THandle('employers', employer_type)))), EVar('employer_name').with_type(TInt())).with_type(TBag(THandle('employers', employer_type))), ELambda(EVar('_var48').with_type(THandle('employers', employer_type)), EGetField(EGetField(EVar('_var48').with_type(THandle('employers', employer_type)), 'val').with_type(employer_type), 'employer_name').with_type(TInt()))).with_type(TBag(TInt()))).with_type(TInt())
        e = EMapGet(EMakeMap(EVar('employees').with_type(TBag(THandle('employees', employee_type))), ELambda(EVar('_var39').with_type(THandle('employees', employee_type)), EGetField(EGetField(EVar('_var39').with_type(THandle('employees', employee_type)), 'val').with_type(employee_type), 'employer_id').with_type(TInt())), ELambda(EVar('_var45').with_type(TBag(THandle('employees', employee_type))), EVar('_var45').with_type(TBag(THandle('employees', employee_type))))).with_type(TMap(TInt(), TBag(THandle('employees', employee_type)))), s).with_type(TBag(THandle('employees', employee_type)))
        satisfy(equal(e, EEmptyList().with_type(e.type)))

    def test_function_extraction(self):
        x = EVar("x").with_type(TNative("Foo"))
        e = ECall("f", [x]).with_type(TBool())
        model = satisfy(e)
        assert "x" in model
        assert "f" in model
        assert model["f"](model["x"]) is True

    def test_symbolic_maps(self):
        x = EVar("x").with_type(TMap(TInt(), TInt()))
        y = EVar("y").with_type(TMap(TInt(), TInt()))
        e = ENot(equal(x, y))
        model = satisfy(e, validate_model=True)
