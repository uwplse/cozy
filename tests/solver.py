import unittest

from cozy.solver import satisfy
from cozy.typecheck import typecheck
from cozy.target_syntax import *

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
