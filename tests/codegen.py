from collections import OrderedDict, defaultdict
import io
import os
import subprocess
import tempfile
import unittest

from cozy.target_syntax import *
from cozy.structures.heaps import *
from cozy.syntax_tools import pprint, mk_lambda, fresh_var
from cozy.codegen import CxxPrinter, JavaPrinter

class TestCodegen(unittest.TestCase):

    def trove_path(self):
        dir = "/tmp"
        path = os.path.join(dir, "trove-3.0.3.jar")
        if not os.path.exists(path):
            subprocess.run(["curl", "-LO", "https://bitbucket.org/trove4j/trove/downloads/trove-3.0.3.tar.gz"], cwd=dir)
            subprocess.run(["tar", "xf", "trove-3.0.3.tar.gz"], cwd=dir)
            subprocess.run(["ln", "3.0.3/lib/trove-3.0.3.jar", path], cwd=dir)
        return path

    def check(self, impl, state_map, share_info, codegen):
        with io.StringIO() as f:
            codegen = codegen(f)
            codegen.visit(impl, state_map, share_info)
            code = f.getvalue()

        ext = "java" if isinstance(codegen, JavaPrinter) else "cpp"
        compile = ["javac"] if isinstance(codegen, JavaPrinter) else ["c++", "-std=c++11", "-w", "-c", "-o", "/dev/null"]
        dir = tempfile.mkdtemp()
        print("Writing impls to {}".format(dir))
        filename = os.path.join(dir, "{}.{}".format(impl.name, ext))
        args = compile + [filename]
        print("Running `{}`".format(" ".join(args)))
        with open(filename, "w") as f:
            f.write(code)
        res = subprocess.run(args)
        assert res.returncode == 0

    def test_regression01(self):
        impl = Spec('MaxBag', [], [], [('_var653', TInt()), ('_var751', TMap(TInt(), TBool())), ('_var1648', TBool()), ('_var2669', TMaxHeap(TInt(), TInt())), ('_var2670', TInt())], (), (Query('get_max', "pubilc", [], (), EVar('_var653').with_type(TInt()), ''), Op('add', [('x', TInt())], [], SSeq(SSeq(SDecl(EVar('_var10457').with_type(TInt()), ECond(EVar('_var1648').with_type(TBool()), EArgMax(EBinOp(ESingleton(EVar('_var653').with_type(TInt())).with_type(TBag(TInt())), '+', ESingleton(EVar('x').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), ELambda(EVar('_var656').with_type(TInt()), EVar('_var656').with_type(TInt()))).with_type(TInt()), EVar('x').with_type(TInt())).with_type(TInt())), SSeq(SDecl(EVar('_var10458').with_type(TInt()), EBinOp(EVar('_var2670').with_type(TInt()), '+', ENum(1).with_type(TInt())).with_type(TInt())), SAssign(EVar('_var653').with_type(TInt()), EVar('_var10457').with_type(TInt())))), SSeq(SSeq(SAssign(EVar('_var1648').with_type(TBool()), EBool(True).with_type(TBool())), SSeq(SCall(EVar('_var2669').with_type(TMaxHeap(TInt(), TInt())), 'remove_all', (EVar('_var2670').with_type(TInt()), EEmptyList().with_type(TBag(TInt())))), SSeq(SCall(EVar('_var2669').with_type(TMaxHeap(TInt(), TInt())), 'add_all', (EVar('_var2670').with_type(TInt()), ESingleton(EVar('x').with_type(TInt())).with_type(TBag(TInt())))), SForEach(EVar('_var4130').with_type(TInt()), EEmptyList().with_type(TBag(TInt())), SCall(EVar('_var2669').with_type(TMaxHeap(TInt(), TInt())), 'update', (EVar('_var4130').with_type(TInt()), EVar('_var4130').with_type(TInt()))))))), SSeq(SAssign(EVar('_var2670').with_type(TInt()), EVar('_var10458').with_type(TInt())), SSeq(SForEach(EVar('_var1131').with_type(TInt()), EEmptyList().with_type(TBag(TInt())), SMapDel(EVar('_var751').with_type(TMap(TInt(), TBool())), EVar('_var1131').with_type(TInt()))), SForEach(EVar('_var1131').with_type(TInt()), ESingleton(EVar('x').with_type(TInt())).with_type(TBag(TInt())), SMapUpdate(EVar('_var751').with_type(TMap(TInt(), TBool())), EVar('_var1131').with_type(TInt()), EVar('_var1132').with_type(TBool()), SAssign(EVar('_var1132').with_type(TBool()), EBool(True).with_type(TBool())))))))), ''), Op('remove', [('x', TInt())], [], SSeq(SSeq(SSeq(SDecl(EVar('_var10459').with_type(TInt()), ECond(EBinOp(EVar('x').with_type(TInt()), '==', EVar('_var653').with_type(TInt())).with_type(TBool()), EHeapPeek2(EVar('_var2669').with_type(TMaxHeap(TInt(), TInt())), EVar('_var2670').with_type(TInt())).with_type(TInt()), EVar('_var653').with_type(TInt())).with_type(TInt())), SDecl(EVar('_var10460').with_type(TInt()), EBinOp(EVar('_var2670').with_type(TInt()), '-', EUnaryOp('len', ECond(EHasKey(EVar('_var751').with_type(TMap(TInt(), TBool())), EVar('x').with_type(TInt())).with_type(TBool()), ESingleton(EVar('x').with_type(TInt())).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TInt())).with_type(TInt()))), SSeq(SDecl(EVar('_var10461').with_type(TBag(TInt())), ECond(EHasKey(EVar('_var751').with_type(TMap(TInt(), TBool())), EVar('x').with_type(TInt())).with_type(TBool()), ESingleton(EVar('x').with_type(TInt())).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt()))), SAssign(EVar('_var653').with_type(TInt()), EVar('_var10459').with_type(TInt())))), SSeq(SSeq(SAssign(EVar('_var1648').with_type(TBool()), EBinOp(EBinOp(EVar('_var2670').with_type(TInt()), '-', ECond(EHasKey(EVar('_var751').with_type(TMap(TInt(), TBool())), EVar('x').with_type(TInt())).with_type(TBool()), ENum(1).with_type(TInt()), ENum(0).with_type(TInt())).with_type(TInt())).with_type(TInt()), '>', ENum(0).with_type(TInt())).with_type(TBool())), SSeq(SCall(EVar('_var2669').with_type(TMaxHeap(TInt(), TInt())), 'remove_all', (EVar('_var2670').with_type(TInt()), ECond(EHasKey(EVar('_var751').with_type(TMap(TInt(), TBool())), EVar('x').with_type(TInt())).with_type(TBool()), ESingleton(EVar('x').with_type(TInt())).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt())))), SSeq(SCall(EVar('_var2669').with_type(TMaxHeap(TInt(), TInt())), 'add_all', (EBinOp(EVar('_var2670').with_type(TInt()), '-', EUnaryOp('len', ECond(EHasKey(EVar('_var751').with_type(TMap(TInt(), TBool())), EVar('x').with_type(TInt())).with_type(TBool()), ESingleton(EVar('x').with_type(TInt())).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TInt())).with_type(TInt()), EEmptyList().with_type(TBag(TInt())))), SForEach(EVar('_var5849').with_type(TInt()), EEmptyList().with_type(TBag(TInt())), SCall(EVar('_var2669').with_type(TMaxHeap(TInt(), TInt())), 'update', (EVar('_var5849').with_type(TInt()), EVar('_var5849').with_type(TInt()))))))), SSeq(SAssign(EVar('_var2670').with_type(TInt()), EVar('_var10460').with_type(TInt())), SSeq(SForEach(EVar('_var2540').with_type(TInt()), EVar('_var10461').with_type(TBag(TInt())), SMapDel(EVar('_var751').with_type(TMap(TInt(), TBool())), EVar('_var2540').with_type(TInt()))), SForEach(EVar('_var2540').with_type(TInt()), EEmptyList().with_type(TBag(TInt())), SMapUpdate(EVar('_var751').with_type(TMap(TInt(), TBool())), EVar('_var2540').with_type(TInt()), EVar('_var2541').with_type(TBool()), SNoOp())))))), '')), '', '', '')
        print(pprint(impl))
        for codegen in (CxxPrinter, JavaPrinter):
            state_map = OrderedDict([('_var653', EArgMax(EVar('l').with_type(TBag(TInt())), ELambda(EVar('x').with_type(TInt()), EVar('x').with_type(TInt()))).with_type(TInt())), ('_var751', EMakeMap2(EVar('l').with_type(TBag(TInt())), ELambda(EVar('_var692').with_type(TInt()), EBool(True).with_type(TBool()))).with_type(TMap(TInt(), TBool()))), ('_var1648', EUnaryOp('exists', EVar('l').with_type(TBag(TInt()))).with_type(TBool())), ('_var2669', EMakeMaxHeap(EVar('l').with_type(TBag(TInt())), ELambda(EVar('_var760').with_type(TInt()), EVar('_var760').with_type(TInt()))).with_type(TMaxHeap(TInt(), TInt()))), ('_var2670', EUnaryOp('len', EVar('l').with_type(TBag(TInt()))).with_type(TInt()))])
            share_info = defaultdict(list, {})
            self.check(impl, state_map, share_info, lambda out: codegen(out=out))

    def test_regression04(self):
        impl = Spec('Basic', [], [], [('_var12', TList(TInt())), ('_var895', TMap(TInt(), TList(TInt()))), ('_var9841', TMap(TInt(), TList(TInt()))), ('_var10947', TMap(TInt(), TBool()))], [], [Query('elems', 'public', [], (), EVar('_var12').with_type(TList(TInt())), ""), Query('_name13', 'internal', [('n', TInt())], (), ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt())), ""), Query('_name14', 'internal', [('n', TInt())], (), EEmptyList().with_type(TBag(TInt())), ""), Query('_name35', 'internal', [('n', TInt())], (), EMapGet(EVar('_var895').with_type(TMap(TInt(), TList(TInt()))), EVar('n').with_type(TInt())).with_type(TList(TInt())), ""), Query('_name911', 'internal', [('_var905', TInt()), ('n', TInt())], (), ESingleton(EVar('_var905').with_type(TInt())).with_type(TBag(TInt())), ""), Query('_name912', 'internal', [('_var905', TInt()), ('n', TInt())], (), EEmptyList().with_type(TBag(TInt())), ""), Query('_name914', 'internal', [('n', TInt())], (), EFilter(ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt())), ELambda(EVar('_var1498').with_type(TInt()), EUnaryOp('not', EMapGet(EVar('_var10947').with_type(TMap(TInt(), TBool())), EVar('_var1498').with_type(TInt())).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), ""), Query('_name1497', 'internal', [('_var1492', TInt()), ('n', TInt())], (), EEmptyList().with_type(TBag(TInt())), ""), Query('_name1506', 'internal', [('_var1492', TInt()), ('n', TInt())], (), ESingleton(EVar('_var1492').with_type(TInt())).with_type(TBag(TInt())), ""), Query('_name1519', 'internal', [('n', TInt())], (), EMapGet(EVar('_var9841').with_type(TMap(TInt(), TList(TInt()))), EVar('n').with_type(TInt())).with_type(TList(TInt())), ""), Query('_name9848', 'internal', [('_var9842', TInt()), ('n', TInt())], (), EBinOp(ECond(EBinOp(EVar('_var9842').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool()), EBinOp(EFilter(EVar('_var12').with_type(TList(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ESingleton(EVar('_var9842').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), '+', EFilter(ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ESingleton(EVar('_var9842').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt()))).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ECond(EBinOp(EVar('_var9842').with_type(TInt()), 'in', EVar('_var12').with_type(TList(TInt()))).with_type(TBool()), EFilter(EVar('_var12').with_type(TList(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('_var9842').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt())), ""), Query('_name9855', 'internal', [('_var9842', TInt()), ('n', TInt())], (), EBinOp(ECond(EBinOp(EVar('_var9842').with_type(TInt()), 'in', EVar('_var12').with_type(TList(TInt()))).with_type(TBool()), EFilter(EVar('_var12').with_type(TList(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('_var9842').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ECond(EBinOp(EVar('_var9842').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool()), EBinOp(EFilter(EVar('_var12').with_type(TList(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ESingleton(EVar('_var9842').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), '+', EFilter(ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ESingleton(EVar('_var9842').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt()))).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt())), ""), Query('_name9863', 'internal', [('n', TInt())], (), EFilter(EUnaryOp('distinct', EBinOp(EUnaryOp('distinct', EVar('_var12').with_type(TList(TInt()))).with_type(TList(TInt())), '+', EUnaryOp('distinct', EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt())), ELambda(EVar('_var9842').with_type(TInt()), EUnaryOp('not', EBinOp(ECond(EBinOp(EVar('_var9842').with_type(TInt()), 'in', EVar('_var12').with_type(TList(TInt()))).with_type(TBool()), EFilter(EVar('_var12').with_type(TList(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('_var9842').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt())), '==', ECond(EBinOp(EVar('_var9842').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool()), EBinOp(EFilter(EVar('_var12').with_type(TList(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ESingleton(EVar('_var9842').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), '+', EFilter(ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ESingleton(EVar('_var9842').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt()))).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), ""), Query('_name16354', 'internal', [('_var16321', TInt()), ('n', TInt())], (), EBinOp(ECond(EBinOp(EVar('_var16321').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool()), EFilter(EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ESingleton(EVar('_var16321').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ECond(EBinOp(EVar('_var16321').with_type(TInt()), 'in', EVar('_var12').with_type(TList(TInt()))).with_type(TBool()), EFilter(EVar('_var12').with_type(TList(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('_var16321').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt())), ""), Query('_name16357', 'internal', [('_var16321', TInt()), ('n', TInt())], (), EBinOp(ECond(EBinOp(EVar('_var16321').with_type(TInt()), 'in', EVar('_var12').with_type(TList(TInt()))).with_type(TBool()), EFilter(EVar('_var12').with_type(TList(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('_var16321').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ECond(EBinOp(EVar('_var16321').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool()), EFilter(EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt())), '-', ESingleton(EVar('_var16321').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt())), ""), Query('_name24791', 'internal', [('_var24789', TInt()), ('n', TInt())], (), ECond(EBinOp(EVar('_var24789').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool()), EBinOp(EVar('_var24789').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '+', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool()), EBool(False).with_type(TBool())).with_type(TBool()), ""), Query('_name28311', 'internal', [('_var28307', TInt()), ('n', TInt())], (), ECond(EBinOp(EVar('_var28307').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool()), EBinOp(EVar('_var28307').with_type(TInt()), 'in', EBinOp(EVar('_var12').with_type(TList(TInt())), '-', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool()), EBool(False).with_type(TBool())).with_type(TBool()), ""), Op('add', [('n', TInt())], [], SSeq(SSeq(SSeq(SSeq(SForEach(EVar('_var15').with_type(TInt()), ECall('_name14', [EVar('n').with_type(TInt())]).with_type(TBag(TInt())), SCall(EVar('_var12').with_type(TList(TInt())), 'remove', [EVar('_var15').with_type(TInt())])), SForEach(EVar('_var15').with_type(TInt()), ECall('_name13', [EVar('n').with_type(TInt())]).with_type(TBag(TInt())), SCall(EVar('_var12').with_type(TList(TInt())), 'add', [EVar('_var15').with_type(TInt())]))), SForEach(EVar('_var905').with_type(TInt()), ECall('_name914', [EVar('n').with_type(TInt())]).with_type(TBag(TInt())), SMapUpdate(EVar('_var895').with_type(TMap(TInt(), TList(TInt()))), EVar('_var905').with_type(TInt()), EVar('_var906').with_type(TList(TInt())), SSeq(SForEach(EVar('_var913').with_type(TInt()), ECall('_name912', [EVar('_var905').with_type(TInt()), EVar('n').with_type(TInt())]).with_type(TBag(TInt())), SCall(EVar('_var906').with_type(TList(TInt())), 'remove', [EVar('_var913').with_type(TInt())])), SForEach(EVar('_var913').with_type(TInt()), ECall('_name911', [EVar('_var905').with_type(TInt()), EVar('n').with_type(TInt())]).with_type(TBag(TInt())), SCall(EVar('_var906').with_type(TList(TInt())), 'add', [EVar('_var913').with_type(TInt())])))))), SForEach(EVar('_var9842').with_type(TInt()), ECall('_name9863', [EVar('n').with_type(TInt())]).with_type(TBag(TInt())), SMapUpdate(EVar('_var9841').with_type(TMap(TInt(), TList(TInt()))), EVar('_var9842').with_type(TInt()), EVar('_var9843').with_type(TList(TInt())), SSeq(SForEach(EVar('_var9856').with_type(TInt()), ECall('_name9855', [EVar('_var9842').with_type(TInt()), EVar('n').with_type(TInt())]).with_type(TBag(TInt())), SCall(EVar('_var9843').with_type(TList(TInt())), 'remove', [EVar('_var9856').with_type(TInt())])), SForEach(EVar('_var9856').with_type(TInt()), ECall('_name9848', [EVar('_var9842').with_type(TInt()), EVar('n').with_type(TInt())]).with_type(TBag(TInt())), SCall(EVar('_var9843').with_type(TList(TInt())), 'add', [EVar('_var9856').with_type(TInt())])))))), SForEach(EVar('_var24789').with_type(TInt()), ECall('_name914', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), SMapUpdate(EVar('_var10947').with_type(TMap(TInt(), TBool())), EVar('_var24789').with_type(TInt()), EVar('_var24790').with_type(TBool()), SAssign(EVar('_var24790').with_type(TBool()), ECall('_name24791', (EVar('_var24789').with_type(TInt()), EVar('n').with_type(TInt()))).with_type(TBool()))))), ""), Op('remove', [('n', TInt())], [], SSeq(SSeq(SSeq(SSeq(SForEach(EVar('_var36').with_type(TInt()), ECall('_name35', (EVar('n').with_type(TInt()),)).with_type(TList(TInt())), SCall(EVar('_var12').with_type(TList(TInt())), 'remove', [EVar('_var36').with_type(TInt())])), SForEach(EVar('_var36').with_type(TInt()), ECall('_name14', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), SCall(EVar('_var12').with_type(TList(TInt())), 'add', [EVar('_var36').with_type(TInt())]))), SForEach(EVar('_var1492').with_type(TInt()), ECall('_name1519', [EVar('n').with_type(TInt())]).with_type(TList(TInt())), SMapUpdate(EVar('_var895').with_type(TMap(TInt(), TList(TInt()))), EVar('_var1492').with_type(TInt()), EVar('_var1493').with_type(TList(TInt())), SSeq(SForEach(EVar('_var1507').with_type(TInt()), ECall('_name1506', [EVar('_var1492').with_type(TInt()), EVar('n').with_type(TInt())]).with_type(TBag(TInt())), SCall(EVar('_var1493').with_type(TList(TInt())), 'remove', [EVar('_var1507').with_type(TInt())])), SForEach(EVar('_var1507').with_type(TInt()), ECall('_name1497', [EVar('_var1492').with_type(TInt()), EVar('n').with_type(TInt())]).with_type(TBag(TInt())), SCall(EVar('_var1493').with_type(TList(TInt())), 'add', [EVar('_var1507').with_type(TInt())])))))), SForEach(EVar('_var16321').with_type(TInt()), ECall('_name35', (EVar('n').with_type(TInt()),)).with_type(TList(TInt())), SMapUpdate(EVar('_var9841').with_type(TMap(TInt(), TList(TInt()))), EVar('_var16321').with_type(TInt()), EVar('_var16322').with_type(TList(TInt())), SSeq(SForEach(EVar('_var16358').with_type(TInt()), ECall('_name16357', (EVar('_var16321').with_type(TInt()), EVar('n').with_type(TInt()))).with_type(TBag(TInt())), SCall(EVar('_var16322').with_type(TList(TInt())), 'remove', [EVar('_var16358').with_type(TInt())])), SForEach(EVar('_var16358').with_type(TInt()), ECall('_name16354', (EVar('_var16321').with_type(TInt()), EVar('n').with_type(TInt()))).with_type(TBag(TInt())), SCall(EVar('_var16322').with_type(TList(TInt())), 'add', [EVar('_var16358').with_type(TInt())])))))), SForEach(EVar('_var28307').with_type(TInt()), ECall('_name1519', (EVar('n').with_type(TInt()),)).with_type(TList(TInt())), SMapUpdate(EVar('_var10947').with_type(TMap(TInt(), TBool())), EVar('_var28307').with_type(TInt()), EVar('_var28309').with_type(TBool()), SAssign(EVar('_var28309').with_type(TBool()), ECall('_name28311', (EVar('_var28307').with_type(TInt()), EVar('n').with_type(TInt()))).with_type(TBool()))))), "")], "", "", "")
        print(pprint(impl))
        for codegen in (CxxPrinter, JavaPrinter):
            state_map = {'_var12': EVar('l').with_type(TBag(TInt())), '_var895': EMakeMap2(EVar('l').with_type(TBag(TInt())), ELambda(EVar('_var116').with_type(TInt()), ESingleton(EVar('_var116').with_type(TInt())).with_type(TBag(TInt())))).with_type(TMap(TInt(), TBag(TInt()))), '_var9841': EMakeMap2(EVar('l').with_type(TBag(TInt())), ELambda(EVar('_var2516').with_type(TInt()), EFilter(EVar('l').with_type(TBag(TInt())), ELambda(EVar('_var2515').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var2515').with_type(TInt()), 'in', EBinOp(EVar('l').with_type(TBag(TInt())), '-', ESingleton(EVar('_var2516').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())))).with_type(TMap(TInt(), TBag(TInt()))), '_var10947': EMakeMap2(EVar('l').with_type(TBag(TInt())), ELambda(EVar('_var1498').with_type(TInt()), EBinOp(EVar('_var1498').with_type(TInt()), 'in', EVar('l').with_type(TBag(TInt()))).with_type(TBool()))).with_type(TMap(TInt(), TBool()))}
            share_info = {}
            self.check(impl, state_map, share_info, lambda out: codegen(out=out))

    def test_construct_concrete_list(self):
        with io.StringIO() as f:
            for codgen in (CxxPrinter(out=f), JavaPrinter(out=f)):
                bag = EFilter(EVar("v").with_type(TBag(INT)), mk_lambda(INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(INT))
                stm = codgen.construct_concrete(TList(INT), bag, EVar("out").with_type(TList(INT)))
                codgen.visit(stm)

    def test_construct_concrete_map(self):
        with io.StringIO() as f:
            for codgen in (CxxPrinter(out=f), JavaPrinter(out=f)):
                bag = EFilter(EVar("v").with_type(TBag(INT)), mk_lambda(INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(INT))
                map = EMakeMap2(bag, mk_lambda(INT, lambda k: k)).with_type(TMap(INT, INT))
                stm = codgen.construct_concrete(TMap(INT, INT), map, EVar("out").with_type(TMap(INT, INT)))
                codgen.visit(stm)

    def test_distinct_foreach(self):
        with io.StringIO() as f:
            for codgen in (CxxPrinter(out=f), JavaPrinter(out=f)):
                bag = EFilter(EVar("v").with_type(TBag(INT)), mk_lambda(INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(INT))
                x = fresh_var(INT)
                v = fresh_var(INT)
                stm = SForEach(x, EUnaryOp(UOp.Distinct, bag).with_type(TSet(INT)), SAssign(v, x))
                codgen.visit(stm)

    def test_distinct(self):
        with io.StringIO() as f:
            for codgen in (CxxPrinter(out=f), JavaPrinter(out=f)):
                bag = EFilter(EVar("v").with_type(TBag(INT)), mk_lambda(INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(INT))
                print(codgen.visit(EUnaryOp(UOp.Distinct, bag).with_type(TSet(INT))))

    def test_len(self):
        with io.StringIO() as f:
            for codgen in (CxxPrinter(out=f), JavaPrinter(out=f)):
                bag = EFilter(EVar("v").with_type(TBag(INT)), mk_lambda(INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(INT))
                print(codgen.visit(EUnaryOp(UOp.Length, bag).with_type(TSet(INT))))

    def test_all(self):
        with io.StringIO() as f:
            for codgen in (CxxPrinter(out=f), JavaPrinter(out=f)):
                bag = EMap(EVar("v").with_type(TBag(INT)), mk_lambda(INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(BOOL))
                print(codgen.visit(EUnaryOp(UOp.All, bag).with_type(TSet(INT))))

    def test_any(self):
        with io.StringIO() as f:
            for codgen in (CxxPrinter(out=f), JavaPrinter(out=f)):
                bag = EMap(EVar("v").with_type(TBag(INT)), mk_lambda(INT, lambda x: EBinOp(x, ">", ZERO).with_type(BOOL))).with_type(TBag(BOOL))
                print(codgen.visit(EUnaryOp(UOp.Any, bag).with_type(TSet(INT))))

    def test_argmin(self):
        with io.StringIO() as f:
            for codgen in (CxxPrinter(out=f), JavaPrinter(out=f)):
                bag = EMap(EVar("v").with_type(TBag(INT)), mk_lambda(INT, lambda x: EBinOp(x, ">", ZERO).with_type(BOOL))).with_type(TBag(BOOL))
                print(codgen.visit(EArgMin(bag, mk_lambda(INT, lambda x: EUnaryOp("-", x).with_type(x.type))).with_type(INT)))
