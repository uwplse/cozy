"""
Parser for Cozy files.

The key function to look at is:
    parse(string) -> AST
"""

# buitin
import re
import sys
import ast

# 3rd party
from ply import lex, yacc

# ours
from cozy import parsetools
from cozy import syntax

# Each keyword becomes a KW_* token for the lexer. So, e.g. "and" becomes
# KW_AND.
_KEYWORDS = ([
    "extern",
    "type",
    "handletype",
    "enum",
    "private",
    "op",
    "query",
    "state",
    "assume",
    "true",
    "false",
    "min", "argmin",
    "max", "argmax",
    "if",
    "else",
    "Native"] +
    list(syntax.UOps) +
    list(syntax.BOps))

# Each operator has a name and a raw string. Each becomes an OP_* token for the
# lexer. So, e.g. ("ASSIGN", "=") matches "=" and the token will be named
# OP_ASSIGN.
_OPERATORS = [
    ("ASSIGN", "="),
    ("IMPLIES", "=>"),
    ("GE", ">="),
    ("LE", "<="),
    ("GT", ">"),
    ("LT", "<"),
    ("EQ", "=="),
    ("NE", "!="),
    ("PLUS", "+"),
    ("MINUS", "-"),
    ("QUESTION", "?"),
    ("COLON", ":"),
    ("SEMICOLON", ";"),
    ("COMMA", ","),
    ("OPEN_BRACE", "{"),
    ("CLOSE_BRACE", "}"),
    ("OPEN_PAREN", "("),
    ("CLOSE_PAREN", ")"),
    ("OPEN_BRACKET", "["),
    ("CLOSE_BRACKET", "]"),
    ("DOT", "."),
    ("LEFT_ARROW", "<-"),
    ("RIGHT_ARROW", "->"),
    ("VBAR", "|")
    ]

# Lexer ########################################################################

def keyword_token_name(kw):
    return "KW_{}".format(kw.upper())

def op_token_name(opname):
    return "OP_{}".format(opname.upper())

# Enumerate token names
tokens = []
for kw in _KEYWORDS:
    tokens.append(keyword_token_name(kw))
for opname, op in _OPERATORS:
    tokens.append(op_token_name(opname))
tokens += ["WORD", "NUM", "STRINGLITERAL", "EXTERNCODETOKEN"]
tokens = tuple(tokens) # freeze tokens

def make_lexer():
    # *sigh*... ply has such a weird interface. There might be a cleaner way to
    # programmatically produce token productions, but I don't know what it is.
    for kw in _KEYWORDS:
        locals()["t_{}".format(keyword_token_name(kw))] = re.escape(kw)
    for opname, op in _OPERATORS:
        locals()["t_{}".format(op_token_name(opname))] = re.escape(op)

    def t_WORD(t):
        r"[a-zA-Z_]\w*"
        if t.value in _KEYWORDS:
            # I wish I knew why I needed this. :(
            t.type = keyword_token_name(t.value)
        return t

    def t_COMMENT(t):
        r"\/\/[^\n]*"
        pass

    def t_NUM(t):
        r"\d+(l|L)?"
        if t.value.lower().endswith("l"):
            t.value = syntax.ENum(int(t.value[:-1])).with_type(syntax.TLong())
        else:
            t.value = syntax.ENum(int(t.value)).with_type(syntax.TInt())
        return t

    def t_STRINGLITERAL(t):
        r'"([^\\"]|\\.)*"'
        t.value = ast.literal_eval(t.value)
        return t

    def t_EXTERNCODETOKEN(t):
        r"\{\{(.|\n)*?\}\}"
        t.value = t.value[2:-2]
        return t

    # Define a rule so we can track line numbers
    def t_newline(t):
        r'\n+'
        t.lexer.lineno += len(t.value)

    t_ignore = ' \t'

    def t_error(t):
        print("Illegal character {} on line {}".format(repr(t.value[0]), t.lexer.lineno), file=sys.stderr)
        t.lexer.skip(1)

    return lex.lex()

_lexer = make_lexer()
def tokenize(s):
    lexer = _lexer.clone() # Because lexer objects are stateful
    lexer.input(s)
    while True:
        tok = lexer.token()
        if not tok:
            break
        yield tok

# Parser #######################################################################

def make_parser():
    start = "spec"

    def p_spec(p):
        """spec : externcode WORD OP_COLON typedecls funcdecls states assumes methods externcode"""
        p[0] = syntax.Spec(p[2], p[4], p[5], p[6], p[7], p[8], p[1], p[9])

    def p_externcode(p):
        """externcode :
                      | EXTERNCODETOKEN"""
        p[0] = p[1] if len(p) > 1 else ""

    parsetools.multi(locals(), "typedecls", "typedecl")

    def p_typedecl(p):
        """typedecl : KW_TYPE WORD OP_ASSIGN type
                    | KW_HANDLETYPE WORD OP_ASSIGN type"""
        if p[1] == "type":
            p[0] = (p[2], p[4])
        elif p[1] == "handletype":
            p[0] = (p[2], syntax.THandle(p[2], p[4]))

    def p_type(p):
        """type : WORD
                | WORD OP_LT type OP_GT
                | OP_OPEN_BRACE typednames OP_CLOSE_BRACE
                | KW_ENUM OP_OPEN_BRACE enum_cases OP_CLOSE_BRACE
                | OP_OPEN_PAREN typelist OP_CLOSE_PAREN
                | KW_NATIVE STRINGLITERAL"""
        if len(p) == 2:
            p[0] = syntax.TNamed(p[1])
        elif len(p) == 3:
            p[0] = syntax.TNative(p[2])
        elif len(p) == 5:
            if p[1] == "enum":
                p[0] = syntax.TEnum(p[3])
            else:
                p[0] = syntax.TApp(p[1], p[3])
        elif len(p) == 4:
            if p[1] == "{":
                p[0] = syntax.TRecord(p[2])
            elif p[1] == "(":
                p[0] = syntax.TTuple(p[2])

    parsetools.multi(locals(), "enum_cases", "WORD", sep="OP_COMMA")

    def p_typedname(p):
        """typedname : WORD OP_COLON type"""
        p[0] = (p[1], p[3])

    parsetools.multi(locals(), "typednames", "typedname", sep="OP_COMMA")
    parsetools.multi(locals(), "typelist", "type", sep="OP_COMMA")

    def p_func(p):
        """func : KW_EXTERN WORD OP_OPEN_PAREN typednames OP_CLOSE_PAREN OP_COLON type OP_ASSIGN STRINGLITERAL"""
        p[0] = syntax.ExternFunc(p[2], p[4], p[7], p[9])

    parsetools.multi(locals(), "funcdecls", "func")

    def p_statevar(p):
        """statevar : KW_STATE WORD OP_COLON type"""
        p[0] = (p[2], p[4])

    parsetools.multi(locals(), "states", "statevar")

    def p_assume(p):
        """assume : KW_ASSUME exp OP_SEMICOLON"""
        p[0] = p[2]

    parsetools.multi(locals(), "assumes", "assume")

    precedence = (
        ("nonassoc", "IF_PLAIN"),
        ("nonassoc", "KW_ELSE"),
        ("left", "OP_COMMA"),
        ("left", "OP_QUESTION"),
        ("left", "OP_IMPLIES"),
        ("left", "KW_AND", "KW_OR"),
        ("left", "OP_EQ", "OP_NE", "OP_LT", "OP_LE", "OP_GT", "OP_GE"),
        ("left", "OP_PLUS", "OP_MINUS"),
        ("left", "KW_IN"),
        ("left", "KW_NOT", "KW_UNIQUE", "KW_EMPTY", "KW_EXISTS", "KW_THE", "KW_MIN", "KW_MAX", "KW_SUM", "KW_ANY", "KW_ALL", "KW_LEN"),
        ("left", "OP_OPEN_PAREN"),
        ("left", "OP_DOT"))

    def p_exp_strlit(p):
        """exp : STRINGLITERAL"""
        p[0] = syntax.EStr(p[1])

    def p_lambda(p):
        """lambda : OP_OPEN_BRACE WORD OP_RIGHT_ARROW exp OP_CLOSE_BRACE"""
        p[0] = syntax.ELambda(syntax.EVar(p[2]), p[4])

    def p_exp(p):
        """exp : NUM
               | WORD
               | WORD OP_OPEN_PAREN exp_list OP_CLOSE_PAREN
               | KW_TRUE
               | KW_FALSE
               | exp OP_PLUS  exp
               | exp OP_MINUS exp
               | exp OP_EQ exp
               | exp OP_NE exp
               | exp OP_LT exp
               | exp OP_LE exp
               | exp OP_GT exp
               | exp OP_GE exp
               | exp KW_AND exp
               | exp KW_OR exp
               | exp OP_IMPLIES exp
               | exp OP_QUESTION exp OP_COLON exp
               | KW_NOT exp
               | OP_MINUS exp
               | exp KW_IN exp
               | KW_UNIQUE exp
               | KW_EMPTY exp
               | KW_THE exp
               | KW_MIN exp
               | KW_MAX exp
               | KW_ARGMIN lambda exp
               | KW_ARGMAX lambda exp
               | KW_SUM exp
               | KW_LEN exp
               | KW_ANY exp
               | KW_ALL exp
               | KW_EXISTS exp
               | exp OP_DOT NUM
               | exp OP_DOT WORD
               | OP_OPEN_PAREN exp_list OP_CLOSE_PAREN
               | OP_OPEN_BRACE record_fields OP_CLOSE_BRACE
               | OP_OPEN_BRACKET exp OP_CLOSE_BRACKET
               | OP_OPEN_BRACKET exp OP_VBAR comprehension_body OP_CLOSE_BRACKET"""
        if len(p) == 2:
            if type(p[1]) is syntax.ENum:
                p[0] = p[1]
            elif p[1] == "true":
                p[0] = syntax.EBool(True)
            elif p[1] == "false":
                p[0] = syntax.EBool(False)
            else:
                p[0] = syntax.EVar(p[1])
        elif len(p) == 3:
            if p[1] == "min":
                p[0] = syntax.EArgMin(p[2], syntax.ELambda(syntax.EVar("x"), syntax.EVar("x")))
            elif p[1] == "max":
                p[0] = syntax.EArgMax(p[2], syntax.ELambda(syntax.EVar("x"), syntax.EVar("x")))
            else:
                p[0] = syntax.EUnaryOp(p[1], p[2])
        elif len(p) == 4:
            if p[1] == "(":
                exps = p[2]
                if len(exps) == 0:
                    raise Exception("illegal ()")
                elif len(exps) == 1:
                    p[0] = exps[0]
                elif len(exps) > 1:
                    p[0] = syntax.ETuple(tuple(exps))
            elif p[1] == "[":
                p[0] = syntax.ESingleton(p[2])
            elif p[1] == "{":
                p[0] = syntax.EMakeRecord(p[2])
            elif p[2] == ".":
                if isinstance(p[3], syntax.ENum):
                    p[0] = syntax.ETupleGet(p[1], p[3].val)
                else:
                    p[0] = syntax.EGetField(p[1], p[3])
            elif p[1] == "argmin":
                p[0] = syntax.EArgMin(p[3], p[2])
            elif p[1] == "argmax":
                p[0] = syntax.EArgMax(p[3], p[2])
            else:
                p[0] = syntax.EBinOp(p[1], p[2], p[3])
        else:
            if p[2] == "?":
                p[0] = syntax.ECond(p[1], p[3], p[5])
            elif p[1] == "[":
                p[0] = syntax.EListComprehension(p[2], p[4])
            elif p[2] == "(":
                p[0] = syntax.ECall(p[1], p[3])
            else:
                assert False, "unknown case: {}".format(repr(p[1:]))

    parsetools.multi(locals(), "exp_list", "exp", sep="OP_COMMA")

    def p_record_field(p):
        """record_field : WORD OP_COLON exp"""
        p[0] = (p[1], p[3])

    parsetools.multi(locals(), "record_fields", "record_field", sep="OP_COMMA")

    def p_comprehension_clause(p):
        """comprehension_clause : WORD OP_LEFT_ARROW exp
                                | exp"""
        if len(p) == 2:
            p[0] = syntax.CCond(p[1])
        else:
            p[0] = syntax.CPull(p[1], p[3])

    parsetools.multi(locals(), "comprehension_body", "comprehension_clause", sep="OP_COMMA")

    def p_accesschain(p):
        """accesschain : WORD
                       | accesschain OP_DOT WORD"""
        if len(p) > 2:
            p[0] = syntax.EGetField(p[1], p[3])
        else:
            p[0] = syntax.EVar(p[1])

    def p_visibility(p):
        """visibility :
                      | KW_PRIVATE"""
        if len(p) > 1:
            p[0] = syntax.Visibility.Private
        else:
            p[0] = syntax.Visibility.Public

    def p_method(p):
        """method : empty      KW_OP    WORD OP_OPEN_PAREN typednames OP_CLOSE_PAREN assumes stm
                  | visibility KW_QUERY WORD OP_OPEN_PAREN typednames OP_CLOSE_PAREN assumes exp"""
        if p[2] == "op":
            p[0] = syntax.Op(p[3], p[5], p[7], p[8])
        else:
            p[0] = syntax.Query(p[3], p[1], p[5], p[7], p[8])

    parsetools.multi(locals(), "methods", "method")

    def p_stm(p):
        """stm : accesschain OP_OPEN_PAREN exp_list OP_CLOSE_PAREN
               | accesschain OP_ASSIGN exp
               | KW_IF exp OP_COLON stm %prec IF_PLAIN
               | KW_IF exp OP_COLON stm KW_ELSE OP_COLON stm"""
        if p[1] == "if":
            else_expr = p[7] if len(p) == 8 else syntax.SNoOp()
            p[0] = syntax.SIf(p[2], p[4], else_expr)
        elif p[2] == "(":
            p[0] = syntax.SCall(p[1].e, p[1].f, p[3])
        else:
            p[0] = syntax.SAssign(p[1], p[3])

    def p_empty(p):
        'empty :'
        pass

    def p_error(p):
        if p is None:
            raise Exception("Unexpected end-of-file")
        raise Exception("Syntax error on line {}".format(p.lineno))

    return yacc.yacc()

_parser = make_parser()

def parse(s):
    parser = _parser
    return parser.parse(s)
