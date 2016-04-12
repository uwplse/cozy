"""
Parser for Cozy files.

The key function to look at is:
    parse(string) -> AST
"""

# buitin
from __future__ import print_function
import re
import sys

# 3rd party
from ply import lex, yacc

# ours
import parsetools
import syntax

# Each keyword becomes a KW_* token for the lexer. So, e.g. "and" becomes
# KW_AND.
_KEYWORDS = [
    "type",
    "enum",
    "op",
    "query",
    "state",
    "assume",
    "true",
    "false",
    "not",
    "and",
    "or",
    "in",
    "empty",
    "unique",
    "min",
    "max",
    "sum",
    "some",
    "new",
    "del"]

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
    ("VBAR", "|")]

################################################################################

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
tokens += ["WORD", "NUM"]
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
        r"\d+"
        t.value = int(t.value)
        return t

    # Define a rule so we can track line numbers
    def t_newline(t):
        r'\n+'
        t.lexer.lineno += len(t.value)

    t_ignore = ' \t'

    def t_error(t):
        print("Illegal character {}".format(repr(t.value[0])), file=sys.stderr)
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

################################################################################

def make_parser():
    start = "spec"

    def p_spec(p):
        """spec : WORD OP_COLON typedecls states assumes methods"""
        p[0] = syntax.Spec(p[1], p[3], p[4], p[5], p[6])

    parsetools.multi(locals(), "typedecls", "typedecl")

    def p_typedecl(p):
        """typedecl : KW_TYPE WORD OP_ASSIGN type"""
        p[0] = (p[2], p[4])

    def p_type(p):
        """type : WORD
                | WORD OP_LT type OP_GT
                | OP_OPEN_BRACE typednames OP_CLOSE_BRACE
                | KW_ENUM OP_OPEN_BRACE enum_cases OP_CLOSE_BRACE"""
        if len(p) == 2:
            p[0] = syntax.TNamed(p[1])
        elif len(p) == 5:
            if p[1] == "enum":
                p[0] = syntax.TEnum(p[3])
            else:
                p[0] = syntax.TApp(p[1], p[3])
        elif len(p) == 4:
            p[0] = syntax.TRecord(p[2])

    parsetools.multi(locals(), "enum_cases", "WORD", sep="OP_COMMA")

    def p_typedname(p):
        """typedname : WORD OP_COLON type"""
        p[0] = (p[1], p[3])

    parsetools.multi(locals(), "typednames", "typedname", sep="OP_COMMA")

    def p_statevar(p):
        """statevar : KW_STATE WORD OP_COLON type"""
        p[0] = (p[2], p[4])

    parsetools.multi(locals(), "states", "statevar")

    def p_assume(p):
        """assume : KW_ASSUME exp OP_SEMICOLON"""
        p[0] = p[2]

    parsetools.multi(locals(), "assumes", "assume")

    precedence = (
        ("left", "OP_COMMA"),
        ("left", "OP_IMPLIES"),
        ("left", "KW_AND", "KW_OR"),
        ("left", "OP_EQ", "OP_NE", "OP_LT", "OP_LE", "OP_GT", "OP_GE"),
        ("left", "OP_PLUS", "OP_MINUS"),
        ("left", "KW_IN"),
        ("left", "KW_NOT", "KW_UNIQUE", "KW_EMPTY", "KW_SOME", "KW_MIN", "KW_MAX", "KW_SUM", "KW_NEW", "KW_DEL"),
        ("left", "OP_OPEN_PAREN"),
        ("left", "OP_DOT"))

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
               | KW_NOT exp
               | exp KW_IN exp
               | OP_VBAR exp OP_VBAR
               | KW_UNIQUE exp
               | KW_EMPTY exp
               | KW_SOME exp
               | KW_MIN exp
               | KW_MAX exp
               | KW_SUM exp
               | exp OP_DOT WORD
               | OP_OPEN_PAREN exp OP_CLOSE_PAREN
               | KW_NEW WORD OP_OPEN_PAREN exp_list OP_CLOSE_PAREN
               | OP_OPEN_BRACE record_fields OP_CLOSE_BRACE
               | OP_OPEN_BRACKET exp OP_VBAR comprehension_body OP_CLOSE_BRACKET"""
        if len(p) == 2:
            if type(p[1]) is int:
                p[0] = syntax.ENum(p[1])
            elif p[1] == "true":
                p[0] = syntax.EBool(True)
            elif p[1] == "false":
                p[0] = syntax.EBool(False)
            else:
                p[0] = syntax.EVar(p[1])
        elif len(p) == 3:
            p[0] = syntax.EUnaryOp(p[1], p[2])
        elif len(p) == 4:
            if p[1] == "(":
                p[0] = p[2]
            elif p[1] == "{":
                p[0] = syntax.EMakeRecord(p[2])
            elif p[2] == ".":
                p[0] = syntax.EGetField(p[1], p[3])
            elif p[1] == "|":
                p[0] = syntax.EUnaryOp("len", p[2])
            else:
                p[0] = syntax.EBinOp(p[1], p[2], p[3])
        else:
            if p[1] == "new":
                p[0] = syntax.EAlloc(syntax.TNamed(p[2]), p[4])
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

    def p_method(p):
        """method : KW_OP    WORD OP_OPEN_PAREN typednames OP_CLOSE_PAREN assumes stm
                  | KW_QUERY WORD OP_OPEN_PAREN typednames OP_CLOSE_PAREN assumes exp"""
        if p[1] == "op":
            p[0] = syntax.Op(p[2], p[4], p[6], p[7])
        else:
            p[0] = syntax.Query(p[2], p[4], p[6], p[7])

    parsetools.multi(locals(), "methods", "method")

    def p_stm(p):
        """stm : OP_OPEN_PAREN OP_CLOSE_PAREN
               | WORD OP_DOT WORD OP_OPEN_PAREN exp_list OP_CLOSE_PAREN
               | WORD OP_DOT WORD OP_ASSIGN exp
               | KW_DEL exp"""
        if p[1] == "(":
            p[0] = syntax.SNoOp()
        elif p[1] == "del":
            p[0] = syntax.SDel(p[2])
        elif p[4] == "(":
            p[0] = syntax.SCall(p[1], p[3], p[5])
        else:
            p[0] = syntax.SAssign(p[1], p[3], p[5])

    def p_empty(p):
        'empty :'
        pass

    def p_error(p):
        raise Exception("Syntax error at {}:{}".format(p.lineno, p.lexpos))

    return yacc.yacc()

_parser = make_parser()
def parse(s):
    parser = _parser
    return parser.parse(s)
