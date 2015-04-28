import re
import itertools
import predicates

_EOF = object()
_TOKEN_REGEX = re.compile(r'\s*(\w+|>=|<=|>|<|==|.)')
_KEYWORDS = ("fields", "vars", "query", "assume")

def _tokenize(text):
    while True:
        match = _TOKEN_REGEX.match(text)
        if not match:
            assert text.strip() == ""
            yield _EOF
            return
        yield match.group(1)
        text = text[len(match.group(0)):]

class peekable(object):
    def __init__(self, i):
        self.i = i
    def __iter__(self):
        return self
    def __next__(self):
        return self.next()
    def next(self):
        return self.i.next()
    def peek(self):
        e = self.next()
        self.i = itertools.chain([e], self.i)
        return e

def _parseType(tokens):
    t = tokens.next()
    while tokens.peek() is not _EOF and tokens.peek() != "," and tokens.peek() not in _KEYWORDS:
        t += tokens.next()
    return t

def _parseVars(tokens):
    while tokens.peek() is not _EOF and tokens.peek() not in _KEYWORDS:
        field_name = tokens.next()
        ty = "double"
        if tokens.peek() == ":":
            tokens.next()
            ty = _parseType(tokens)
        yield (field_name, ty)
        if tokens.peek() == ",":
            tokens.next()

_ops = ["or", "and"] # ordered by associativity
def _parseQuery(fields, qvars, tokens, assoc=0):
    if assoc >= len(_ops):
        tok = tokens.next()
        assert tok is not _EOF
        if tok == "(":
            q = _parseQuery(fields, qvars, tokens, 0)
            assert tokens.next() == ")"
            return q
        elif tok == "not":
            return predicates.Not(_parseQuery(fields, qvars, tokens, 0))
        elif tok == "true":
            return predicates.Bool(True)
        elif tok == "false":
            return predicates.Bool(False)
        else:
            f = tok
            op = tokens.next()
            v = tokens.next()
            assert f in fields or f in qvars, "unkown var '{}'".format(f)
            m = { ">=" : predicates.Ge,
                "<=" : predicates.Le,
                ">" : predicates.Gt,
                "<" : predicates.Lt,
                "==" : predicates.Eq,
                "!=" : predicates.Ne }
            assert op in m
            assert v in fields or v in qvars
            return predicates.Compare(predicates.Var(f), m[op], predicates.Var(v))
    else:
        q1 = _parseQuery(fields, qvars, tokens, assoc + 1)
        if tokens.peek() == _ops[assoc]:
            op = tokens.next()
            q2 = _parseQuery(fields, qvars, tokens, assoc)
            m = { "and": predicates.And, "or": predicates.Or }
            assert op in m
            return m[op](q1, q2)
        return q1

def parseQuery(text):
    tokens = peekable(_tokenize(text))
    assert tokens.next() == "fields"
    fields = list(_parseVars(tokens))
    assert tokens.next() == "vars"
    qvars = list(_parseVars(tokens))

    field_names = set(f for f,t in fields)
    var_names = set(v for v,t in qvars)

    assumptions = []
    tok = tokens.next()
    while tok == "assume":
        assumptions.append(_parseQuery(field_names, var_names, tokens))
        tok = tokens.next()

    assert tok == "query"
    q = _parseQuery(field_names, var_names, tokens)

    costmodel = None
    if tokens.peek() == "costmodel":
        tokens.next()
        costmodel = ""
        while tokens.peek() is not _EOF:
            costmodel += tokens.next()

    assert tokens.peek() is _EOF
    return fields, qvars, assumptions, q, costmodel
