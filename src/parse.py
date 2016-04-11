import re
import itertools
import predicates
from queries import Query

_EOF = object()
_TOKEN_REGEX = re.compile(r'\s*(\w+|>=|<=|>|<|==|!=|.)')
_KEYWORDS = ("fields", "vars", "query", "assume", "sort", "costmodel")

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
        return next(self.i)
    def peek(self):
        e = self.next()
        self.i = itertools.chain([e], self.i)
        return e

def _parseType(tokens):
    t = tokens.next()
    while (tokens.peek() is not _EOF and
            tokens.peek() != "," and
            tokens.peek() != ")" and
            tokens.peek() not in _KEYWORDS):
        t += tokens.next()
    return t

def _parseVars(tokens):
    while tokens.peek() is not _EOF and tokens.peek() not in _KEYWORDS and tokens.peek() != ")":
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
            m = { ">=" : predicates.Ge,
                "<=" : predicates.Le,
                ">" : predicates.Gt,
                "<" : predicates.Lt,
                "==" : predicates.Eq,
                "!=" : predicates.Ne }
            assert f in fields or f in qvars, "unkown var '{}'".format(f)
            assert op in m
            assert v in fields or v in qvars, "unkown var '{}'".format(v)
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

    field_names = set(f for f,t in fields)

    assumptions = []
    while tokens.peek() == "assume":
        tokens.next()
        assumptions.append(_parseQuery(field_names, [], tokens))

    queries = []
    while tokens.peek() == "query":
        tokens.next()

        # name
        name = tokens.next()

        # vars
        assert tokens.next() == "("
        qvars = list(_parseVars(tokens))
        var_names = set(v for v,t in qvars)
        assert tokens.next() == ")"

        # assumptions
        query_assumptions = []
        while tokens.peek() == "assume":
            tokens.next()
            query_assumptions.append(_parseQuery((), var_names, tokens))

        # body
        pred = _parseQuery(field_names, var_names, tokens)

        # sort?
        sort_field = None
        if tokens.peek() == "sort":
            tokens.next()
            sort_field = tokens.next()

        queries.append(Query(
            name=name,
            vars=qvars,
            pred=pred,
            assumptions=query_assumptions,
            sort_field=sort_field))

    costmodel = None
    if tokens.peek() == "costmodel":
        tokens.next()
        costmodel = ""
        while tokens.peek() is not _EOF:
            costmodel += tokens.next()

    assert tokens.peek() is _EOF
    return fields, assumptions, queries, costmodel
