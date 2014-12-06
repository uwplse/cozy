import re
import itertools

_EOF = object()
_regex = re.compile(r'\s*(\(|\)|\w+|>=|<=|>|<|==)')
def _tokenize(text):
    while True:
        match = _regex.match(text)
        if not match:
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

def _parseFields(tokens):
    while tokens.peek() is not _EOF and tokens.peek() != "vars" and tokens.peek() != "query":
        yield tokens.next()

def _parseVars(tokens):
    while tokens.peek() is not _EOF and tokens.peek() != "query":
        yield tokens.next()

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
            return ["Not", _parseQuery(fields, qvars, tokens, 0)]
        elif tok == "true":
            return ["TrueQuery"]
        elif tok == "false":
            return ["FalseQuery"]
        else:
            f = tok
            op = tokens.next()
            v = tokens.next()
            assert f in fields
            m = { ">=" : "Ge", "<=" : "Le", ">" : "Gt", "<" : "Lt", "==" : "Eq" }
            assert op in m
            assert v in qvars
            return ["Cmp", f, m[op], v]
    else:
        q1 = _parseQuery(fields, qvars, tokens, assoc + 1)
        if tokens.peek() is not _EOF and tokens.peek() == _ops[assoc]:
            op = tokens.next()
            q2 = _parseQuery(fields, qvars, tokens, assoc)
            return [op[0].upper() + op[1:], q1, q2]
        return q1

def parseQuery(text):
    tokens = peekable(_tokenize(text))
    assert tokens.next() == "fields"
    fields = list(_parseFields(tokens))
    assert tokens.next() == "vars"
    qvars = list(_parseVars(tokens))
    assert tokens.next() == "query"
    q = _parseQuery(fields, qvars, tokens)
    assert tokens.peek() is _EOF
    return fields, qvars, q
