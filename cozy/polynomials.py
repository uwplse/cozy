"""Class for representing polynomials of one variable."""

import functools

@functools.total_ordering
class Polynomial(object):
    __slots__ = ("terms",)

    def __init__(self, terms=()):
        terms = list(terms)
        while terms and (terms[-1] == 0):
            terms.pop()
        self.terms = tuple(terms)

    def __hash__(self):
        return hash(self.terms)

    def __eq__(self, other):
        return self.terms == other.terms

    def __lt__(self, other):
        if len(self.terms) != len(other.terms):
            return len(self.terms) < len(other.terms)
        for i in reversed(range(len(self.terms))):
            self_term = self.terms[i]
            other_term = other.terms[i]
            if self_term < other_term:
                return True
            if other_term < self_term:
                return False
        return False

    def __str__(self):
        if not self.terms:
            return "0"
        s = str(self.terms[0])
        for i in range(1, len(self.terms)):
            if self.terms[i]:
                term = str(self.terms[i])
                exponent = "n^{}".format(i) if i > 1 else "n"
                s = term + exponent + " + " + s
        return s

    def __repr__(self):
        return "Polynomial({!r})".format(self.terms)

    def get_coefficient(self, i):
        if i >= len(self.terms):
            return 0
        return self.terms[i]

    def largest_term(self):
        if not self.terms:
            return DominantTerm.ZERO
        exponent = len(self.terms) - 1
        return DominantTerm(
            multiplier=self.get_coefficient(exponent),
            exponent=exponent)

    def __add__(self, other):
        terms = [0] * max(len(self.terms), len(other.terms))
        for i in range(len(terms)):
            terms[i] = self.get_coefficient(i) + other.get_coefficient(i)
        return Polynomial(terms)

    def __mul__(self, other):
        if isinstance(other, Polynomial):
            res = Polynomial.ZERO
            for i in range(len(self.terms)):
                res += other * self.terms[i]
                res += Polynomial([0] * i + list(other.terms))
            return res
        else:
            return Polynomial((t * other) for t in self.terms)

Polynomial.ZERO = Polynomial()
Polynomial.ONE  = Polynomial([1])
Polynomial.N    = Polynomial([0, 1])

@functools.total_ordering
class DominantTerm(object):
    """A term of the form c*n^e for some unknown n.

    Instances of this class can be added, multiplied, and compared.  A term
    with a higher exponent is always greater than one with a lower exponent.
    """
    __slots__ = ("multiplier", "exponent")
    def __init__(self, multiplier, exponent):
        self.multiplier = multiplier
        self.exponent = exponent
    def __eq__(self, other):
        return self.multiplier == other.multiplier and self.exponent == other.exponent
    def __lt__(self, other):
        return (self.exponent, self.multiplier) < (other.exponent, other.multiplier)
    def __str__(self):
        return "{}n^{}".format(self.multiplier, self.exponent)
    def __repr__(self):
        return "DominantTerm({}, {})".format(self.multiplier, self.exponent)
    def __add__(self, other):
        if other.exponent == self.exponent:
            return DominantTerm(self.multiplier + other.multiplier, self.exponent)
        if other.exponent > self.exponent:
            return other
        return self
    def __mul__(self, other):
        return DominantTerm(self.multiplier * other.multiplier, self.exponent + other.exponent)

DominantTerm.ZERO = DominantTerm(0, 0)
DominantTerm.ONE  = DominantTerm(1, 0)
DominantTerm.N    = DominantTerm(1, 1)
