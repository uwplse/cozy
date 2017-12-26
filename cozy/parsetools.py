"""
Helper functions for the parser.
"""

from cozy.common import fresh_name

def multi(ldict, selfname, production, sep=None):
    """
    Usage:
        multi(locals(), NAME, P[, sep=SEP])
        where P and SEP are production names.

    This produces a production named NAME of the form

        NAME ::= empty | P (SEP P)*

    that produces tuples of whatever P produces.
    """

    if sep is None:
        sep = "empty"

    f1name = fresh_name("multisep")
    def f1(p):
        if len(p) > 2 and p[3]:
            p[0] = (p[1],) + p[3]
        else:
            p[0] = (p[1],)
    f1.__doc__ = (
        """{f1name} : {prod}
                    | {prod} {sep} {f1name}""".format(f1name=f1name, prod=production, sep=sep))
    f1.__name__ = "p_{}".format(f1name)
    ldict[f1.__name__] = f1

    def f2(p):
        if p[1]:
            p[0] = p[1]
        else:
            p[0] = ()
    f2.__doc__ = (
        """{self} : empty
                  | {f1name}""".format(self=selfname, f1name=f1name))
    f2.__name__ = "p_{}".format(selfname)
    ldict[f2.__name__] = f2

def unindent(value, pos, source):
    """
    Find the whitespace that preceded the opening line of the
    multiline string. If it's the same as the prefix of the other lines,
    remove it from the other lines. Used to normalize a multi-line comment,
    which comes to us like this:
    /* line 1
                * line 2
                * line 3...
                */

    ...but we want this, if possible:
    /* line 1
     * line 2
     * line 3...
     */
    """
    # If -1 is returned, we start at index 0. If anything else is returned, we
    # skip the newline that was found.
    line_begin = source.rfind('\n', 0, pos) + 1
    prefix = source[line_begin:pos]
    matched_lines = value.splitlines()

    if all(line.startswith(prefix) for line in matched_lines[1:]):
        return matched_lines[0] + '\n' + '\n'.join(
                line[len(prefix):] for line in matched_lines[1:])

    return value
