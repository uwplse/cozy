
class Query(object):
    def __init__(self, name, vars, pred, assumptions=(), sort_field=None):
        self.name = name
        self.vars = vars
        self.pred = pred
        self.assumptions = assumptions
        self.sort_field = sort_field
