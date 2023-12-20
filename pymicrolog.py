from enum import Enum


class TemporalAnnotation(Enum):
    start = 1
    next = 2

    def __repr__(self):
        if self == start:
            return "start"
        if self == next:
            return "next"


start = TemporalAnnotation.start
next = TemporalAnnotation.next


class Oracle(object):
    fn = None

    def __init__(self, fn):
        self.fn = fn

    def __call__(self, *args):
        return OracleFormula(self, args)


class Call(object):
    fn = None

    def __init__(self, fn):
        self.fn = fn

    def __call__(self, *args):
        return CallFormula(self, args)


class Conjunction(object):
    literals = None

    def __init__(self, *literals):
        self.literals = literals

    def reorder(self):

        def litOrder(lit):
            return [
                Formula, NegatedFormula, OracleFormula, NegatedOracleFormula
            ].index(type(lit))

        lits = list(self.literals)
        lits.sort(key=litOrder)
        return Conjunction(*lits)

    def asConjunction(self):  # very bad name
        return list(self.literals)

    def __repr__(self):
        return " & ".join(repr(l) for l in self.literals)

    def __and__(self, other):
        return Conjunction(*self.asConjunction(), *other.asConjunction())

    def __invert__(self):
        raise ValueError("Cannot negate Conjunction")


class Variable(object):
    varname = None

    def __init__(self, varname):
        self.varname = varname

    def __repr__(self):
        return f"Var({self.varname})"


class Relation(object):
    relname = None

    def __init__(self, relname):
        self.relname = relname

    def __call__(self, *params):
        return Formula(self.relname, params)

    def asConjunction(self):
        raise ValueError("Missing ()?")

    def __invert__(self):
        raise ValueError("Missing ()?")

    def __le__(self):
        raise ValueError("Missing ()?")

    def __repr__(self):
        return f"R({self.relname})"


class Formula(object):
    fn = None
    args = None

    def __init__(self, fn, args):
        self.fn = fn
        self.args = args

    def variables(self):
        return frozenset(arg for arg in self.args if isinstance(arg, Variable))

    def asRule(self):
        return Rule(head=self)

    def asConjunction(self):
        return [self]

    def __repr__(self):
        return f"{self.fn}{repr(self.args)}"

    def __and__(self, other):
        return Conjunction(*self.asConjunction(), *other.asConjunction())

    def __matmul__(self, other):  # @
        if not isinstance(other, TemporalAnnotation):
            raise NotImplementedError()
        else:
            return TempAnnotatedFormula(self, other)

    def __le__(self, other):
        return Rule(self, other)

    def __invert__(self):
        return NegatedFormula(self)


class Rule(object):
    head = None
    body = None

    def __init__(self, head, body=None):
        self.head = head
        self.body = body

    def __repr__(self):
        if self.body is None:
            return f"{repr(self.head)}."
        else:
            return f"{repr(self.head)} <- {repr(self.body)}."

    def asRule(self):
        return self

    def isRangeRestricted(self):
        if self.body is None:
            return not bool(self.head.variables())
        positives = set()
        dependents = set(self.head.variables())
        for lit in self.body.asConjunction():
            if isinstance(lit, Formula):
                positives.update(lit.variables())
            else:
                dependents.update(lit.variables())
        return positives.issuperset(dependents)

    def variables(self):
        if self.body is None:
            return self.head.variables()
        return self.head.variables() | self.body.variables()


class TempAnnotatedFormula(object):
    fn = None
    args = None
    temporalAnnotation = None

    def __init__(self, formula, annotation):
        self.fn = formula.fn
        self.args = formula.args
        self.temporalAnnotation = annotation

    def asRule(self):
        return Rule(head=self)

    def __le__(self, other):
        return Rule(self, other)

    def variables(self):
        return Formula(self.fn, self.args).variables()

    def __repr__(self):
        return f"{self.fn}{repr(self.args)}@{repr(self.temporalAnnotation)}"


class CallFormula(object):
    fn = None
    args = None

    def __init__(self, oracle, args):
        self.fn = oracle.fn
        self.args = args

    def variables(self):
        return frozenset(arg for arg in self.args if isinstance(arg, Variable))

    def __matmul__(self, other):
        if other is not next:
            raise ValueError()
        else:
            return self

    def __le__(self, other):
        return Rule(self, other)


class NegatedFormula(object):
    orig = None

    def __init__(self, orig):
        self.orig = orig

    def asConjunction(self):
        return [self]

    def variables(self):
        return self.orig.variables()

    def __repr__(self):
        return f"~{repr(self.orig)}"


class NegatedOracleFormula(object):
    orig = None

    def __init__(self, orig):
        self.orig = orig

    def asConjunction(self):
        return [self]

    def __and__(self, other):
        return Conjunction(*self.asConjunction(), *other.asConjunction())

    def variables(self):
        return self.orig.variables()


class OracleFormula(object):
    fn = None
    args = None

    def __init__(self, oracle, args):
        self.fn = oracle.fn
        self.args = args

    def asConjunction(self):
        return [self]

    def __and__(self, other):
        return Conjunction(*self.asConjunction(), *other.asConjunction())

    def __invert__(self):
        return NegatedOracleFormula(self)

    def variables(self):
        return frozenset(arg for arg in self.args if isinstance(arg, Variable))


class Program(object):
    rules = None
    strata = None
    initial = None
    always = None
    next = None

    def __init__(self, rules, name=None, fnmapping=dict(), reorderBodies=True):
        self.fnmapping = fnmapping
        rules = list(rule.asRule() for rule in rules)
        for rule in rules:
            if not rule.isRangeRestricted():
                raise ValueError("Rule Not Range Restricted", repr(rule))
        if reorderBodies:
            rules = list((Rule(head=rule.head, body=rule.body.reorder(
            )) if isinstance(rule.body, Conjunction) else rule)
                         for rule in rules)
        numberOfRules = len(rules)
        self.initial = []
        self.next = []
        self.always = []
        unstratified = []
        # Split Rules
        while rules:
            rule = rules.pop()
            if isinstance(rule.head, TempAnnotatedFormula):
                if rule.head.temporalAnnotation is start:
                    if rule.body is not None:
                        raise ValueError(
                            "Rule Body for start facts must be empty")
                    self.initial.append(rule)
                elif rule.head.temporalAnnotation is next:
                    self.next.append(rule)
                else:
                    raise ValueError("Unknown Temporal Annotation",
                                     rule.head.temporalAnnotation)
            elif isinstance(rule.head, Formula):
                if rule.body is None:
                    self.always.append(rule)
                elif isinstance(rule.body, OracleFormula) or isinstance(
                        rule.body, NegatedOracleFormula):
                    self.always.append(rule)
                elif isinstance(rule.body, Conjunction) and all(
                        isinstance(formula, OracleFormula)
                        or isinstance(formula, NegatedOracleFormula)
                        for formula in rule.body.asConjunction()):
                    self.always.append(rule)
                else:
                    unstratified.append(rule)
            elif isinstance(rule.head, CallFormula):
                self.next.append(rule)
            else:
                raise ValueError("Unsupported rule head", rule.head)
        assert numberOfRules == len(self.initial) + len(self.next) + len(
            self.always) + len(unstratified)
        # Create dependency graph
        deps = set()

        def make_edge(head, body):
            if isinstance(body, Formula) and head.fn != body.fn:
                deps.add((head.fn, 0, body.fn))
            elif isinstance(body, NegatedFormula):
                deps.add((head.fn, -1, body.orig.fn))
            else:
                pass

        print(unstratified)
        for rule in unstratified:
            assert rule.body is not None
            if isinstance(rule.body, Formula) or isinstance(
                    rule.body, NegatedFormula):
                make_edge(rule.head, rule.body)
            elif isinstance(rule.body, Conjunction):
                for lit in rule.body.asConjunction():
                    make_edge(rule.head, lit)
            else:
                raise ValueError("Unsupported Rule configuration", rule)
        print(deps)

    def run(self, cycles=None, cb=None, fnmapping=dict()):
        pass

    def run_cb(self, cycles=None, cb=None, fnmapping=dict()):
        pass

    def run_yield(self, cycles=None, fnmapping=dict()):
        pass


def relation(relname):
    return Relation(relname)


def variable(varname):
    return Variable(varname)


def variables(*varnames):
    return [Variable(varname) for varname in varnames]


def oracle(fn):
    return Oracle(fn)


def call(fn):
    return Call(fn)
