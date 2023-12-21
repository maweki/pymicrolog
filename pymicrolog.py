from enum import Enum


class TemporalAnnotation(Enum):
    START = 1
    NEXT = 2

    def __repr__(self):
        if self == START:
            return "START"
        if self == NEXT:
            return "NEXT"
        return "???"


START = TemporalAnnotation.START
NEXT = TemporalAnnotation.NEXT


class Oracle():
    fn = None

    def __init__(self, fn):
        self.fn = fn

    def __call__(self, *args):
        return OracleFormula(self, args)


class Call():
    fn = None

    def __init__(self, fn):
        self.fn = fn

    def __call__(self, *args):
        return CallFormula(self, args)


class Conjunction():
    literals = None

    def __init__(self, *literals):
        self.literals = literals

    def reorder(self):

        def lit_order(lit):
            return [
                Formula, NegatedFormula, OracleFormula, NegatedOracleFormula
            ].index(type(lit))

        lits = list(self.literals)
        lits.sort(key=lit_order)
        return Conjunction(*lits)

    def as_conjunction(self):  # very bad name
        return list(self.literals)

    def __repr__(self):
        return " & ".join(repr(l) for l in self.literals)

    def __and__(self, other):
        return Conjunction(*self.as_conjunction(), *other.as_conjunction())

    def __invert__(self):
        raise ValueError("Cannot negate Conjunction")


class Variable():
    varname = None

    def __init__(self, varname):
        self.varname = varname

    def __repr__(self):
        return f"Var({self.varname})"


class Relation():
    relname = None

    def __init__(self, relname):
        self.relname = relname

    def __call__(self, *params):
        return Formula(self, params)

    def as_conjunction(self):
        raise ValueError("Missing ()?")

    def __invert__(self):
        raise ValueError("Missing ()?")

    def __le__(self, other):
        raise ValueError("Missing ()?")

    def __repr__(self):
        return f"R({self.relname})"


class Formula():
    fn = None
    args = None

    def __init__(self, fn, args):
        self.fn = fn
        self.args = tuple(args)

    def variables(self):
        return frozenset(arg for arg in self.args if isinstance(arg, Variable))

    def as_rule(self):
        return Rule(head=self)

    def as_conjunction(self):
        return [self]

    def __repr__(self):
        return f"{self.fn}{repr(self.args)}"

    def __and__(self, other):
        return Conjunction(*self.as_conjunction(), *other.as_conjunction())

    def __matmul__(self, other):  # @
        if not isinstance(other, TemporalAnnotation):
            raise NotImplementedError()
        return TempAnnotatedFormula(self, other)

    def __le__(self, other):
        return Rule(self, other)

    def __invert__(self):
        return NegatedFormula(self)

    def apply_substitution(self, substitution):
        new_args = [substitute_argument(arg, substitution) for arg in self.args]
        return Formula(self.fn, new_args)

    def substitutions(self, data, partial_substitutions=None):
        if partial_substitutions is None:
            partial_substitutions = {}
        matches = set()
        for rel, data_args in data:
            if rel != self.fn:
                continue
            for my_arg, data_arg in zip(self.args, data_args):
                if my_arg is Ellipsis:
                    continue
                if isinstance(my_arg, Variable):
                    match = (my_arg, data_arg)
                    if match in matches:
                        break
                    matches.add(match)
                if my_arg != data_arg:
                    break
            else:
                yield partial_substitutions
        for match in matches:
          partial = dict((match,))
          yield from self.apply_substitution(partial).substitutions(data, partial_substitutions | partial)


class Rule():
    head = None
    body = None

    def __init__(self, head, body=None):
        self.head = head
        self.body = body

    def __repr__(self):
        if self.body is None:
            return f"{repr(self.head)}."
        return f"{repr(self.head)} <- {repr(self.body)}."

    def as_rule(self):
        return self

    def is_range_restricted(self):
        if self.body is None:
            return not bool(self.head.variables())
        positives = set()
        dependents = set(self.head.variables())
        for lit in self.body.as_conjunction():
            if isinstance(lit, Formula):
                positives.update(lit.variables())
            else:
                dependents.update(lit.variables())
        return positives.issuperset(dependents)

    def variables(self):
        if self.body is None:
            return self.head.variables()
        return self.head.variables() | self.body.variables()


class TempAnnotatedFormula():
    fn = None
    args = None
    temporalAnnotation = None

    def __init__(self, formula, annotation):
        self.fn = formula.fn
        self.args = formula.args
        self.temporalAnnotation = annotation

    def as_rule(self):
        return Rule(head=self)

    def __le__(self, other):
        return Rule(self, other)

    def variables(self):
        return Formula(self.fn, self.args).variables()

    def __repr__(self):
        return f"{self.fn}{repr(self.args)}@{repr(self.temporalAnnotation)}"


class CallFormula():
    fn = None
    args = None

    def __init__(self, oracle, args):
        self.fn = oracle.fn
        self.args = args

    def variables(self):
        return frozenset(arg for arg in self.args if isinstance(arg, Variable))

    def __matmul__(self, other):
        if other is not NEXT:
            raise ValueError()
        return self

    def __le__(self, other):
        return Rule(self, other)


class NegatedFormula():
    orig = None

    def __init__(self, orig):
        self.orig = orig

    def as_conjunction(self):
        return [self]

    def variables(self):
        return self.orig.variables()

    def __repr__(self):
        return f"~{repr(self.orig)}"

    def exists(self, data): # bad name
        for _ in self.orig.substitutions(data):
          return True
        return False


class NegatedOracleFormula():
    orig = None

    def __init__(self, orig):
        self.orig = orig

    def as_conjunction(self):
        return [self]

    def __and__(self, other):
        return Conjunction(*self.as_conjunction(), *other.as_conjunction())

    def variables(self):
        return self.orig.variables()

    def __repr__(self):
        return '~'+repr(self.orig)

    def eval(self):
        return not self.orig.eval()

    def apply_substitution(self, substitution):
        new_args = [substitute_argument(arg, substitution) for arg in self.orig.args]
        return NegatedOracleFormula(self.orig, new_args)

def substitute_argument(arg, substitution):
    if isinstance(arg, Variable) and arg in substitution:
        return substitution[arg]
    return arg

class OracleFormula():
    fn = None
    args = None

    def __init__(self, oracle, args):
        self.fn = oracle.fn
        self.args = args

    def apply_substitution(self, substitution):
        new_args = [substitute_argument(arg, substitution) for arg in self.args]
        return OracleFormula(self, new_args)

    def as_conjunction(self):
        return [self]

    def __and__(self, other):
        return Conjunction(*self.as_conjunction(), *other.as_conjunction())

    def __invert__(self):
        return NegatedOracleFormula(self)

    def variables(self):
        return frozenset(arg for arg in self.args if isinstance(arg, Variable))

    def __repr__(self):
        return repr(self.fn) + repr(self.args)

    def eval(self):
        return self.fn(*self.args)


class Program():
    rules = None  # we can calculate this from the rest
    strata = None
    initial = None
    always = None
    next = None

    def __init__(self,
                 rules,
                 name=None,
                 fnmapping=dict(),
                 reorder_bodies=True):
        self.fnmapping = fnmapping
        rules = list(rule.as_rule() for rule in rules)
        for rule in rules:
            if not rule.is_range_restricted():
                raise ValueError("Rule Not Range Restricted", repr(rule))
        if reorder_bodies:
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
                if rule.head.temporalAnnotation is START:
                    if rule.body is not None:
                        raise ValueError(
                            "Rule Body for START facts must be empty")
                    self.initial.append(rule)
                elif rule.head.temporalAnnotation is NEXT:
                    self.next.append(rule)
                else:
                    raise ValueError("Unknown Temporal Annotation",
                                     rule.head.temporalAnnotation)
            elif isinstance(rule.head, Formula):
                if rule.body is None:
                    self.always.append(rule)
                elif isinstance(rule.body,
                                (OracleFormula, NegatedOracleFormula)):
                    self.always.append(rule)
                elif isinstance(rule.body, Conjunction) and all(
                        isinstance(formula, (OracleFormula,
                                             NegatedOracleFormula))
                        for formula in rule.body.as_conjunction()):
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
                deps.add((head.fn, 0, head.fn))
            elif isinstance(body, NegatedFormula):
                deps.add((head.fn, -1, body.orig.fn))
                deps.add((head.fn, 0, head.fn))
            else:
                pass

        for rule in unstratified:
            assert rule.body is not None
            if isinstance(rule.body, (Formula, NegatedFormula)):
                make_edge(rule.head, rule.body)
            elif isinstance(rule.body, Conjunction):
                for lit in rule.body.as_conjunction():
                    make_edge(rule.head, lit)
            else:
                raise ValueError("Unsupported Rule configuration", rule)

        # calculate a stratification
        strata = []
        while deps:  # Algorithm according to Ceri/Gottlob/Tanca 1990
            this_stratum = set(f for f, val, t in deps)
            for f, val, t in deps:
                if val == -1:
                    this_stratum.discard(f)
            strata.append(this_stratum)
            old_deps, deps = deps, set()
            while old_deps:
                f, val, t = old_deps.pop()
                if f in this_stratum or t in this_stratum:
                    continue
                deps.add((f, val, t))

        # select rules into strata
        self.strata = []
        for stratum in strata:
            this_stratum = []
            for rule in unstratified:
                if rule.head.fn in stratum:
                    this_stratum.append(rule)
            self.strata.append(this_stratum)
        assert sum(len(s) for s in self.strata) == len(
            unstratified)  # we did not forget a rule

    def run(self, cycles=None, cb=None, fnmapping=None):
        fnmapping = {} if fnmapping is None else fnmapping

        initial_facts = initial_facts_to_model(self.initial)
        print(initial_facts)
        s0 = apply_rules(self.always, initial_facts)
        print(s0)



    def run_cb(self, cycles=None, cb=None, fnmapping={}):
        pass

    def run_yield(self, cycles=None, fnmapping={}):
        pass

def formula_to_fact(formula):
    return (formula.fn, formula.args)

def initial_facts_to_model(init):
    return set(formula_to_fact(rule.head) for rule in init)

def apply_rules(rules, model):
    new_facts = set()
    for rule in rules:
        if rule.body is None:
            new_facts.add(formula_to_fact(rule.head))
        body = rule.body.as_conjunction()
        print(body)
    return new_facts - model

def step(rules_always, rules_stratified, rules_next, init, fnmapping):
    changed = False


    return init




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
