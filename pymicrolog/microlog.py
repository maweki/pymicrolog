from enum import Enum
from itertools import zip_longest

class TemporalAnnotation(Enum):
    START = 1
    NEXT = 2

    def __repr__(self):
        if self == START:
            return "START"
        if self == NEXT:
            return "NEXT"
        raise NotImplementedError()


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
                Formula, CallFormula, NegatedFormula, NegatedCallFormula, OracleFormula, NegatedOracleFormula
            ].index(type(lit))

        lits = list(self.literals)
        lits.sort(key=lit_order)
        return Conjunction(*lits)

    def substitutions(self, data, partial_substitutions=None, fnmapping=None):
        partial_substitutions = {} if partial_substitutions is None else partial_substitutions
        fnmapping = {} if fnmapping is None else fnmapping
        if len(self.literals) == 0:
            yield partial_substitutions
            return
        first_lit, *rest = self.literals
        for subst in first_lit.substitutions(data, partial_substitutions, fnmapping):
            full_subst = {**subst, **partial_substitutions}
            new_conjunction = Conjunction(*[other_lits.apply_substitution(full_subst) for other_lits in rest])
            yield from new_conjunction.substitutions(data, partial_substitutions=full_subst, fnmapping=fnmapping)

    def as_list(self):  # very bad name
        return list(self.literals)

    def __repr__(self):
        return " & ".join(repr(l) for l in self.literals)

    def __and__(self, other):
        return Conjunction(*self.as_list(), *other.as_list())

    def __invert__(self):
        raise ValueError("Cannot negate Conjunction")


class Variable():
    varname = None

    def __init__(self, varname):
        self.varname = varname

    def __hash__(self):
        return hash((Variable, self.varname))

    def __repr__(self):
        return "Var({})".format(self.varname)

    def __lt__(self, other):
        import operator
        return oracle(operator.lt)(self, other)

    def __le__(self, other):
        import operator
        return oracle(operator.le)(self, other)

    def __eq__(self, other):
        import operator
        return oracle(operator.eq)(self, other)

    def __ne__(self, other):
        import operator
        return oracle(operator.ne)(self, other)

    def __ge__(self, other):
        import operator
        return oracle(operator.ge)(self, other)

    def __gt__(self, other):
        import operator
        return oracle(operator.gt)(self, other)


class Relation():
    relname = None

    def __init__(self, relname):
        self.relname = relname

    def __call__(self, *params):
        return Formula(self, params)

    def as_list(self):
        raise ValueError("Missing ()?")

    def __invert__(self):
        raise ValueError("Missing ()?")

    def __le__(self, other):
        raise ValueError("Missing ()?")

    def __repr__(self):
        return "R({})".format(self.relname)


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

    def as_list(self):
        return [self]

    def __repr__(self):
        return "{}{}".format(self.fn, repr(self.args))

    def __and__(self, other):
        return Conjunction(*self.as_list(), *other.as_list())

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

    def as_fact(self):
        if self.variables():
            raise ValueError("Variables in Formula.", self, "not Factable.")
        if Ellipsis in self.args:
            raise ValueError("Ellipsis in Formula.", self, "not Factable.")
        return (self.fn, self.args)

    def substitutions(self, data, partial_substitutions=None, fnmapping=None):
        partial_substitutions = {} if partial_substitutions is None else partial_substitutions
        fnmapping = {} if fnmapping is None else fnmapping
        matches = set()
        for rel, data_args in data:
            if fnmapping.get(rel, rel) != fnmapping.get(self.fn, self.fn):
                continue
            # this data matches function symbol
            bound_variables = set()
            single_match = set()
            for my_arg, data_arg in zip_longest(self.args, data_args):
                if my_arg is Ellipsis:
                    continue
                if isinstance(my_arg, Variable):
                    var_match = (my_arg, data_arg)
                    single_match.add(var_match)
                    bound_variables.add(my_arg)
                    continue
                elif my_arg != data_arg:
                    break
            else:
                if len(bound_variables) == len(single_match):
                    matches.add(frozenset(single_match))
        for match in matches:
          yield {**dict(match), **partial_substitutions}

class Rule():
    head = None
    body = None

    def __init__(self, head, body=None):
        self.head = head
        self.body = body

    def __repr__(self):
        if self.body is None:
            return "{}.".format(repr(self.head))
        return "{} <- {}.".format(repr(self.head), repr(self.body))

    def as_rule(self):
        return self

    def is_range_restricted(self):
        if self.body is None:
            return not bool(self.head.variables())
        positives = set()
        dependents = set(self.head.variables())
        for lit in self.body.as_list():
            if isinstance(lit, (Formula, CallFormula)):
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
        return "{}{}@{}".format(self.fn, repr(self.args), repr(self.temporalAnnotation))

    def apply_substitution(self, substitution):
        return TempAnnotatedFormula(Formula(self.fn, self.args).apply_substitution(substitution), self.temporalAnnotation)


class CallFormula():
    fn = None
    args = None

    def __init__(self, oracle, args):
        self.fn = oracle.fn
        self.args = tuple(args)

    def as_rule(self):
        return Rule(head=self)

    def variables(self):
        return frozenset(arg for arg in self.args if isinstance(arg, Variable))

    def __matmul__(self, other):
        if other is not NEXT:
            raise ValueError()
        return self

    def __invert__(self):
        return NegatedCallFormula(self)

    def __le__(self, other):
        return Rule(self, other)

    def __and__(self, other):
        return Conjunction(*self.as_list(), *other.as_list())

    def as_list(self):
        return [self]

    def apply_substitution(self, substitution):
        new_args = [substitute_argument(arg, substitution) for arg in self.args]
        return CallFormula(self, new_args)

    def substitutions(self, data, partial_substitutions=None, fnmapping=None):
        partial_substitutions = {} if partial_substitutions is None else partial_substitutions
        fnmapping = {} if fnmapping is None else fnmapping
        fn = fnmapping[self.fn] if self.fn in fnmapping else self.fn
        yield from Formula(fn, self.args).substitutions(data, partial_substitutions, fnmapping)
        # Here we need to package the call

class NegatedCallFormula():
    orig = None

    def __init__(self, orig):
        self.orig = orig

    def as_list(self):
        return [self]

    def variables(self):
        return self.orig.variables()

    def __repr__(self):
        return "~{}".format(repr(self.orig))

    def __and__(self, other):
        return Conjunction(*self.as_list(), *other.as_list())

    def apply_substitution(self, substitution):
        return NegatedCallFormula(self.orig.apply_substitution(substitution))

    def substitutions(self, data, partial_substitutions=None, fnmapping=None):
        partial_substitutions = {} if partial_substitutions is None else partial_substitutions
        fnmapping = {} if fnmapping is None else fnmapping
        for _ in self.orig.substitutions(data, partial_substitutions, fnmapping):
            return
        yield partial_substitutions

class NegatedFormula():
    orig = None

    def __init__(self, orig):
        self.orig = orig

    def as_list(self):
        return [self]

    def variables(self):
        return self.orig.variables()

    def __repr__(self):
        return "~{}".format(repr(self.orig))

    def __and__(self, other):
        return Conjunction(*self.as_list(), *other.as_list())

    def apply_substitution(self, substitution):
        return NegatedFormula(self.orig.apply_substitution(substitution))

    def substitutions(self, data, partial_substitutions=None, fnmapping=None):
        partial_substitutions = {} if partial_substitutions is None else partial_substitutions
        fnmapping = {} if fnmapping is None else fnmapping
        for _ in self.orig.substitutions(data, partial_substitutions, fnmapping):
            return
        yield partial_substitutions


class NegatedOracleFormula():
    orig = None

    def __init__(self, orig):
        self.orig = orig

    def as_list(self):
        return [self]

    def __and__(self, other):
        return Conjunction(*self.as_list(), *other.as_list())

    def variables(self):
        return self.orig.variables()

    def __repr__(self):
        return '~'+repr(self.orig)

    def eval(self):
        return not self.orig.eval()

    def apply_substitution(self, substitution):
        substituted = self.orig.apply_substitution(substitution)
        return ~substituted

    def substitutions(self, data, partial_substitutions=None, fnmapping=None):
        partial_substitutions = {} if partial_substitutions is None else partial_substitutions
        fnmapping = {} if fnmapping is None else fnmapping
        for _ in self.orig.substitutions(data, partial_substitutions, fnmapping):
            return
        yield partial_substitutions

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

    def as_list(self):
        return [self]

    def __and__(self, other):
        return Conjunction(*self.as_list(), *other.as_list())

    def __invert__(self):
        return NegatedOracleFormula(self)

    def variables(self):
        return frozenset(arg for arg in self.args if isinstance(arg, Variable))

    def __repr__(self):
        return repr(self.fn) + repr(self.args)

    def eval(self):
        return self.fn(*self.args)

    def substitutions(self, data, partial_substitutions=None, fnmapping=None):
        partial_substitutions = {} if partial_substitutions is None else partial_substitutions
        fnmapping = {} if fnmapping is None else fnmapping
        fn = fnmapping[self.fn] if self.fn in fnmapping else self.fn
        if fn(*self.args):
            yield partial_substitutions

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
                        for formula in rule.body.as_list()):
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
            if isinstance(body, Formula):
                deps.add((head.fn, 0, body.fn))
            elif isinstance(body, NegatedFormula):
                deps.add((head.fn, -1, body.orig.fn))
            else:
                pass

        for rule in unstratified:
            assert rule.body is not None
            if isinstance(rule.body, (Formula, NegatedFormula)):
                make_edge(rule.head, rule.body)
            elif isinstance(rule.body, Conjunction):
                for lit in rule.body.as_list():
                    make_edge(rule.head, lit)
            elif isinstance(rule.body, CallFormula):
                pass
            else:
                raise ValueError("Unsupported Rule configuration", rule)

        # calculate reachability
        import itertools
        rels = set(f for f, val, t in deps) | set(t for f, val, t in deps)
        edeps = set()
        for r in rels:
          reachable = {r: 0}
          while True:
            traversal = (len(reachable), sum(reachable.values()))
            for df, v, dt in deps:
              if df in reachable:
                reachable[dt] = min(v, reachable.get(dt, 0), reachable.get(df, 0))
            if traversal == (len(reachable), sum(reachable.values())):
              break
          for reach in reachable:
            edeps.add((r, reachable[reach] ,reach))
        deps = edeps

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

    def run(self, cycles=None, fnmapping=None):
        for iofacts in self.run_generator(cycles, fnmapping):
            pass

    def run_cb(self, cycles=None, cb=None, fnmapping=None, extended_state=False):
        for iofacts in self.run_generator(cycles, fnmapping, extended_state):
            cb(iofacts)

    def run_generator(self, cycles=None, fnmapping=None, extended_state=False):
        fnmapping = {} if fnmapping is None else fnmapping
        fnmapping = {**self.fnmapping, **fnmapping}

        initial_facts = initial_facts_to_model(self.initial)
        model = initial_facts
        while True:
            if cycles == 0:
                break
            for stratum in [self.always] + self.strata:
                while True:
                    new_facts = apply_rules(stratum, model, fnmapping)
                    if not new_facts - model:
                        break
                    model = model | new_facts
            tentative_next_model = apply_rules(self.next, model, fnmapping)
            next_model = set()
            iofacts = set()
            for fact_head, fact_args in tentative_next_model:
                if isinstance(fact_head, Relation):
                    next_model.add((fact_head, fact_args))
                elif callable(fact_head):
                    return_value = fact_head(*fact_args)
                    if isinstance(return_value, tuple):
                        iofact = (fact_head, fact_args + return_value)
                    else:
                        iofact = (fact_head, fact_args + (return_value,))
                    iofacts.add(iofact)
            model = next_model | iofacts
            if extended_state:
                yield frozenset(model)
            else:
                yield frozenset(iofacts)
            if cycles is not None:
                cycles = cycles - 1

def formula_to_fact(formula, fnmapping=None):
    fnmapping = {} if fnmapping is None else fnmapping
    fn = fnmapping[formula.fn] if formula.fn in fnmapping else formula.fn
    return (fn, formula.args)

def initial_facts_to_model(init):
    return set(formula_to_fact(rule.head) for rule in init)

def apply_rules(rules, model, fnmapping=None):
    fnmapping = {} if fnmapping is None else fnmapping
    new_facts = set()
    for rule in rules:
        if rule.body is None:
            new_facts.add(formula_to_fact(rule.head, fnmapping=fnmapping))
            continue
        for subst in rule.body.substitutions(model, fnmapping=fnmapping):
            new_facts.add(formula_to_fact(rule.head.apply_substitution(subst), fnmapping=fnmapping))
    return new_facts

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
