from enum import Enum

class TemporalAnnotation(Enum):
  start = 1
  next = 2
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
      return [Formula, NegatedFormula, OracleFormula, NegatedOracleFormula].index(type(lit))
    lits = list(self.literals)
    lits.sort(key=litOrder)
    return Conjunction(*lits)

  def asConjunction(self): # very bad name
    return list(self.literals)

  def __and__(self, other):
    return Conjunction(*self.asConjunction(), *other.asConjunction())

  def __invert__(self):
    raise ValueError("Cannot negate Conjunction")

class Variable(object):
  varname = None

  def __init__(self, varname):
    self.varname = varname

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

class Formula(object):
  fn = None
  args = None
  def __init__(self, fn, args):
    self.fn = fn
    self.args = args

  def asRule(self):
    return Rule(head=self)

  def asConjunction(self):
    return [self]

  def __and__(self, other):
    return Conjunction(*self.asConjunction(), *other.asConjunction())

  def __matmul__(self, other): # @
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

  def asRule(self):
    return self

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

class CallFormula(object):
  fn = None
  args = None
  def __init__(self, oracle, args):
    self.fn = oracle.fn
    self.args = args

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

class NegatedOracleFormula(object):
  orig = None
  def __init__(self, orig):
    self.orig = orig

  def asConjunction(self):
    return [self]

  def __and__(self, other):
    return Conjunction(*self.asConjunction(), *other.asConjunction())

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

class Program(object):
  rules = None
  strata = None
  initial = None
  next = None
  def __init__(self, rules, name=None, fnmapping=dict(), reorderBodies=True):
    self.fnmapping = fnmapping
    rules = list(rule.asRule() for rule in rules)
    if reorderBodies:
      rules = list((Rule(head=rule.head, body=rule.body.reorder()) if isinstance(rule.body, Conjunction) else rule) for rule in rules)
    numberOfRules = len(rules)
    self.initial = []
    self.next = []
    unstratified = []
    while rules:
      rule = rules.pop()
      if isinstance(rule.head, TempAnnotatedFormula):
        if rule.head.temporalAnnotation is start:
          self.initial.append(rule)
        elif rule.head.temporalAnnotation is next:
          self.next.append(rule)
        else:
          raise ValueError("Unknown Temporal Annotation", rule.head.temporalAnnotation)
      elif isinstance(rule.head, Formula):
        if rule.body is None:
          self.initial.append(rule)
        elif isinstance(rule.body, OracleFormula) or isinstance(rule.body, NegatedOracleFormula):
          self.initial.append(rule)
        else:
          unstratified.append(rule)
      elif isinstance(rule.head, CallFormula):
        self.next.append(rule)
      else:
        raise ValueError("Unsupported rule head", rule.head)
    assert numberOfRules == len(self.initial) + len(self.next) + len(unstratified)

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
