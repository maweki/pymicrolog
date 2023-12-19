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

  def asConjunction(self):
    return list(self.literals)

  def __and__(self, other):
    return Conjunction(*self.asConjunction(), *other.asConjunction())

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

class Formula(object):
  fn = None
  args = None
  def __init__(self, fn, args):
    self.fn = fn
    self.args = args

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

class Rule(object):
  head = None
  body = None
  def __init__(self, head, body=None):
    self.head = head
    self.body = body

class TempAnnotatedFormula(object):
  fn = None
  args = None
  temporalAnnotation = None
  def __init__(self, formula, annotation):
    self.fn = formula.fn
    self.args = formula.args
    self.temporalAnnotation = annotation

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

def relation(relname):
  return Relation(relname)

def variable(varname):
  return Variable(varname)

def oracle(fn):
  return Oracle(fn)

def call(fn):
  return Call(fn)
