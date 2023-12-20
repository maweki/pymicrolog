from pymicrolog import *
import operator
import time

a = relation("a")
b = relation("b")
c = relation("c")
d = relation("d")
X = variable("X")
Y, Z = variables(*"YZ")
mylt = oracle(operator.lt)
tcall1 = call(time.time)
tcall2 = call("time")

rules = [
  a(2)@start,
  a(7)@start,
  a(12),
  b(1,2),
  a(0)@next,
  a(X)@next <= a(X) & ~mylt(5, X) & mylt(X, 5),
  b(X, X) <= a(X),
  b(X, X) <= b(X, ...),
  b(X, X) <= b(..., X),
  c() <= ~b(..., ...),
  d() <= a(...) & b(X, X),
  tcall1()@next <= a(2),
  tcall2()@next <= ~a(7),
]

p = Program(rules, name="Testprogram")
p.run(cycles=5, fnmapping={"time": time.time})
