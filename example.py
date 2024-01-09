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
  a(2)@START,
  a(7)@START,
  a(12),
  b(1,2),
  a(0)@NEXT,
  a(X)@NEXT <= a(X) & ~mylt(5, X) & mylt(X, 5),
  b(X, X) <= a(X),
  b(X, X) <= b(X, ...),
  b(X, X) <= b(..., X),
  c() <= ~b(..., ...),
  d() <= a(...) & b(X, X),
  b(X, Y) <= tcall1(X) & tcall2(Y),
  tcall1()@NEXT <= a(2),
  tcall2()@NEXT <= ~a(7),
]

s1 = [
  a(7)@START,
  a(X)@NEXT <= a(X),
]

s2 = [
  b(7, 5),
  b(8, 8),
  b(X, X) <= b(X, ...),
  d() <= b(X, X),
]

# for no, rule in enumerate(rules):
#   print("RULE", no, ":\t", rule)

p = Program(rules, name="Testprogram")
p.run(cycles=5, fnmapping={"time": time.time})

# print(mylt(5, X).apply_substitution({X: 7}).eval())
# data = set([(a, (5,5)),(a, (7,5))])
# for subst in a(Y, X).substitutions(data):
#     print(subst)
# print((~a(5, ...)).exists(data))
