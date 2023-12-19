from pymicrolog import *
import operator
import time

a = relation("a")
X = variable("X")
mylt = oracle(operator.lt)
tcall = call(time.time)

rules = [
  a (2) @ start,
  a (7) @ start,
  a (X) @ next <= a (X) & mylt (X, 5),
  tcall () @ next <= a (2),
]
print(rules)
