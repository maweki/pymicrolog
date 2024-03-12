from pymicrolog import *

# ALGORITHM STRATIFY from Logic Programming and Databases, Ceri/Gottlob/Tanca

A, B, C, V, S, R = variables(*"ABCVSR")

edg = relation("edg")
current_stratum = relation("current_stratum")
rel = relation("rel")

data = [
  edg("safely_connected", "connected", 0)@START,
  edg("safely_connected", "existscutpoint", -1)@START,
  edg("existscutpoint", "station", 0)@START,
  edg("existscutpoint", "cutpoint", 0)@START,
  edg("cutpoint", "station", 0)@START,
  edg("cutpoint", "circumvent", -1)@START,
  edg("cutpoint", "connected", 0)@START,
  edg("circumvent", "circumvent", 0)@START,
  edg("circumvent", "linked", 0)@START,
  edg("connected", "connected", 0)@START,
  edg("station", "linked", 0)@START,
  edg("connected", "linked", 0)@START,
  rel(R) <= edg(R, ..., ...),
  rel(R) <= edg(..., R, ...),
]

reachable = relation("reachable")
reachable_rules = [
  reachable(A, A, 0) <= edg(A, ..., ...),
  reachable(A, A, 0) <= edg(..., A, ...),
  reachable(A, B, V) <= edg(A, B, V),
  reachable(A, C, 0) <= reachable(A, B, 0) & reachable(B, C, 0),
  reachable(A, C, -1) <= reachable(A, B, ...) & reachable(B, C, -1),
  reachable(A, C, -1) <= reachable(A, B, -1) & reachable(B, C, ...),
]

edgs = relation("edg*")
del_edgs = relation("del:edg*")
edgs_rules = [
  edgs(A, B, -1) <= reachable(A, B, -1),
  edgs(A, B, 0) <= edg(A, B, 0) & ~reachable(A, B, -1),
  edgs(A, B, V)@NEXT <= edgs(A, B, V) & ~del_edgs(A, B, ...),
]

def _stratum_out(stratum, relation):
  print(stratum, relation)
  return stratum + 1

stratum_out = call(_stratum_out)
stratum = relation("stratum")
identify_rules = [
  stratum(S, R) <= rel(R) & ~edgs(R, ..., -1) & current_stratum(S), # set k of no outgoing ~edge
  del_edgs(B, V, C) <= stratum(..., V) & edgs(B, V, C), # delete them
  rel(V)@NEXT <= rel(V) & ~stratum(..., V),
  stratum_out(S, V)@NEXT <= stratum(S, V),
  current_stratum(1)@START,
  current_stratum(V) <= stratum_out(..., ..., V),
]

p = Program(rules=data + reachable_rules + edgs_rules + identify_rules)
for x in p.run_generator():
  if not x:
    break
