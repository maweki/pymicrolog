from pymicrolog import *

board = {}

setup = relation("setup")
setup_rules = [ setup()@START ]

winner = relation("winner")
phase = relation("phase")
phase_rules = [
    phase("print")@NEXT <= setup(),
    phase("ask")@NEXT <= phase("print") & ~winner(...),
    phase("gather")@NEXT <= phase("ask") & ~winner(...),
    phase("print")@NEXT <= phase("gather") & ~winner(...),
    phase("halt")@NEXT <= winner(...),
]

player = relation("player")
current_player = relation("current_player")
player_facts = [ player(1), player(2), current_player(1)@START ]

column = relation("column")
column_facts = [column(x) for x in range(7)]

row = relation("row")
row_facts = [row(x) for x in range(6)]

top_of = relation("top_of")
top_of_facts = [top_of(X+1,X) for X in range(5)]

besides = relation("besides")
besides_facts = [besides(X+1,X) for X in range(6)]

C, R, P = variables(*"CRP")
C1, C2, C3, C4 = variables("C1", "C2", "C3", "C4")
R1, R2, R3, R4 = variables("R1", "R2", "R3", "R4")
P2 = variable("R2")

marker = relation("marker")
new_marker = relation("new_marker")
dropped = relation("dropped")
set_board = call(lambda C, R, P: board.update({(C,R):P}))
marker_rules = [
    marker(C, R, 0) <= setup() & row(R) & column(C),
    new_marker(C, 0, P) <= dropped(P, C) & marker(C, 0, 0),
    new_marker(C, R, P) <= dropped(P, C) & ~marker(C, 0, 0) & marker(C, R, 0) & top_of(R, R2) & ~marker(C, R2, 0),
    marker(C, R, P)@NEXT <= marker(C, R, P) & ~new_marker(C, R, ...),
    marker(C, R, P)@NEXT <= new_marker(C, R, P),
    set_board(C, R, P)@NEXT <= marker(C, R, P) & ~new_marker(C, R, ...),
    set_board(C, R, P)@NEXT <= new_marker(C, R, P),
]

ask_column = call((lambda P: int(input("Player {}: Which column to drop in? ".format(P)))))
announce = call(print)
get_drop_rule = [
    ask_column(P)@NEXT <= phase("ask") & current_player(P),
    dropped(P, C) <= current_player(P) & player(P) & ask_column(P, C) & column(C) & marker(C, ..., 0),
    current_player(P2)@NEXT <= dropped(...,...) & player(P2) & ~current_player(P2),
    current_player(P)@NEXT <= ~dropped(...,...) & current_player(P),
]

winner_rules = [
  winner(P) <= player(P) & marker(C1, R, P) & besides(C1, C2) & besides(C2, C3) & besides(C3, C4) & marker(C2, R, P) & marker(C3, R, P) & marker(C4, R, P),
  winner(P) <= player(P) & marker(C, R1, P) & top_of(R1, R2) & top_of(R2, R3) & top_of(R3, R4) & marker(C, R2, P) & marker(C, R3, P) & marker(C, R4, P),
  winner(P) <= player(P) & marker(C1, R1, P)  & top_of(R1, R2) & top_of(R2, R3) & top_of(R3, R4) & besides(C1, C2) & besides(C2, C3) & besides(C3, C4) & marker(C2, R2, P) & marker(C3, R3, P) & marker(C4, R4, P),
  winner(P) <= player(P) & marker(C1, R1, P)  & top_of(R1, R2) & top_of(R2, R3) & top_of(R3, R4) & besides(C2, C1) & besides(C3, C2) & besides(C4, C3) & marker(C2, R2, P) & marker(C3, R3, P) & marker(C4, R4, P),
  announce("Player", P, "has won")@NEXT <= winner(P),
]

all_rules = setup_rules + player_facts + column_facts + row_facts + top_of_facts + besides_facts + marker_rules + get_drop_rule + phase_rules + winner_rules
p = Program(all_rules)

for s in p.run_generator(extended_state=True):
    if (phase, ("halt",)) in s:
      break
    if (phase, ("print",)) in s:
      print("=======")
      print("0123456")
      print("-------")

      for Y in range(5, -1, -1):
          for X in range(7):
              print(board[(X, Y)], end="")
          print("")
      print("")
