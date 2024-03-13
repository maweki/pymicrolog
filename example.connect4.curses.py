from pymicrolog import *
import curses
import sys
stdscr = curses.initscr()
curses.noecho()
curses.cbreak()
stdscr.keypad(True)

def _exit(code):
    curses.nocbreak()
    stdscr.keypad(False)
    curses.echo()
    stdscr.getch()
    curses.endwin()
    sys.exit(code)

exit = call(_exit)
print_marker = call(lambda x, y, ch: stdscr.addch(10-y, x, str(ch)))
get_input = call(lambda : stdscr.getch(0,0))
desired_column = relation("desired_column")
tried_desired_column = relation("tried_desired_column")
refresh = call(stdscr.refresh)

setup = relation("setup")
setup_rules = [ setup()@START ]

winner = relation("winner")
phase = relation("phase")
phase_rules = [
    phase("out")@NEXT <= setup(),
    phase("settle_out")@NEXT <= phase("out"),
    phase("in")@NEXT <= phase("settle_out"),
    phase("settle_in")@NEXT <= phase("in"),
    phase("out")@NEXT <= phase("settle_in"),
    get_input()@NEXT <= phase("in") & ~winner(...),
    desired_column(0) <= setup(),
    refresh()@NEXT <= phase("settle_in"),
    refresh()@NEXT <= phase("settle_out"),
    exit(0)@NEXT <= phase("settle_in") & winner(...),
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
marker_rules = [
    marker(C, R, 0) <= setup() & row(R) & column(C),
    new_marker(C, 0, P) <= dropped(P, C) & marker(C, 0, 0),
    new_marker(C, R, P) <= dropped(P, C) & ~marker(C, 0, 0) & marker(C, R, 0) & top_of(R, R2) & ~marker(C, R2, 0),
    marker(C, R, P)@NEXT <= marker(C, R, P) & ~new_marker(C, R, ...),
    marker(C, R, P)@NEXT <= new_marker(C, R, P),
    print_marker(C, R, P)@NEXT <= marker(C, R, P) & ~new_marker(C, R, ...) & phase("out"),
    print_marker(C, R, P)@NEXT <= new_marker(C, R, P) & phase("out"),
    print_marker(C, 8, P)@NEXT <= current_player(P) & desired_column(C) & phase("out"),
    print_marker(C, 8, " ")@NEXT <= column(C) & current_player(P) & ~desired_column(C) & phase("out"),
]

announce = call(lambda *a: stdscr.addstr(12,0, ' '.join(map(str,a))))
get_drop_rule = [
    tried_desired_column(C2) <= get_input(curses.KEY_RIGHT) & desired_column(C1) & besides(C2, C1),
    tried_desired_column(C2) <= get_input(curses.KEY_LEFT) & desired_column(C1) & besides(C1, C2),
    desired_column(C)@NEXT <= desired_column(C) & ~tried_desired_column(...),
    desired_column(C)@NEXT <= tried_desired_column(C),
    dropped(P, C) <= current_player(P) & player(P) & desired_column(C) & get_input(curses.KEY_DOWN) & column(C) & marker(C, ..., 0),
    current_player(P2)@NEXT <= dropped(...,...) & player(P2) & ~current_player(P2),
    current_player(P)@NEXT <= ~dropped(...,...) & current_player(P),
]

winner_rules = [
  winner(P) <= player(P) & marker(C1, R, P) & besides(C1, C2) & besides(C2, C3) & besides(C3, C4) & marker(C2, R, P) & marker(C3, R, P) & marker(C4, R, P),
  winner(P) <= player(P) & marker(C, R1, P) & top_of(R1, R2) & top_of(R2, R3) & top_of(R3, R4) & marker(C, R2, P) & marker(C, R3, P) & marker(C, R4, P),
  winner(P) <= player(P) & marker(C1, R1, P)  & top_of(R1, R2) & top_of(R2, R3) & top_of(R3, R4) & besides(C1, C2) & besides(C2, C3) & besides(C3, C4) & marker(C2, R2, P) & marker(C3, R3, P) & marker(C4, R4, P),
  winner(P) <= player(P) & marker(C1, R1, P)  & top_of(R1, R2) & top_of(R2, R3) & top_of(R3, R4) & besides(C2, C1) & besides(C3, C2) & besides(C4, C3) & marker(C2, R2, P) & marker(C3, R3, P) & marker(C4, R4, P),
  announce("Player", P, "has won\n\n")@NEXT <= winner(P),
  winner(P)@NEXT <= winner(P),
]

all_rules = setup_rules + player_facts + column_facts + row_facts + top_of_facts + besides_facts + marker_rules + get_drop_rule + phase_rules + winner_rules
p = Program(all_rules)

p.run()
