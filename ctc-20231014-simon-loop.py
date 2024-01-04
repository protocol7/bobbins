from solver import Solver
from loops import loop, pretty_print
import z3

# https://www.youtube.com/watch?v=hgx0Rso7JNs

THERMOS = [
  [(0, 0), (1, 0), (0, 1)],
  [(4, 0), (3, 1), (2, 1)],
  [(8, 0), (8, 1), (7, 0)],
  [(7, 2), (6, 3)],
  [(0, 4), (0, 3)],
  [(8, 4), (8, 5), (8, 6)],
  [(1, 5), (0, 4)],
  [(0, 8), (1, 7), (2, 8), (1, 8)],
  [(3, 8), (3, 7), (3, 6), (3, 5)],
  [(5, 8), (5, 7)],
  [(7, 8), (7, 7), (8, 8), (8, 7)]
]

z3_solver = None
loop_grid = None


def loops(s, vars):
    global z3_solver, loop_grid

    z3_solver = s

    bulbs = [thermo[0] for thermo in THERMOS]

    # cells will be > 0 if part of the loop
    loop_grid = loop(s, must_include_cells=bulbs)

    vs = [[vars[r][c], loop_grid[r][c]] for r in range(9) for c in range(9)]

    # Each digit on the loop indicates exactly how many times that digit
    # appears on the loop.
    # Eg: If there's a 5 on the loop, it means there are five 5s on the loop
    for digit in range(1, 10):
        count = z3.Sum([z3.If(z3.And(v == digit, l > 0), 1, 0) for v, l in vs])

        s.add(z3.Or(count == digit, count == 0))


s = (
    Solver(Solver.EMPTY)
    .white_kropkis([
        [(6, 0), (6, 1)],
        [(6, 3), (7, 3)],
        [(5, 3), (5, 4)],
        [(1, 7), (2, 7)],
    ])
)

for thermo in THERMOS:
    s.thermo(thermo)

s.extra_constraint(loops)

solution = s.solve()

Solver.pretty_print(solution)

print()

# print the loop as well
pretty_print(z3_solver, loop_grid)
