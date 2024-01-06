from solver import Solver
from loops import loop, pretty_print
import z3

# https://www.youtube.com/watch?v=OpVCpxuCP98

CAGES = [
  ([(0, 0), (1, 0)], 7),
  ([(7, 0), (8, 0)], 13),
  ([(4, 2), (4, 3)], 7),
  ([(6, 7), (7, 7)], 7),
  ([(1, 8), (2, 8)], 13),
]

z3_solver = None
loop_grid = None
solver = Solver(Solver.EMPTY)


def loops(s, vars):
    global z3_solver, loop_grid

    z3_solver = s

    cage_cells = [cell for cage, _ in CAGES for cell in cage]

    # cells will be > 0 if part of the loop
    loop_grid = loop(s, must_include_cells=cage_cells)

    for r in range(9):
        for c in range(9):
            v = vars[r][c]
            l = loop_grid[r][c]

            for nc, nr in solver.orthogonal(c, r):
                nv = vars[nr][nc]
                nl = loop_grid[nr][nc]

                s.add(z3.Or(
                    l == 0,  # this is not loop
                    nl == 0,  # neighbour is not loop
                    z3.And(
                        l > 0,
                        nl > 0,
                        z3.Or(
                            z3.And(v > 5, nv < 5),
                            z3.And(v < 5, nv > 5),
                        )
                    )
                ))


solver.white_kropkis([
        [(6, 2), (6, 3)],
        [(2, 3), (3, 3)],
        [(2, 4), (2, 5)],
        [(4, 4), (4, 5)],
        [(5, 5), (6, 5)],
        [(5, 7), (5, 8)],
    ])

for cage, sum in CAGES:
    solver.killer_cage(cage, sum)

solver.extra_constraint(loops)

solution = solver.solve()

Solver.pretty_print(solution)

print()

# print the loop as well
pretty_print(z3_solver, loop_grid)
