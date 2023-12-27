from solver import Solver
import z3

# https://www.youtube.com/watch?v=3rwa9GtLeMI

LINES = [
    [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)],
    [(3, 0), (2, 0), (1, 0), (1, 1), (1, 2), (2, 2), (3, 2), (3, 1)],
    [(4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5)],
    [(0, 6), (0, 5), (1, 5), (1, 4), (1, 3), (2, 3), (2, 4), (3, 4), (3, 3)],
    [(0, 7), (0, 8), (1, 7), (1, 8), (2, 8), (3, 8), (4, 8)],
    [(4, 7), (3, 7), (2, 7), (1, 6), (2, 5), (3, 5), (4, 6)],
    [(5, 8), (5, 7), (5, 6), (6, 7), (6, 6), (6, 5)],
    [(6, 1), (6, 0), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, 5),
     (8, 6), (7, 6), (7, 7), (8, 7), (8, 8), (7, 8)],
    [(8, 0), (8, 1), (8, 2), (8, 3), (8, 4)],
]


def sumthing(s, cells):
    for line in LINES:
        yline = line[::-1]
        xc, xr = line[0]
        yc, yr = line[-1]
        xv = cells[xr][xc]
        yv = cells[yr][yc]

        constrains = []
        for x in range(1, len(line) + 1):
            xvars = [cells[r][c] for c, r in line[:x]]
            for y in range(1, len(line) + 1):
                yvars = [cells[r][c] for c, r in yline[:y]]
                constrains.append(z3.And(xv == x, yv == y, z3.Sum(xvars) == z3.Sum(yvars)))

        s.add(z3.Or(constrains))


s = (
    Solver(Solver.EMPTY)
    .extra_constraint(sumthing)
)
solution = s.solve()

Solver.pretty_print(solution)
