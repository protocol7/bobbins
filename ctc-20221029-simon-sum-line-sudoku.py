from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=UVXyMBCsv7Q

LINES = [
    [(0, 0), (0, 1), (1, 2), (0, 2), (1, 1), (2, 2)],
    [(1, 0), (2, 0), (3, 0), (3, 1), (2, 1)],
    [(5, 0), (4, 0), (4, 1), (3, 2)],
    [(6, 2), (5, 2), (5, 1), (4, 2), (5, 3)],
    [(7, 1), (8, 2), (7, 3)],
    [(3, 3), (3, 4), (2, 5)],
    [(0, 4), (0, 5), (0, 6), (1, 7), (1, 6), (1, 5), (0, 4), (0, 5)],
    [(3, 5), (4, 6), (5, 5)],
    [(6, 5), (7, 5), (8, 5)],
    [(3, 6), (3, 7), (3, 8)],
    [(4, 7), (5, 6), (6, 6), (6, 7), (6, 8), (5, 8)],
]


def sum_line(s, cells):
    for line in LINES:
        for (c0, r0), (c1, r1), (c2, r2) in zip(line, line[1:], line[2:]):
            v0 = cells[r0][c0]
            v1 = cells[r1][c1]
            v2 = cells[r2][c2]

            s.add(z3.Or(v0 == v1 + v2, v1 == v0 + v2, v2 == v0 + v1))


s = (
    Solver()
    .extra_constraint(sum_line)
)
solution = s.solve()

Solver.pretty_print(solution)
