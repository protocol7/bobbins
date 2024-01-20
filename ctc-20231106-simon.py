from solver import Solver, _
import z3
from utils import z3_count

# https://www.youtube.com/watch?v=h1wS5XtYpWE

ODDS = [
    (1, 1), (4, 1), (7, 1),
    (1, 4), (4, 4), (7, 4),
    (0, 8), (4, 7), (7, 7),
]

LINES = [
    [(1, 0), (0, 1), (1, 2)],
    [(5, 1), (5, 2), (6, 2), (6, 3), (7, 3)],
    [(3, 4), (3, 5), (4, 5)],
    [(6, 7), (7, 8), (8, 7)],
]

QUADS = [
    (3, 0), (4, 0), (6, 3), (7, 3), (7, 4), (1, 6), (0, 7),
]


def same_difference_lines(s, vars):
    for i, line in enumerate(LINES):
        d = z3.Int("d_%s" % i)
        for (c0, r0), (c1, r1) in zip(line, line[1:]):
            s.add(z3.Abs(vars[r0][c0] - vars[r1][c1]) == d)


def circles(s, vars):
    vs = [vars[r][c] for c, r in ODDS]

    for c, r in QUADS:
        vs.append(vars[r][c])
        vs.append(vars[r][c + 1])
        vs.append(vars[r + 1][c])
        vs.append(vars[r + 1][c + 1])

    for digit in range(1, 10):
        count = z3_count(lambda v: v == digit, vs)
        s.add(z3.Or(count == 0, count == digit))


solver = (
    Solver()
    .odds(ODDS)
    .extra_constraint(same_difference_lines)
    .extra_constraint(circles)
)

solution = solver.solve()

Solver.pretty_print(solution)
