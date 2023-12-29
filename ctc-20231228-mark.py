from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=L8Kum87ibpI

given = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, 1, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, 7, _, _),
    (_, 3, _, _, _, _, _, _, _),
)

LINES = [
    [
        (7, 4), (6, 5), (5, 5), (4, 5), (3, 5), (2, 5), (1, 4), (1, 3), (1, 2),
        (1, 1), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 1), (7, 2), (7, 3),
        (7, 4), (7, 5), (7, 6), (7, 7), (6, 8), (5, 8), (4, 8), (3, 8), (2, 8),
        (1, 7)
    ],
    [(2, 4), (2, 3), (2, 2), (3, 3), (4, 2), (4, 3), (4, 4)]
]


def sums(s, vars):
    for line in LINES:
        for (c0, r0), (c1, r1) in zip(line, line[1:]):
            v0 = vars[r0][c0]
            v1 = vars[r1][c1]

            s.add(z3.Or([v0 + v1 == sum for sum in [7, 8, 9]]))


s = (
    Solver(given)
    .extra_constraint(sums)
)
solution = s.solve()

Solver.pretty_print(solution)
