from solver import Solver
import z3

# https://www.youtube.com/watch?v=2gsHqiAPj8g

PALINDROM = [(7, 2), (8, 3)]
ZIPPER_LINES = [
    [(0, 0), (1, 1), (2, 2)],
    [(5, 2), (4, 2), (3, 2), (2, 3), (2, 4), (2, 5)],
    [(4, 6), (5, 6), (6, 5), (6, 4)],
]
LINES = PALINDROM + [x for xx in ZIPPER_LINES for x in xx]


def z3_count(predicate, xs):
    return z3.Sum([z3.If(predicate(x), 1, 0) for x in xs])


def circles(s, vars):
    vlines = [vars[r][c] for c, r in LINES]
    for d in range(1, 10):
        # count in lines must be either the same as the digit, or 0
        s.add(z3.Or([z3_count(lambda v: v == d, vlines) == sum for sum in [0, d]]))


s = (
    Solver(Solver.EMPTY)
    .killer_cage([(2, 0), (3, 0), (4, 0), (5, 0)], 23)
    .killer_cage([(0, 1), (0, 2), (1, 2)], 23)
    .killer_cage([(0, 3), (1, 3), (2, 3), (3, 3)], 23)
    .killer_cage([(4, 3), (5, 3), (5, 2), (6, 3), (7, 3)], 23)
    .killer_cage([(4, 4), (5, 4), (4, 5), (5, 5)], 23)
    .killer_cage([(6, 4), (6, 5), (7, 4), (8, 4)], 23)
    .killer_cage([(0, 5), (0, 6), (0, 7), (0, 8)], 23)
    .killer_cage([(2, 5), (1, 5), (1, 6), (1, 7), (1, 8), (2, 8)], 23)
    .killer_cage([(7, 5), (7, 6), (8, 6), (8, 7)], 23)
    .killer_cage([(2, 6), (3, 6), (4, 6), (5, 6)], 23)
    .killer_cage([(2, 7), (3, 7), (3, 8), (4, 7)], 23)
    .killer_cage([(6, 7), (6, 8), (5, 8)], 23)
    .palindrom_lines([PALINDROM])
    .zipper_lines(ZIPPER_LINES)
    .extra_constraint(circles)
)
solution = s.solve()

Solver.pretty_print(solution)
