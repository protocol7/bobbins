from solver import Solver
import z3

# https://www.youtube.com/watch?v=nJmG4OT72as

FAST_THERMOS = [
    [(1, 1), (0, 0), (0, 1)],
    [(7, 1), (8, 1)],
    [(4, 4), (3, 4), (4, 3)],
    [(1, 5), (1, 4), (1, 3)],
    [(7, 5), (7, 4), (7, 3)],
    [(4, 6), (4, 7)],
    [(1, 7), (0, 7)],
    [(1, 7), (1, 8)],
    [(7, 7), (8, 6)],
]

RED_LINE = [
    (1, 1), (2, 1), (3, 0), (4, 0), (5, 0), (6, 1), (7, 1), (7, 2),
    (8, 3), (8, 4), (8, 5), (7, 6), (7, 7), (6, 7), (5, 8), (4, 8),
    (3, 8), (2, 7), (1, 7), (1, 6), (0, 5), (0, 4), (0, 3), (1, 2),
    (1, 1)
]


def z3_count(predicate, xs):
    return z3.Sum([z3.If(predicate(x), 1, 0) for x in xs])


def fast_thermos(s, vars):
    for thermo in FAST_THERMOS:
        for (c0, r0), (c1, r1) in zip(thermo, thermo[1:]):
            s.add(vars[r1][c1] - vars[r0][c0] > 1)


def red_line(s, vars):
    vs = [(vars[r0][c0], vars[r1][c1]) for (c0, r0), (c1, r1) in zip(RED_LINE, RED_LINE[1:])]

    s.add(z3.Sum([z3.If(v1 <= v0, 1, 0) for v0, v1 in vs]) == 5)


s = (
    Solver(Solver.EMPTY)
    .extra_constraint(fast_thermos)
    .extra_constraint(red_line)
)

solution = s.solve()

Solver.pretty_print(solution)
