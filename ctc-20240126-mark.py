from solver import Solver, _
import z3
from utils import orthogonal

# https://www.youtube.com/watch?v=vR9n7CGYNxU

GIVEN = (
    (7, _, _, _, _, _, _, _, _),
    (_, _, 9, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, 6, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)

BLACKS = [
    (1, 5), (2, 5), (3, 6), (4, 6), (7, 6), (4, 7), (7, 7), (4, 8),
]

WHITES = [
    (5, 2), (5, 3), (4, 4), (5, 4), (2, 6), (3, 7), (7, 8),
]

GRAYS = [
    (3, 8),
]

ALL = BLACKS + WHITES + GRAYS


def circles(s, vars, visible):
    # negative
    for r in range(9):
        for c in range(9):
            if (c, r) not in visible:
                continue

            if (c, r) in ALL:
                continue

            v = vars[r][c]

            for nc, nr in orthogonal(vars, c, r):
                nv = vars[nr][nc]

                s.add(z3.Abs(v - nv) != 1)
                s.add(v * 2 != nv, nv * 2 != v)
                s.add(nv + v != 5)

    # turns out, ths solves with only the negative constraints


solver = (
    Solver(GIVEN)
    .visible([
        (0, 0), (1, 0), (0, 1), (1, 1), (2, 1), (1, 2),
        (4, 3),
        (6, 3), (7, 3), (6, 4), (7, 4), (8, 4), (7, 5),
        (3, 6), (3, 7), (3, 8),
    ])
    .extra_constraint(circles, with_visible=True)
)


solution = solver.solve()

Solver.pretty_print(solution)
