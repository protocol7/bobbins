from solver import Solver
import z3

# https://www.youtube.com/watch?v=9RXpL65r2cU

BLUE_DOTS = [
    [(6, 0), (7, 0)],
    [(2, 4), (3, 4)],
]


def doubler_blue_dots(s, vars, multipliers):
    for (c0, r0), (c1, r1) in BLUE_DOTS:
        v0 = vars[r0][c0]
        v1 = vars[r1][c1]
        m0 = multipliers[r0][c0]
        m1 = multipliers[r1][c1]

        s.add(z3.Or(v0 * m0 * 2 == v1 * m1 * 3, v1 * m1 * 2 == v0 * m0 * 3))


solver = (
    Solver()
    .multipliers(2)
    .zipper_lines([
        [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0)],
        [(2, 1), (3, 1), (2, 2)],
        [(1, 2), (2, 3), (3, 4)],
        [(4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)],
        [(7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)],
        [(0, 8), (1, 8), (1, 7), (1, 6), (2, 6)],
        [(2, 8), (3, 8), (4, 8), (5, 7), (5, 8)],
        [(6, 8), (7, 8), (8, 8)],
    ])
    .black_kropkis([
        [(2, 5), (3, 5)],
        [(2, 5), (2, 6)],
        [(0, 6), (0, 7)],
    ])
    .extra_constraint(doubler_blue_dots, with_multipliers=True)
)

solution = solver.solve()

Solver.pretty_print(solution)
