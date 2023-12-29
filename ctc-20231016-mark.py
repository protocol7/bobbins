from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=iiD0cLER_j8

given = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)

DOWN = (0, 1)
UP = (0, -1)
LEFT = (-1, 0)
RIGHT = (1, 0)

ARROWS = [
    [(2, 0), LEFT],
    [(2, 1), LEFT],
    [(2, 2), DOWN],
    [(3, 0), DOWN],
    [(5, 0), DOWN],
    [(7, 0), DOWN],
    [(5, 1), DOWN],
    [(3, 2), RIGHT],
    [(7, 3), LEFT],
    [(1, 4), DOWN],
    [(7, 4), LEFT],
    [(2, 5), RIGHT],
    [(5, 5), UP],
    [(2, 6), RIGHT],
    [(3, 6), DOWN],
    [(4, 6), DOWN],
    [(6, 6), LEFT],
    [(5, 7), LEFT],
    [(0, 8), RIGHT],
]


def search8or9(s, cells):
    for (c, r), (dc, dr) in ARROWS:
        v = cells[r][c]

        or_constraints = []
        for d in range(1, 10):
            cc = c + dc * d
            rr = r + dr * d

            if cc < 0 or rr < 0 or cc >= 9 or rr >= 9:
                continue

            vv = cells[rr][cc]
            or_constraints.append(z3.And(v == d, z3.Or(vv == 8, vv == 9)))

        s.add(z3.Or(or_constraints))


s = (
    Solver(given)
    .extra_constraint(search8or9)
)
solution = s.solve()

Solver.pretty_print(solution)
