from solver import Solver, _
from utils import ORTHOGONAL
import z3

# https://www.youtube.com/watch?v=xSIR0_bey_U

GIVEN = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, 5, _, _, _, _),
    (_, 7, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, 8, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)

CIRCLES = [
    (4, 0), (5, 0), (8, 0),
    (0, 1), (3, 1), (5, 1),
    (3, 2), (4, 2),
    (4, 3),
    (7, 6),
    (2, 7),
    (3, 8), (4, 8),
]


def beachcomb(s, vars):
    def ifs(v, ns):
        if len(ns) == 0:
            return 0
        else:
            ands = [n < v for n in ns]
            return z3.If(z3.And(ands), len(ns), ifs(v, ns[:-1]))

    for c, r in CIRCLES:
        v = vars[r][c]

        count_terms = []
        for dc, dr in ORTHOGONAL:
            ns = []
            for i in range(1, 9):
                nc = c + dc * i
                nr = r + dr * i

                if nc < 0 or nc >= 9 or nr < 0 or nr >= 9:
                    break

                ns.append(vars[nr][nc])

            count_terms.append(ifs(v, ns))

        s.add(z3.Sum(count_terms) == v)




solver = (
    Solver(GIVEN)
    .xs([
        [(2, 2), (2, 3)]
    ])
    .extra_constraint(beachcomb)
)

solution = solver.solve()

Solver.pretty_print(solution)
