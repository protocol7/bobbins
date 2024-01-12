from solver import Solver
import z3
from utils import z3_count

# https://www.youtube.com/watch?v=qj1Bo_8F66M

CAGES = [
    [(0, 0), (1, 0), (1, 1)],
    [(2, 2), (2, 1), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0)],
    [(0, 1), (0, 2), (1, 2)],
    [(3, 2), (3, 1), (4, 1)],
    [(6, 1), (7, 1), (7, 2)],
    [(8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (7, 6), (6, 6)],
    [(2, 3), (3, 3), (3, 4), (4, 3), (5, 3), (5, 4), (5, 5), (4, 5), (5, 6)],
    [(7, 3), (7, 4)],
    [(0, 4), (1, 4)],
    [(2, 5), (3, 5)],
    [(6, 5), (7, 5)],
    [(1, 6), (0, 7), (1, 7), (2, 7), (1, 8)],
    [(3, 7), (3, 8)],

    [(6, 7), (6, 8), (7, 8)],
    [(7, 7), (8, 7), (8, 8)],
]


def cages(s, vars):
    for i, cage in enumerate(CAGES):
        vs = [vars[r][c] for c, r in cage]

        k = z3.Int("cage_%s" % i)

        s.add(z3.Distinct(vs))

        s.add(z3.Sum(vs) == k)

        evens = z3_count(lambda v: v % 2 == 0, vs)
        odds = len(cage) - evens

        s.add(z3.Or(
            z3.And(evens == k / 10, odds == k % 10),
            z3.And(evens == k % 10, odds == k / 10),
            ))


solver = (
    Solver()
    .evens([
        (3, 0), (7, 0), (8, 1), (2, 4), (4, 4), (3, 5), (8, 5),
        (2, 6), (4, 6), (0, 8)
    ])
    .odds([(7, 1)])
    .extra_constraint(cages)
)

solution = solver.solve()

Solver.pretty_print(solution)
