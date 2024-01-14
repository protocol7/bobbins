from solver import Solver
import z3
from utils import z3_max

# https://www.youtube.com/watch?v=lU7hpaEgUHo

CAGES = [
    [(3, 0), (3, 1), (2, 1)],
    [(4, 0), (5, 0), (4, 1), (5, 1)],
    [(6, 0), (6, 1), (7, 1)],
    [(7, 0), (8, 0), (8, 1)],
    [(0, 1), (1, 1), (0, 2), (1, 2)],
    [(3, 2), (4, 2), (5, 2)],
    [(0, 3), (1, 3), (0, 4), (1, 4)],
    [(3, 3), (4, 3), (3, 4)],
    [(5, 3), (5, 4), (6, 4)],
    [(7, 3), (8, 3), (7, 4)],
    [(0, 5), (1, 5), (0, 6)],
    [(6, 5), (7, 5), (8, 5), (6, 6)],
    [(1, 6), (2, 6), (1, 7), (2, 7)],
    [(4, 6), (4, 7), (3, 7)],
    [(5, 6), (5, 7), (6, 7)],
    [(7, 6), (8, 6), (7, 7)],
    [(8, 7), (7, 8), (8, 8)],
    [(1, 8), (2, 8), (3, 8)],
]


def cages(s, vars):
    seen = set()

    for cage in CAGES:
        assert not set(cage) & seen, cage
        seen.update(cage)

        vs = [vars[r][c] for c, r in cage]

        s.add(z3.Distinct(vs))

        largest = z3_max(vs)

        s.add(z3.Sum(vs) == 2 * largest)


solver = (
    Solver()
    .black_kropkis([
        [(2, 1), (3, 1)],
        [(4, 1), (5, 1)],
        [(6, 2), (7, 2)],
        [(7, 2), (7, 3)],
        [(1, 4), (2, 4)],
        [(3, 5), (3, 6)],
        [(0, 6), (0, 7)],
        [(8, 6), (8, 7)],
        [(2, 7), (3, 7)],
        [(3, 7), (3, 8)],
        [(7, 7), (7, 8)],
        [(4, 8), (5, 8)],
        [(7, 8), (8, 8)],
    ])
    .thermo([(3, 8), (4, 8), (5, 8), (4, 7), (3, 6)])
    .x((0, 5), (1, 5))
    .extra_constraint(cages)
)

solution = solver.solve()

Solver.pretty_print(solution)
