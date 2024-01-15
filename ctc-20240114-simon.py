from solver import Solver, _
import z3
from utils import z3_max

# https://www.youtube.com/watch?v=_Mfhj7-qAVI

given = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, 1),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)

COLS = [
    (3, 3),
    (5, 3),
]
ROWS = [
    (2, 3),
    ]


def cloudy_skyscrapers(s, vars):
    def _skyscraper(xs, count):
        sum_terms = []
        for i in range(9):
            v = xs[i]
            vs = xs[:i + 1]

            sum_terms.append(z3.If(z3.And(v >= 6, z3_max(vs) == v), 1, 0))

        s.add(z3.Sum(sum_terms) == count)

    for r, count in ROWS:
        _skyscraper(vars[r], count)

    cols = list(map(list, zip(*vars)))
    for c, count in COLS:
        _skyscraper(cols[c], count)


solver = (
    Solver(given)
    .whisper_lines([
        [(7, 0), (8, 1)],
        [(0, 1), (1, 1)],
        [(2, 3), (1, 2), (2, 2), (3, 2), (4, 2), (5, 2), (6, 2), (7, 3), (7, 2)],
        [(4, 2), (4, 3), (4, 4)],
        [(6, 4), (6, 5)],

        [(3, 5), (3, 6), (3, 7), (4, 8), (4, 7), (5, 7), (5, 6), (5, 5)],
        [(2, 6), (3, 6)],
        [(5, 6), (6, 6)],
        [(8, 6), (7, 6), (7, 7)],
        [(1, 8), (1, 7), (2, 8)],
    ])
    .extra_constraint(cloudy_skyscrapers)
)

solution = solver.solve()

Solver.pretty_print(solution)
