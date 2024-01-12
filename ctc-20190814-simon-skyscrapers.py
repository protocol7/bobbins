from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=rLlZA5ZND00


def z3_max(vs):
    m = vs[0]
    for v in vs[1:]:
        m = z3.If(v > m, v, m)
    return m


given = (
    (1, _, _, _, _, 2, _, _, 8),
    (_, _, _, _, _, _, _, _, _),
    (3, _, _, 6, _, _, 4, _, _),
    (_, _, _, _, _, _, _, _, _),
    (5, _, 2, _, _, 3, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (7, _, _, 8, _, _, 2, _, _),
    (_, _, _, _, _, _, _, _, _),
    (9, _, _, _, _, 4, _, _, 6),
)

COLS = [
    (4, 5)
]
ROWS = [
    (1, 2),
    (3, 4),
    (5, 6),
    (7, 8)
    ]


def skyscrapers(s, vars):
    def _skyscraper(xs, count):
        sum_terms = []
        for i in range(9):
            v = xs[i]
            vs = xs[:i + 1]

            sum_terms.append(z3.If(z3_max(vs) == v, 1, 0))

        s.add(z3.Sum(sum_terms) == count)

    for r, count in ROWS:
        _skyscraper(vars[r], count)

    cols = list(map(list, zip(*vars)))
    for c, count in COLS:
        _skyscraper(cols[c], count)



solver = (
    Solver(given)
    .extra_constraint(skyscrapers)
)

solution = solver.solve()

Solver.pretty_print(solution)
