from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=L-cbtgqTE9M

MAKE_IT_UNIQUE_CELLS = [
    [(0, 5), (1, 5)],
    [(8, 5), (8, 6)],
]

s = Solver()


def make_it_unique(z3_s, cells):
    for (mc0, mr0), (mc1, mr1) in MAKE_IT_UNIQUE_CELLS:
        mv0 = cells[mr0][mc0]
        mv1 = cells[mr1][mc1]

        for (c0, r0), v0, (c1, r1), v1 in s.all_dominos(cells):

            if c0 == mc0 and r0 == mr0 and c1 == mc1 and r1 == mr1:
                continue
            else:
                z3_s.add(z3.Or(mv0 != v0, mv1 != v1))


s = (
    s.digits(list(range(0, 8 + 1)))
    .white_kropkis(
        (
            ((3, 1), (4, 1)),
            ((4, 1), (5, 1)),
        )
    )
    .black_kropkis(
        (
            ((4, 3), (4, 4)),
            ((4, 4), (4, 5)),
            ((4, 5), (4, 6)),
        )
    )
    .thermo([(4, 2), (5, 2)])
    .arrows(
        (
            [(2, 4), (3, 3), (2, 2), (2, 1), (3, 0), (4, 0), (5, 0), (6, 1), (6, 2), (5, 3), (6, 4)],
            [(6, 6), (5, 7), (4, 7), (3, 7), (2, 6)],
        )
    )
    .whisper_lines([
        [(2, 5), (1, 4), (0, 3)],
        [(1, 4), (0, 4)],

        [(6, 5), (7, 4), (8, 3)],
        [(7, 4), (7, 3)],
    ])
    .extra_constraint(make_it_unique)
)
solution = s.solve()

Solver.pretty_print(solution)
