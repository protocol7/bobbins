from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=1wGrV70pfo0

GIVEN = (
    (6, _, _, _, _, _, _, 5, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, 7, _, _, _, _),
    (_, _, 8, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, 9, _),
)


ARROWS = [
    [(1, 1), (2, 2), (3, 3)],
    [(4, 1), (4, 2), (4, 3)],
    [(7, 1), (6, 2), (5, 3)],
    [(1, 4), (2, 4), (3, 4)],
    [(7, 4), (6, 4), (5, 4)],
    [(1, 7), (2, 6), (3, 5)],
    [(7, 7), (6, 6), (5, 5)],
]


def unique_arrows(s, vars):
    hs = [vars[arrow[0][1]][arrow[0][0]] for arrow in ARROWS]

    s.add(z3.Distinct(hs))


solver = (
    Solver(GIVEN)
    .arrows(ARROWS)
    .extra_constraint(unique_arrows)
)

solution = solver.solve()

Solver.pretty_print(solution)
