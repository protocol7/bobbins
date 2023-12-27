from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=hAyZ9K2EBF0

givens = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (3, 8, 4, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, 2),
)

MAGIC_SQUARES = [(4, 4)]


def magic_squares(s, cells):
    for cc, cr in MAGIC_SQUARES:
        v0, v1, v2 = cells[cr - 1][cc - 1], cells[cr - 1][cc], cells[cr - 1][cc + 1]
        v3, v4, v5 = cells[cr][cc - 1], cells[cr][cc], cells[cr][cc + 1]
        v6, v7, v8 = cells[cr + 1][cc - 1], cells[cr + 1][cc], cells[cr + 1][cc + 1]

        # rows
        s.add(v0 + v1 + v2 == 15)
        s.add(v3 + v4 + v5 == 15)
        s.add(v6 + v7 + v8 == 15)

        # cols
        s.add(v0 + v3 + v6 == 15)
        s.add(v1 + v4 + v7 == 15)
        s.add(v2 + v5 + v8 == 15)

        # diagonals
        s.add(v0 + v4 + v8 == 15)
        s.add(v2 + v4 + v6 == 15)

s = (
    Solver(givens)
    .unique_negative_diagonal()
    .unique_positive_diagonal()
    .anti_knight()
    .extra_constraint(magic_squares)
)
solution = s.solve()

Solver.pretty_print(solution)
