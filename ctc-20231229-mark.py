from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=rqFz9WRbNi0

given = (
    (8, _, _, _, 4, _, _, _, 2),
    (4, 2, _, _, 9, _, _, 1, _),
    (_, _, 7, _, 3, _, _, 8, _),
    (_, _, _, _, _, _, _, _, _),
    (2, 1, _, _, 8, _, _, 4, 3),
    (_, _, _, _, _, _, _, _, _),
    (_, 4, _, _, _, _, 3, _, _),
    (_, 6, _, _, 5, _, _, 9, _),
    (5, _, 2, _, 6, _, _, _, 4),
)


def anti_windoku(s, vars):
    # hard coding the outsiders and insiders here is a boring solution,
    # but SetHasSize is no longer supported so not sure how to otherwise
    # constrain the window to have a certain number of distinct digits
    for co, ro in [(3, 1), (3, 2), (3, 3), (2, 3), (1, 3)]:
        s.add(z3.Or([vars[ro][co] == vars[r][c] for c, r in [(1, 1), (1, 2), (2, 1), (2, 2)]]))

    for co, ro in [(5, 1), (5, 2), (5, 3), (6, 3), (7, 3)]:
        s.add(z3.Or([vars[ro][co] == vars[r][c] for c, r in [(6, 1), (7, 1), (6, 2), (7, 2)]]))

    for co, ro in [(1, 5), (2, 5), (3, 5), (3, 6), (3, 7)]:
        s.add(z3.Or([vars[ro][co] == vars[r][c] for c, r in [(1, 6), (2, 6), (1, 7), (2, 7)]]))

    for co, ro in [(7, 5), (6, 5), (5, 5), (5, 6), (5, 7)]:
        s.add(z3.Or([vars[ro][co] == vars[r][c] for c, r in [(6, 6), (7, 6), (6, 7), (7, 7)]]))


s = (
    Solver(given)
    .extra_constraint(anti_windoku)
)
solution = s.solve()

Solver.pretty_print(solution)
