from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=_BAt9Bwhb-c


GIVEN = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, 5, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)

AREAS = [
    ([(4, 0), (5, 1), (4, 2), (3, 3), (2, 4), (1, 3), (2, 2), (3, 1)], [(4, 1), (3, 2), (2, 3)]),
    ([(6, 0), (7, 1), (6, 2), (5, 1)], [(6, 1)]),
    ([(5, 1), (6, 2), (5, 3), (4, 2)], [(5, 2)]),
    ([(7, 1), (8, 2), (7, 3), (6, 4), (5, 3), (6, 2)], [(7, 2), (6, 3)]),
    ([(4, 2), (5, 3), (6, 4), (5, 5), (4, 6), (3, 5), (4, 4), (3, 3)], [(4, 3), (5, 4), (4, 5)]),
    ([(3, 3), (4, 4), (3, 5), (2, 4)], [(3, 4)]),
    ([(7, 3), (8, 4), (7, 5), (6, 6), (5, 5), (6, 4)], [(7, 4), (6, 5)]),

    ([(2, 4), (3, 5), (2, 6), (1, 5)], [(2, 5)]),
    ([(3, 5), (4, 6), (3, 7), (2, 6)], [(3, 6)]),
    ([(5, 5), (6, 6), (5, 7), (4, 6)], [(5, 6)]),
]


def area_lines(s, vars):
    for line, area in AREAS:
        ls = [vars[r][c] for c, r in line]
        aa = [vars[r][c] for c, r in area]

        s.add(z3.Sum(ls) == z3.Sum(aa))


solver = (
    Solver(GIVEN)
    .white_kropkis([[(1, 8), (2, 8)]])
    .extra_constraint(area_lines)
)

solution = solver.solve()

Solver.pretty_print(solution)