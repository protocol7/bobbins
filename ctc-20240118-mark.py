from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=sDr14uZUE7Y


ROWS = [
    [(0, 0), [5]],
    [(0, 4), [4, 5]],
    [(0, 8), [9]],
    [(8, 4), [2, 6]],
    [(8, 6), [4]],
    [(8, 8), [2]],
]

COLS = [
    [(1, 0), [3, 4]],
    [(4, 0), [9]],
    [(6, 0), [7]],
    [(7, 0), [1, 2]],
    [(3, 8), [2]],
    [(5, 8), [9]],
]


def outside(s, vars):
    for (c, r), ns in ROWS:
        for n in ns:
            if c == 0:
                cs = [0, 1, 2]
            else:
                cs = [6, 7, 8]

            or_terms = []
            for cc in cs:
                or_terms.append(vars[r][cc] == n)
            s.add(z3.Or(or_terms))

    for (c, r), ns in COLS:
        for n in ns:
            if r == 0:
                rs = [0, 1, 2]
            else:
                rs = [6, 7, 8]

            or_terms = []
            for rr in rs:
                or_terms.append(vars[rr][c] == n)
            s.add(z3.Or(or_terms))


solver = (
    Solver()
    .killer_cage([(2, 0), (3, 0), (4, 0), (0, 1), (1, 1), (2, 1), (0, 2)], 29)
    .killer_cage([(8, 0), (6, 1), (7, 1), (8, 1), (4, 2), (5, 2), (6, 2)], 32)
    .killer_cage([(0, 3), (1, 3), (2, 3), (2, 4), (3, 4), (1, 5), (2, 5)], 31)
    .killer_cage([(6, 3), (7, 3), (5, 4), (6, 4), (6, 5), (7, 5), (8, 5)], 35)
    .killer_cage([(1, 6), (2, 6), (3, 6)], 15)
    .killer_cage([(5, 6), (6, 6), (7, 6)], 15)
    .killer_cage([(3, 7), (5, 7), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8)], 38)
    .extra_constraint(outside)
)

solution = solver.solve()

Solver.pretty_print(solution)
