from solver import Solver
import z3

# https://www.youtube.com/watch?v=3BpWRA6dtug

CAGES = [
    ([(2, 1), (3, 1), (2, 2)], (1, 0)),
    ([(6, 1), (6, 2)], (5, 0)),
    ([(3, 3)], (2, 2)),
    ([(5, 3), (5, 4)], (4, 2)),
    ([(7, 4), (7, 5)], (6, 3)),
    ([(2, 5), (2, 6), (3, 6)], (1, 4)),
    ([(6, 8), (7, 8), (8, 8)], (5, 7)),
]

ARROWS = [
    [(4, 3), (-1, 1)],
    [(7, 3), (-1, -1)],
    [(7, 3), (1, -1)],
    [(8, 6), (-1, -1)],
    [(3, 8), (-1, -1)],
]


def cages(s, vars):
    for cage, (sc, sr) in CAGES:
        sum = vars[sr][sc]

        vs = [vars[r][c] for c, r in cage]

        s.add(z3.Sum(vs) == sum)
        s.add(z3.Distinct(vs))


def arrows(s, vars):
    for (c, r), (dc, dr) in ARROWS:
        sum = vars[r][c]

        vs = []
        nc = c + dc
        nr = r + dr
        while nc >= 0 and nc < 9 and nr >= 0 and nr < 9:
            vs.append(vars[nr][nc])

            nc += dc
            nr += dr

        s.add(z3.Sum(vs) == sum)


solver = (
    Solver()
    .extra_constraint(cages)
    .extra_constraint(arrows)
)


solution = solver.solve()

Solver.pretty_print(solution)
