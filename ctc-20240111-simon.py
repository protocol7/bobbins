from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=pXXggaJbbSQ

given = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, 6, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)


ARROWS = [
    [(8, 1), (8, 2), (8, 3), (8, 4)],
    [(2, 5), (3, 6), (4, 6)],
]

THERMOS = [
    [(5, 1), (6, 1), (6, 2)],
    [(3, 3), (3, 4)],
    [(5, 8), (4, 8), (3, 8)],
]

WHISPERS = [
    [(4, 0), (3, 0), (2, 0), (2, 1)],
    [(1, 2), (0, 2), (0, 3), (0, 4)],

]

RENBANS = [
    [(3, 2), (4, 2), (5, 2)],
    [(1, 3), (1, 4), (1, 5)],
    [(7, 5), (8, 5)],
]

DOTS = [
    [(4, 3), (4, 4)],
    [(8, 6), (8, 7)],
]


def unique(s, vars):
    for lists in [ARROWS, THERMOS, WHISPERS, RENBANS, DOTS]:
        lists = [x for xs in lists for x in xs]
        vs = [vars[r][c] for c, r in lists]

        s.add(z3.Distinct(vs))


solver = (
    Solver(given)
    .whisper_lines(WHISPERS)
    .renban_lines(RENBANS)
    .arrows(ARROWS)
    .black_kropkis(DOTS)
    .extra_constraint(unique)
)

for thermo in THERMOS:
    solver.thermo(thermo)

solution = solver.solve()

Solver.pretty_print(solution)
