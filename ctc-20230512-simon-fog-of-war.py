from solver import Solver

# https://www.youtube.com/watch?v=-c2Ox6agRoI

ARROWS = [
    [(0, 1), (1, 1), (2, 0), (2, 1), (3, 1)],
    [(0, 2), (1, 2), (2, 2)],
    [(4, 0), (4, 1), (4, 2), (4, 3)],
    [(0, 4), (1, 3), (2, 3)],
    [(5, 6), (6, 6), (7, 5)],
]

THERMOS = [
    [(3, 0), (2, 0)],
    [(3, 3), (3, 4), (4, 4), (5, 4), (5, 5)],
    [(7, 8), (8, 8)],
]

WHITES = [
    [(5, 0), (5, 1)],
    [(6, 1), (7, 1)],
    [(0, 2), (0, 3)],
    [(8, 5), (8, 6)],
    [(2, 6), (2, 7)],
    [(7, 7), (8, 7)],
]

BLACKS = [
    [(1, 6), (2, 6)],
    [(4, 7), (5, 7)],
    [(8, 7), (8, 8)],
]

solver = (
    Solver()
    .arrows(ARROWS)
    .white_kropkis(WHITES)
    .black_kropkis(BLACKS)
    .thermos(THERMOS)
    .visible([
        (0, 0), (1, 0), (2, 0),
        (0, 1), (1, 1), (2, 1),
        (0, 2), (1, 2), (2, 2),
    ])
)

solution = solver.solve()

Solver.pretty_print(solution)
