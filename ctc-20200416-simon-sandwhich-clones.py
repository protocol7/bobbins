from solver import Solver, _
import z3
from itertools import combinations

# https://www.youtube.com/watch?v=F5x7ouoqQJk

givens = (
    (_, _, _, _, _, _, _, 9, _),
    (5, _, _, _, 8, _, 4, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, 4, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, 1, _, _, 6, _, _),
)

SANDWHICH_ROWS = [
    (3, 28),
    (5, 0),
    (6, 0),
    (8, 10),
]

SANDWHICH_COLS = [
    (0, 16),
    (3, 27),
    (4, 7),
]

s = (
    Solver(givens)
    .clones([
        [(1, 2), (6, 7)],
        [(1, 3), (6, 6)],
        [(2, 3), (5, 6)],
        [(3, 3), (4, 6)],
        [(3, 2), (4, 7)],
        [(4, 3), (3, 6)],
        [(5, 3), (2, 6)],
        [(5, 2), (2, 7)],
        [(6, 2), (1, 7)],
        [(7, 2), (0, 7)],
        [(7, 3), (0, 6)],
        [(7, 4), (0, 5)],
        [(6, 4), (1, 5)],
        [(5, 4), (2, 5)],
    ])
    .sandwhiches(SANDWHICH_ROWS, SANDWHICH_COLS)
)
solution = s.solve()

Solver.pretty_print(solution)
