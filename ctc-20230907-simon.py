from solver import Solver
import z3
from utils import z3_count

# https://www.youtube.com/watch?v=4jIB89I7mM4

solver = (
    Solver()
    .nabner_lines([
        [(2, 0), (1, 0), (0, 0), (0, 1), (0, 2)],
        [(3, 0), (3, 1), (3, 2), (4, 3)],
        [(4, 2), (3, 3)],
        [(4, 0), (4, 1), (5, 1), (5, 2)],
        [(5, 0), (6, 1), (7, 1), (7, 2)],
        [(1, 1), (1, 2), (2, 3), (2, 4)],
        [(2, 1), (2, 2), (1, 3), (1, 4)],
        [(0, 3), (0, 4), (1, 5), (2, 5)],
        [(5, 3), (6, 3), (7, 3), (8, 3)],
        [(5, 4), (4, 4), (3, 4), (3, 5)],
        [(6, 4), (7, 4)],
        [(0, 5), (1, 6), (1, 7)],
        [(5, 5), (6, 5), (7, 5), (8, 5)],
        [(0, 6), (0, 7), (0, 8)],
        [(2, 6), (3, 6), (4, 5), (5, 6)],
        [(4, 6), (3, 7), (3, 8)],
        [(8, 6), (7, 6), (6, 6), (7, 7)],
        [(2, 7), (2, 8), (1, 8)],
        [(4, 7), (5, 7), (6, 8)],
        [(6, 7), (5, 8)],
    ])
    .smaller_than((8, 0), (7, 0))
)


solution = solver.solve()

Solver.pretty_print(solution)
