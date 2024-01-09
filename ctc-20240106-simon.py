from solver import Solver, _

# https://www.youtube.com/watch?v=y18YGirVpIQ

LINES = [
    [(6, 0), (6, 1), (5, 1), (5, 2)],
    [(0, 1), (0, 2), (1, 3), (0, 3), (0, 4)],
    [(1, 1), (2, 2), (3, 2), (2, 3), (1, 4)],
    [(8, 1), (8, 2), (7, 3), (8, 4), (7, 5)],
    [(6, 4), (6, 5), (6, 6), (6, 7), (5, 6), (4, 6), (3, 6)],
    [(1, 8), (2, 7), (3, 7), (4, 8), (5, 7)],
]

solver = (
    Solver()
    .region_sum_lines(LINES)
    .zipper_lines(LINES)
)

solution = solver.solve()

Solver.pretty_print(solution)
