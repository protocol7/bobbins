from solver import Solver

# https://www.youtube.com/watch?v=AcXPvXIY5eg

s = (
    Solver(Solver.EMPTY)
    .evens([(4, 5)])
    .white_kropkis([
        ((2, 2), (2, 3))
    ])
    .region_sum_lines([
        [(0, 1), (0, 2), (0, 3), (1, 3), (2, 3), (2, 4), (2, 5), (2, 6), (1, 6)],
        [(2, 1), (2, 2), (3, 3), (3, 4)],
        [(2, 0), (3, 0), (4, 1), (5, 2)],
        [(4, 0), (5, 0), (6, 0)],
        [(6, 1), (6, 2), (5, 3), (5, 4)],
        [(8, 1), (8, 2), (8, 3), (7, 3), (6, 3), (6, 4), (6, 5)],
        [(1, 8), (2, 8), (3, 7), (4, 7), (5, 7), (6, 6), (7, 6)],
    ])
)
solution = s.solve()

Solver.pretty_print(solution)
