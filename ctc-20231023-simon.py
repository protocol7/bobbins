from solver import Solver

# https://www.youtube.com/watch?v=d_4FHAJGTPg

# this solves very slowly

s = (
    Solver(Solver.EMPTY)
    .unique_negative_diagonal()
    .unique_positive_diagonal()
    .x((3, 3), (3, 4))
    .x((3, 6), (3, 7))
    .x((1, 8), (2, 8))
    .v((2, 7), (2, 8))
    .renban_lines([
        [(0, 0), (1, 0), (1, 1), (0, 1)],
        [(8, 0), (7, 0), (7, 1), (8, 1)],
        [(3, 4), (2, 4), (2, 3), (2, 2), (3, 2), (4, 2), (5, 2), (6, 2), (6, 3)],

        [(1, 3), (0, 3), (0, 4)],
        [(1, 4), (1, 5), (0, 5)],
        [(7, 3), (8, 3)],

        [(7, 4), (8, 4), (8, 5)],

        [(5, 4), (6, 4), (6, 5), (6, 6), (5, 6), (4, 6), (3, 6), (2, 6), (2, 5)],

        [(0, 7), (1, 7), (1, 8), (0, 8)],

        [(8, 7), (7, 7), (7, 8), (8, 8)],
    ])
)
solution = s.solve()

Solver.pretty_print(solution)
