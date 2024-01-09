from solver import Solver

# https://www.youtube.com/watch?v=pUmxnOB942I

s = (
    Solver()
    .sandwhiches([(8, 33)], [(0, 33), (8, 32)])
    .smaller_than((6, 4), (7, 4))
    .smaller_than((1, 5), (2, 5))
    .renban_lines([
        [(1, 1), (1, 2), (1, 3)],
        [(2, 1), (2, 2), (2, 3)],
        [(3, 1), (3, 2), (3, 3)],

        [(5, 1), (6, 1), (7, 1)],
        [(5, 2), (6, 2), (7, 2)],
        [(5, 3), (6, 3), (7, 3)],

        [(5, 5), (5, 6), (5, 7)],
        [(6, 5), (6, 6), (6, 7)],
        [(7, 5), (7, 6), (7, 7)],

        [(1, 5), (2, 5), (3, 5)],
        [(1, 6), (2, 6), (3, 6)],
        [(1, 7), (2, 7), (3, 7)],
    ])
)

solution = s.solve()

Solver.pretty_print(solution)
