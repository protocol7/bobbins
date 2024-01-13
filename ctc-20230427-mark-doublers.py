from solver import Solver

# https://www.youtube.com/watch?v=XPiF-OljHkY


solver = (
    Solver()
    .multipliers(2)
    .whisper_lines([
        [
            (1, 7), (0, 7), (0, 6), (0, 5), (0, 4), (0, 3), (0, 2), (0, 1), (0, 0),
            (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (8, 1),
            (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)
        ],
        [(2, 1), (2, 2), (2, 3), (2, 4), (2, 5)],
        [(4, 5), (5, 5), (5, 4)],
        [(2, 6), (3, 6), (4, 6), (5, 6), (6, 6), (6, 5)],
        [(5, 8), (6, 8), (6, 7)],
    ])
)

solution = solver.solve()

Solver.pretty_print(solution)
