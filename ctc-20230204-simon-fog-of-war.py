from solver import Solver

# https://www.youtube.com/watch?v=vcQuufZ1rOE

solver = (
    Solver()
    .anti_x_v()
    .v((0, 1), (1, 1))
    .xs([
        [(0, 0), (0, 1)],
        [(7, 6), (7, 7)],
    ])
    .whisper_lines([
        [(0, 2), (0, 1), (0, 0), (1, 1), (1, 0), (2, 0), (3, 1)],
        [(6, 0), (7, 0), (6, 1), (5, 1), (4, 1)],
        [(7, 1), (7, 2), (7, 3), (7, 4), (7, 5)],
        [(2, 2), (3, 2)],
        [(2, 7), (3, 6)],
        [(4, 7), (5, 8), (6, 7), (6, 6), (7, 6)],
        [(6, 7), (5, 6), (4, 6)],
        [(4, 8), (5, 7)],
    ])
    .visible([(0, 0), (1, 0), (0, 1), (1, 1)])
)

solution = solver.solve()

Solver.pretty_print(solution)
