from solver import Solver

# https://www.youtube.com/watch?v=HMdV3F5wK48

s = (
    Solver(Solver.EMPTY)
    .whisper_lines([
        [(0, 2), (1, 2), (2, 2)],
        [(4, 0), (5, 0), (5, 1), (4, 1)],
        [(6, 1), (7, 1), (8, 1), (7, 2)],
        [(1, 4), (1, 5), (2, 5), (2, 4)],
        [(3, 4), (3, 3), (4, 3), (4, 4)],
        [(5, 6), (5, 7)],
        [(7, 8), (8, 8)],
    ])
    .anti_x_v()
)
solution = s.solve()

Solver.pretty_print(solution)
