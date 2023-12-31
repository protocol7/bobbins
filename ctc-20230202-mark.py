from solver import Solver

# https://www.youtube.com/watch?v=30Qpm8APXl0
# https://app.crackingthecryptic.com/qDFjTTFG2h

s = Solver(Solver.EMPTY).arrows(
    [
        [(1, 0), (2, 1), (3, 2)],
        [(0, 1), (1, 1), (1, 2), (0, 2)],
        [(0, 3), (1, 3), (2, 2)],
        [(0, 3), (1, 4), (1, 5)],
        [(0, 3), (0, 4), (0, 5)],
        [(5, 2), (5, 1), (5, 0)],
        [(8, 1), (7, 1), (7, 0)],
        [(8, 3), (7, 2), (6, 1)],
        [(8, 3), (7, 3), (6, 3)],
        [(3, 5), (3, 4), (3, 3)],
        [(3, 5), (4, 4), (4, 3)],
        [(3, 5), (4, 5), (5, 6)],
        [(3, 5), (2, 6), (2, 7), (2, 8)],
        [(6, 5), (7, 5), (8, 5)],
        [(7, 7), (7, 8), (6, 8)],
        [(4, 8), (4, 7), (4, 6)],
        [(8, 8), (8, 7), (8, 6)],
    ]
)

solution = s.solve()

Solver.pretty_print(solution)
