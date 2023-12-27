from solver import Solver

# https://www.youtube.com/watch?v=8gFTYxHEAls

s = (
    Solver(Solver.EMPTY)
    .between_lines([
        [(1, 0), (2, 0), (2, 1), (2, 2)],
        [(7, 0), (6, 0), (5, 0), (4, 0), (3, 0), (3, 1)],
        [(3, 2), (2, 3), (2, 4), (3, 4), (4, 5), (5, 5), (5, 6), (4, 6), (3, 6)],
        [(6, 5), (6, 4), (6, 3), (7, 3), (7, 4), (7, 5)],
        [(2, 6), (3, 7), (4, 7), (5, 7), (6, 6), (7, 6), (8, 6), (8, 5)],
        [(1, 7), (2, 8), (3, 8), (4, 8)],
        [(7, 8), (7, 7), (8, 7), (8, 8)],
    ])
    .quadruple((0, 2), [3])
    .quadruple((0, 4), [4, 6, 8])
    .quadruple((4, 1), [8])
    .quadruple((5, 1), [2])
    .quadruple((6, 1), [1, 6])
    .quadruple((4, 3), [3, 5, 6])
)
solution = s.solve()

Solver.pretty_print(solution)
