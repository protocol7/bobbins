from solver import Solver, _

# https://www.youtube.com/watch?v=yW2FrDEg0HQ


solver = (
    Solver()
    .odds([(1, 0)])
    .arrows([
        [(3, 0), (2, 1)],
        [(3, 1), (2, 2), (1, 2), (0, 2)],
        [(5, 1), (6, 0)],
        [(3, 2), (2, 3)],
        [(4, 2), (4, 3), (4, 4)],
        [(5, 2), (5, 3), (5, 4)],
        [(6, 2), (6, 3), (6, 4)],
        [(7, 2), (7, 3), (7, 4)],
        [(8, 2), (8, 3), (8, 4)],
        [(1, 4), (2, 5), (2, 6)],
        [(0, 5), (0, 6), (0, 7)],
        [(3, 5), (3, 6), (3, 7)],
        [(5, 5), (6, 6), (6, 7)],
        [(6, 5), (7, 6), (7, 7)],
        [(7, 5), (8, 6), (8, 7)],
    ])
)

solution = solver.solve()

Solver.pretty_print(solution)
