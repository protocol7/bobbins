from solver import Solver, _


# https://www.youtube.com/watch?v=-egiLh6s-nw

solver = (
    Solver(Solver.EMPTY)
    .thermos([
        [(2, 3), (1, 3), (1, 2), (2, 2), (3, 1), (3, 2)],
        [(7, 3), (8, 3), (7, 2), (6, 1), (5, 2), (5, 1)],
        [(0, 5), (1, 5), (1, 6), (2, 7), (3, 7), (3, 6)],
        [(6, 5), (7, 5), (7, 6), (6, 7), (5, 7), (5, 8)],
    ])
)

solution = solver.solve()

Solver.pretty_print(solution)
