from solver import Solver, _

# https://www.youtube.com/watch?v=r-SRALo9e8Q


solver = (
    Solver()
    .white_kropkis([
        [(4, 1), (4, 2)],
        [(1, 4), (2, 4)],
        [(6, 4), (7, 4)],
        [(4, 6), (4, 7)],
    ])
    .quadruple((2, 0), [3, 8])
    .quadruple((5, 0), [1, 2, 3])
    .quadruple((1, 1), [8])
    .quadruple((6, 1), [7])
    .quadruple((0, 2), [4, 5, 6])
    .quadruple((7, 2), [4, 7, 9])
    .quadruple((0, 5), [6, 7, 9])
    .quadruple((7, 5), [1, 4])
    .quadruple((1, 6), [2])
    .quadruple((6, 6), [6])
    .quadruple((2, 7), [1, 3, 8])
    .quadruple((5, 7), [1, 2, 5])
)

solution = solver.solve()

Solver.pretty_print(solution)
