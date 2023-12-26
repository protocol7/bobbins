from solver import Solver

# https://www.youtube.com/watch?v=ONcbJwNdw9A

s = (
    Solver(Solver.EMPTY)
    .thermo([(5, 0), (4, 0), (3, 0), (2, 1), (1, 1)])
    .thermo([(7, 0), (8, 1)])
    .thermo([(8, 2), (7, 2), (6, 2), (5, 3), (4, 3)])

    .thermo([(2, 2), (2, 3), (3, 2), (4, 2)])
    .thermo([(0, 3), (1, 3), (2, 3), (3, 2), (4, 2)])
    .thermo([(2, 4), (3, 4)])
    .thermo([(3, 5), (2, 6), (1, 6), (0, 7)])
    .thermo([(3, 6), (2, 7), (1, 7)])
    .thermo([(5, 6), (6, 5)])
    .thermo([(8, 5), (8, 6), (8, 7)])
    .renban_lines([
        [(0, 2), (1, 2), (2, 2), (3, 1), (4, 1), (5, 1)],
        [(0, 4), (1, 4), (2, 4), (3, 3)],
        [(7, 5), (8, 5)],
    ])
)
solution = s.solve()

Solver.pretty_print(solution)
