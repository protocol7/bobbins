from solver import Solver

# https://www.youtube.com/watch?v=_-fTTLSHcvI

s = (
    Solver(Solver.EMPTY)
    .unique_positive_diagonal()
    .unique_negative_diagonal()
    .thermo([(4, 4), (4, 3), (3, 2), (2, 1), (2, 0)])
    .thermo([(4, 0), (5, 1), (6, 1), (7, 1)])
    .thermo([(0, 8), (1, 8), (2, 7), (3, 6), (2, 5)])
    .thermo([(8, 8), (7, 8), (6, 8), (5, 7), (5, 6)])
)
solution = s.solve()

Solver.pretty_print(solution)
