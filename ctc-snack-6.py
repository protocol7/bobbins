from solver import Solver

# http://tinyurl.com/CTC-Snack-6

s = (
    Solver.regular_4x4()
    .thermo([(0, 2), (0, 1), (1, 0)])
    .arrow([(3, 2), (3, 1), (2, 0)])
    .quadruple((1, 2), [1, 2])
)
solution = s.solve()

Solver.pretty_print(solution)
