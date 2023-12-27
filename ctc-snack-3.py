from solver import Solver

# http://tinyurl.com/CTC-Snack-3

s = (
    Solver.regular_4x4()
    .little_killer([(1, 0), (2, 1), (3, 2)], 3)
    .little_killer([(2, 0), (1, 1), (0, 2)], 6)
    .little_killer([(0, 1), (1, 2), (2, 3)], 9)
)
solution = s.solve()

Solver.pretty_print(solution)
