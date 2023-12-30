from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=hUZhMCuVlek&

s = (
    Solver(Solver.EMPTY)
    .thermo([(1, 4), (2, 3), (3, 2)], slow=True)
    .thermo([(1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)], slow=True)
    .thermo([(1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (7, 0)], slow=True)
    .thermo([(1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2), (7, 1), (8, 0)], slow=True)
    .thermo([(1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3), (7, 2)], slow=True)
    .thermo([(2, 8), (3, 7), (4, 6), (5, 5), (6, 4)], slow=True)
    .thermo([(3, 8), (4, 7), (5, 6), (6, 5), (7, 4)], slow=True)
    .thermo([(4, 8), (5, 7), (6, 6), (7, 5), (8, 4)], slow=True)
)
solution = s.solve()

Solver.pretty_print(solution)
