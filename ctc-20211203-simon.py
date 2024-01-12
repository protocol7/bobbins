from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=9wM7Jgy4QL8


solver = (
    Solver()
    .killer_cage([(6, 0), (7, 0), (8, 0), (8, 1), (8, 2)], 17)
    .killer_cage([(1, 1), (2, 1), (3, 1)], 14)
    .killer_cage([(5, 1), (5, 2), (5, 3), (6, 3), (7, 3)], 29)
    .killer_cage([(2, 2), (3, 2), (3, 3)], 21)
    .killer_cage([(0, 3), (0, 4), (1, 4), (2, 4), (0, 5)], 17)
    .killer_cage([(5, 5), (6, 5), (6, 6)], 21)
    .killer_cage([(7, 5), (7, 6), (7, 7)], 18)
    .killer_cage([(1, 6), (2, 6), (2, 7)], 20)
    .killer_cage([(4, 6), (4, 7), (3, 8), (4, 8), (5, 8)], 22)
)

solution = solver.solve()

Solver.pretty_print(solution)
