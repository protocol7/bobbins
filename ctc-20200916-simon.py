from solver import Solver

# https://www.youtube.com/watch?v=Uex5HJh0wiY

s = (
    Solver(Solver.EMPTY)
    .killer_cage([(1, 0), (2, 0), (1, 1)], 22)
    .killer_cage([(3, 0), (3, 1), (3, 2)], 11)
    .killer_cage([(6, 0), (5, 0), (5, 1), (5, 2), (5, 3), (6, 3), (7, 3), (8, 3), (8, 2)], 45)
    .killer_cage([(7, 0), (7, 1), (8, 1)], 19)
    .killer_cage([(0, 1), (0, 2)], 10)
    .killer_cage([(0, 3), (1, 3)], 13)
    .killer_cage([(2, 3), (3, 3)], 6)
    .killer_cage([(0, 6), (0, 5), (1, 5), (2, 5), (3, 5), (3, 6), (3, 7), (3, 8), (2, 8)], 45)
    .killer_cage([(6, 5), (5, 5), (5, 6)], 21)
    .killer_cage([(7, 5), (8, 5)], 15)
    .killer_cage([(8, 6), (8, 7), (7, 7)], 13)
    .killer_cage([(0, 7), (1, 7), (1, 8)], 20)
    .killer_cage([(5, 7), (5, 8)], 14)
    .killer_cage([(6, 8), (7, 8)], 5)
)

solution = s.solve()

Solver.pretty_print(solution)
