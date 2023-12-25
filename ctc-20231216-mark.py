from solver import Solver

# https://app.crackingthecryptic.com/q9tbRnF4Nh

s = (
    Solver(Solver.EMPTY)
    .smaller_than((0, 1), (0, 0))
    .killer_cage([(0, 0), (0, 1), (0, 2), (1, 2)], 12)
    .killer_cage([(4, 0), (5, 0), (6, 0), (6, 1)], 20)
    .killer_cage([(3, 1), (3, 2), (4, 2), (3, 3)], 12)
    .killer_cage([(6, 2), (7, 2), (6, 3), (6, 4)], 12)
    .killer_cage([(0, 4), (1, 4), (2, 4), (0, 5)], 20)
    .killer_cage([(8, 4), (8, 5), (8, 6), (7, 6)], 28)
    .killer_cage([(5, 5), (5, 6), (5, 7), (4, 6)], 28)
    .killer_cage([(1, 6), (2, 6), (2, 7), (2, 8)], 28)
    .unique_negative_diagonal()
)
solution = s.solve()

Solver.pretty_print(solution)
