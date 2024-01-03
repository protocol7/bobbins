from solver import Solver
import z3

# https://app.crackingthecryptic.com/tNJDm73TjD

x = z3.Int("x")

s = (
    Solver.regular_6x6()
    .unique_negative_diagonal()
    .unique_positive_diagonal()
    .little_killer([(0, 1), (1, 0)], x)
    .little_killer([(0, 4), (1, 5)], x + 2)
    .little_killer([(5, 1), (4, 0)], x + 1)
    .little_killer([(3, 5), (4, 4), (5, 3)], x * 2)
    .killer_cage([(3, 4), (3, 5)], x * 2)
)

solution = s.solve()

Solver.pretty_print(solution)
