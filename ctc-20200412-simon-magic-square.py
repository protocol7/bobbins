from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=hAyZ9K2EBF0

givens = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (3, 8, 4, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, 2),
)

s = (
    Solver(givens)
    .unique_negative_diagonal()
    .unique_positive_diagonal()
    .anti_knight()
    .magic_squares([(4, 4)])
)
solution = s.solve()

Solver.pretty_print(solution)
