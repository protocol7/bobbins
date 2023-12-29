from solver import Solver, _

# https://www.youtube.com/watch?v=8C-A7xmBLRU

givens = (
    (1, _, _, 4, _, _, 7, _, _),
    (_, 2, _, _, 5, _, _, 8, _),
    (_, _, 3, _, _, 6, _, _, 9),
    (_, 1, _, _, 4, _, _, 7, _),
    (_, _, 2, _, _, 5, _, _, 8),
    (9, _, _, 3, _, _, 6, _, _),
    (7, _, _, _, _, 8, _, _, 2),
    (8, _, _, 2, _, _, 9, _, _),
    (_, 9, _, _, 7, _, _, 1, _),
)

s = (
    Solver(givens)
)
solution = s.solve()

Solver.pretty_print(solution)
