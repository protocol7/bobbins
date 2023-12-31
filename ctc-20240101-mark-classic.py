from solver import Solver, _

# https://www.youtube.com/watch?v=OCAQVwoJolQ

given = (
    (1, _, _, _, 3, _, _, _, 9),
    (_, 2, _, _, 4, _, _, 8, _),
    (_, _, 3, _, _, _, 7, _, _),
    (_, _, _, 4, _, 3, 5, _, _),
    (2, 3, _, _, 5, _, _, 7, 8),
    (_, _, _, 6, _, 7, _, _, _),
    (_, _, 7, _, _, _, 3, _, 5),
    (_, 8, _, _, 6, _, _, 2, _),
    (9, _, _, _, 7, _, _, _, 1),
)


s = Solver(given)

solution = s.solve()

Solver.pretty_print(solution)
print("")
