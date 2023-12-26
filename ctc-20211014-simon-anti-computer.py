from solver import Solver

# https://www.youtube.com/watch?v=zR-ngVP0kVg

given = (
    (0, 0, 0, 1, 0, 2, 0, 0, 0),
    (0, 0, 8, 0, 6, 0, 7, 0, 5),
    (0, 9, 0, 0, 0, 0, 0, 8, 0),
    (4, 0, 0, 0, 1, 0, 0, 0, 0),
    (0, 8, 0, 3, 0, 4, 0, 6, 0),
    (3, 0, 0, 0, 2, 0, 8, 0, 0),
    (0, 6, 0, 0, 0, 5, 4, 7, 0),
    (0, 0, 5, 0, 7, 0, 6, 0, 9),
    (0, 7, 0, 0, 0, 0, 0, 5, 0),
)

s = Solver(given)

solution = s.solve()

Solver.pretty_print(solution)
