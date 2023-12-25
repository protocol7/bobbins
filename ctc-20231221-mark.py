from solver import Solver

# https://www.youtube.com/watch?v=ACpwLkIUV1E

given = (
    (0, 3, 2, 8, 0, 0, 0, 9, 7),
    (0, 0, 0, 0, 3, 0, 0, 0, 6),
    (9, 8, 0, 0, 2, 0, 1, 0, 0),
    (0, 5, 0, 0, 0, 3, 9, 0, 8),
    (0, 2, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 9, 1, 4, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 5, 0, 0, 9),
    (0, 0, 0, 3, 1, 0, 0, 0, 5),
    (7, 0, 0, 4, 0, 6, 3, 0, 0),
)

s = Solver(given)

solution = s.solve()

Solver.pretty_print(solution)
