from solver import Solver

# https://www.youtube.com/watch?v=YoO12J51Irs

given = (
    (0, 1, 2, 0, 3, 0, 4, 5, 0),
    (5, 6, 0, 0, 0, 0, 0, 0, 0),
    (3, 0, 0, 0, 0, 0, 0, 0, 2),
    (0, 7, 0, 0, 1, 5, 0, 0, 0),
    (0, 0, 0, 6, 0, 9, 0, 0, 0),
    (0, 0, 0, 4, 2, 0, 0, 8, 0),
    (1, 0, 0, 0, 0, 0, 0, 0, 3),
    (0, 0, 0, 0, 0, 0, 0, 2, 4),
    (0, 8, 3, 0, 4, 0, 5, 7, 0),
)

s = Solver(given)

solution = s.solve()

Solver.pretty_print(solution)
