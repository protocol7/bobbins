from solver import Solver

# https://www.youtube.com/watch?v=aBczbciOcwA


s = (
    Solver()
    .thermo([(2, 4), (2, 3), (3, 2), (2, 1)])
    .thermo([(6, 4), (7, 4), (7, 3), (8, 3)])
    .thermo([(0, 8), (0, 7), (1, 6), (0, 5)])
    .thermo([(2, 8), (2, 7), (3, 6), (2, 5)])
    .circles([
        (8, 0),

        (0, 2), (2, 2), (4, 2), (6, 2),
        (1, 3), (3, 3), (5, 3),

        (0, 4), (2, 4), (4, 4), (6, 4),
        (1, 5), (3, 5), (5, 5),

        (0, 6), (2, 6), (4, 6), (6, 6),
        (1, 7), (3, 7), (5, 7),

        (0, 8), (2, 8), (4, 8), (6, 8),
    ])
)

solution = s.solve()

Solver.pretty_print(solution)
