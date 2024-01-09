from solver import Solver

# https://www.youtube.com/watch?v=Vc-FYo_nur4

s = (
    Solver()
    .arrows([
        [(2, 2), (3, 3)],
        [(2, 2), (1, 3), (1, 4), (1, 5)],

        [(6, 2), (5, 3)],
        [(6, 2), (5, 1), (4, 1), (3, 1)],

        [(2, 6), (3, 5)],
        [(2, 6), (3, 7), (4, 7), (5, 7)],

        [(6, 6), (5, 5)],
        [(6, 6), (7, 5), (7, 4), (7, 3)],
    ])
    .little_killer([(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)], 55)
    .little_killer([(2, 0), (1, 1), (0, 2)], 8)
    .little_killer([(8, 0), (7, 1), (6, 2), (5, 3), (4, 4), (3, 5), (2, 6), (1, 7), (0, 8)], 53)
    .little_killer([(0, 3), (1, 4), (2, 5), (3, 6), (4, 7), (5, 8)], 31)
    .little_killer([(8, 5), (7, 4), (6, 3), (5, 2), (4, 1), (3, 0)], 26)
    .little_killer([(6, 8), (7, 7), (8, 6)], 15)
)

solution = s.solve()

Solver.pretty_print(solution)
