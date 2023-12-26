from solver import Solver

# https://www.youtube.com/watch?v=naW99FoEXc8

s = (
    Solver(Solver.EMPTY)
    .anti_x_v()
    .arrows([
        ((1, 4), (0, 4), (1, 3), (2, 4)),
        ((3, 5), (3, 4), (4, 4)),
        ((5, 4), (5, 3), (4, 3)),
        ((7, 3), (8, 3), (7, 4), (6, 3)),
        ((0, 8), (1, 7), (2, 6)),
        ((4, 6), (4, 7), (4, 8)),
        ((5, 6), (6, 6), (7, 6)),
        ((8, 6), (7, 5), (6, 5)),
    ])
)
solution = s.solve()

Solver.pretty_print(solution)
