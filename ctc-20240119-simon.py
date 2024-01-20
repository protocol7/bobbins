from solver import Solver, _

# https://www.youtube.com/watch?v=fGUb_E2W558

solver = (
    Solver()
    .magic_squares([(4, 4)])
    .killer_cage([(2, 2), (2, 3), (3, 3), (2, 4), (3, 4), (2, 5)], 37)
    .killer_cage([(3, 2), (4, 2), (5, 2), (6, 2), (4, 3), (5, 3)], 39)
    .killer_cage([(6, 3), (5, 4), (6, 4), (5, 5), (6, 5), (6, 6)], 38)
    .killer_cage([(3, 5), (4, 5), (2, 6), (3, 6), (4, 6), (5, 6)], 36)
    .white_kropkis([
        [(0, 0), (0, 1)],
        [(1, 0), (1, 1)],
        [(0, 1), (1, 1)],
        [(7, 1), (7, 2)],
        [(1, 6), (1, 7)],
        [(7, 7), (8, 7)],
        [(7, 7), (7, 8)],
    ])
    .vs([
        [(4, 0), (4, 1)],
        [(0, 4), (1, 4)],
    ])
    .xs([
        [(7, 4), (8, 4)],
        [(4, 7), (4, 8)],
    ])
)

solution = solver.solve()

Solver.pretty_print(solution)
