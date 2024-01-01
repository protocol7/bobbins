from solver import Solver

# https://www.youtube.com/watch?v=eoh0Bp4svp8

# takes 14 min to solve!

s = (
    Solver(Solver.EMPTY)
    .white_kropkis([
        [(0, 0), (1, 0)],
        [(8, 1), (8, 2)],
        [(3, 2), (4, 2)],
        [(2, 4), (2, 5)],
        [(6, 7), (7, 7)],
    ])
    .black_kropkis([
        [(3, 0), (4, 0)]
    ])
    .killer_cage([(2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (3, 2), (4, 2), (5, 2), (4, 3)])
    .killer_cage([(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (3, 4)])
    .killer_cage([(2, 7), (3, 7), (4, 7), (5, 7), (6, 7), (3, 6), (4, 6), (5, 6), (4, 5)])
    .killer_cage([(7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (6, 3), (6, 4), (6, 5), (5, 4)])

    .little_killer([
        (0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)
    ], 26)
    .little_killer([
        (8, 0), (7, 1), (6, 2), (5, 3), (4, 4), (3, 5), (2, 6), (1, 7), (0, 8)
    ], 32)
    .little_killer([
        (0, 3), (1, 2), (2, 1), (3, 0)
    ], 16)
    .little_killer([
        (8, 3), (7, 2), (6, 1), (5, 0)
    ], 21)
    .little_killer([
        (3, 8), (2, 7), (1, 6), (0, 5)
    ], 17)
)
solution = s.solve()

Solver.pretty_print(solution)
