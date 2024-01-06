from solver import Solver

# https://www.youtube.com/watch?v=K_Dh1mMmHJo

s = (
    Solver(Solver.EMPTY)
    .unique_negative_diagonal()
    .black_kropkis([
        [(0, 0), (0, 1)],
        [(2, 0), (2, 1)],
        [(7, 0), (7, 1)],
        [(5, 6), (6, 6)],
    ])
    .arrows([
        [(4, 3), (4, 2), (3, 1), (3, 0)],
        [(4, 3), (4, 2), (5, 1), (5, 0)],

        [(1, 5), (1, 6), (0, 7), (0, 8)],
        [(1, 5), (1, 6), (2, 7), (2, 8)],

        [(7, 6), (7, 5), (6, 5), (6, 4)],
        [(7, 6), (7, 5), (8, 5), (8, 4)],

        [(3, 8), (3, 7), (4, 7), (4, 6)],
        [(5, 8), (5, 7), (4, 7), (4, 6)],
    ])
)

solution = s.solve()

Solver.pretty_print(solution)
