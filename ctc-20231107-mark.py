from solver import Solver

# https://www.youtube.com/watch?v=S2zrc85C2BM

s = (
    Solver(Solver.EMPTY)
    .unique_positive_diagonal()
    .white_kropkis([((4, 0), (5, 0)), ((3, 8), (4, 8))])
    .black_kropkis([((0, 4), (0, 5)), ((8, 4), (8, 5))])
    .entropic_lines([
        [(0, 1), (0, 2)],
        [(8, 6), (8, 7)],
        [(3, 4), (4, 5)],
        [(3, 5), (4, 4), (5, 3)],

        [(4, 2), (5, 2), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (5, 6), (4, 6), (3, 6), (2, 6), (2, 5)],
        [
            (1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1),
            (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7),
            (6, 7), (5, 7), (4, 7), (3, 7), (2, 7), (1, 7),
            (1, 6), (1, 5), (1, 4), (1, 3), (1, 2)
        ],
    ])
)
solution = s.solve()

Solver.pretty_print(solution)
