from starbattle import Solver

# https://www.youtube.com/watch?v=xyeT5OHul2A

s = (
    Solver([
        [
            (2, 0), (1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4),
            (0, 5), (0, 6), (0, 7), (1, 3), (2, 3), (3, 3),
            (2, 2), (3, 2), (1, 5), (2, 5), (3, 5), (1, 6)
        ],
        [
            (3, 0), (4, 0), (5, 0), (6, 0), (7, 0),
            (5, 1), (5, 2), (6, 2), (6, 3),
        ],
        [(1, 2), (1, 1)],
        [(2, 1), (3, 1), (4, 1), (4, 2), (4, 3), (5, 3)],
        [(1, 4), (2, 4)],
        [(2, 6), (3, 6), (4, 6), (4, 5)],
        [(1, 7), (2, 7), (3, 7), (4, 7)],
        [
            (6, 1), (7, 1), (7, 2), (7, 3),
            (3, 4), (4, 4), (5, 4), (6, 4), (7, 4),
            (5, 5), (6, 5), (7, 5),
            (5, 6), (6, 6), (7, 6),
            (5, 7), (6, 7), (7, 7),
        ],
    ], width=8, height=8, stars=1)
)
solution = s.solve()

Solver.pretty_print(solution)