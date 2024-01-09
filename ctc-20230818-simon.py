from solver import Solver

# https://www.youtube.com/watch?v=t-SnwjwJD88

solver = (
    Solver()
    .unique_positive_diagonal()
    .arrows([
        [(2, 0), (3, 0), (4, 0)],
        [(8, 0), (7, 0), (6, 0)],
        [(3, 3), (2, 4)],
        [(3, 3), (2, 2), (1, 1), (1, 0)],
        [(7, 4), (8, 4), (8, 3)],
        [(0, 5), (0, 4), (1, 4)],
        [(2, 6), (3, 5), (4, 4), (5, 3)],
        [(4, 6), (5, 5)],
        [(4, 6), (3, 6), (4, 7), (4, 8)],
        [(7, 7), (7, 8), (8, 8)],
    ])
)


def parity_mirror(s, vars):
    for r in range(9):
        for c in range(9):
            if c == r:
                continue

            v0 = vars[r][c]
            v1 = vars[c][r]

            s.add(v0 % 2 == v1 % 2)


solver.extra_constraint(parity_mirror)

solution = solver.solve()

Solver.pretty_print(solution)
