from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=O8tnHFS3-Es

givens = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, 1),
)


TEN_SUM_LINES = [
    [(0, 2), (1, 1), (1, 2), (2, 2), (3, 2), (3, 1), (4, 1)],
    [(6, 0), (6, 1), (6, 2), (6, 3), (7, 4), (8, 4)],
    [(0, 3), (1, 3), (2, 3), (3, 4), (4, 4), (4, 5), (5, 5), (6, 6), (6, 7), (6, 8)],
    [(1, 6), (0, 7), (0, 8), (1, 8), (2, 8), (2, 7)],
]


# divide n into a lists of lists it digits that adds up to n, each digits is at least 2
# 5 -> |5], [2, 3], [3, 2]
# 6 -> [6], [2, 4], [4, 2], [3, 3]
def divide(n, ds=[]):
    if n == 0:
        return [ds]
    if n < 2:
        return []

    out = []
    for i in range(2, n + 1):
        out.extend(divide(n - i, ds + [i]))
    return out


assert [[2]] == divide(2)
assert [[3]] == divide(3)
assert [[2, 2], [4]] == divide(4)
assert [[2, 3], [3, 2], [5]] == divide(5)
assert [[2, 2, 2], [2, 4], [3, 3], [4, 2], [6]] == divide(6)
assert [[2, 2, 3], [2, 3, 2], [2, 5], [3, 2, 2], [3, 4], [4, 3], [5, 2], [7]] == divide(7)


def ten_sum_lines(s, cells):
    for line in TEN_SUM_LINES:
        vs = [cells[r][c] for c, r in line]
        or_constraints = []
        for chunks in divide(len(line)):
            and_constraints = []
            offset = 0
            for l in chunks:
                sub_vs = vs[offset:offset + l]
                and_constraints.append(z3.Sum(sub_vs) == 10)

                offset += l

            or_constraints.append(z3.And(and_constraints))

        s.add(z3.Or(or_constraints))

s = (
    Solver(givens)
    .white_kropkis([
        [(1, 3), (2, 3)],
        [(7, 7), (8, 7)],
    ])
    .palindrom_lines([
        [(0, 1), (1, 2), (1, 3), (0, 4), (1, 4)],
        [(3, 2), (4, 1), (5, 0), (6, 1), (7, 2), (7, 3)],
        [(0, 6), (1, 7), (2, 6), (3, 5), (4, 4), (5, 4), (6, 4)],

        [(4, 8), (4, 7), (5, 7), (6, 8), (7, 7)],
    ])
    .extra_constraint(ten_sum_lines)
)
solution = s.solve()

Solver.pretty_print(solution)
