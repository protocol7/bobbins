from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=AJ4-G-UFAjg


TEN_SUM_LINES = [
    [(3, 0), (2, 1)],
    [(4, 0), (3, 1), (2, 2)],
    [(7, 0), (7, 1)],
    [(0, 1), (0, 2), (0, 3), (1, 4)],
    [(4, 1), (5, 2)],
    [(6, 2), (5, 3), (4, 4)],
    [(8, 2), (7, 3), (8, 3)],
    [(3, 3), (2, 4)],
    [(6, 4), (6, 5), (5, 6)],
    [(3, 5), (3, 6)],
    [(0, 6), (1, 6), (2, 6)],
    [(6, 6), (7, 6), (8, 6)],
    [(1, 7), (1, 8)],
    [(3, 7), (4, 8)],
    [(6, 7), (6, 8)],
    [(8, 7), (8, 8)],
]


# divide n into a lists of lists it digits that adds up to n, each digits is at least 2
# 5 -> |5], [2, 3], [3, 2]
# 6 -> [6], [2, 4], [4, 2], [3, 3]
def divide(n, ds=[]):
    if n == 0:
        return [ds]
    if n < 1:
        return []

    out = []
    for i in range(1, n + 1):
        out.extend(divide(n - i, ds + [i]))
    return out


assert [[1, 1], [2]] == divide(2)
assert [[1, 1, 1], [1, 2], [2, 1], [3]] == divide(3)


def ten_sum_lines(s, vars):
    for line in TEN_SUM_LINES:
        vs = [z3.If(vars[r][c] == 1, 10, vars[r][c]) for c, r in line]

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
    Solver()
    .extra_constraint(ten_sum_lines)
)
solution = s.solve()

Solver.pretty_print(solution)
