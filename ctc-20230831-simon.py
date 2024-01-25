from solver import Solver
import z3
from utils import z3_count

# https://www.youtube.com/watch?v=39oIdXDf3J4

LINES = [
    ([
        [(2, 0), (1, 0), (0, 1), (0, 2)],
        [(1, 2), (2, 2), (2, 1)],
    ], [(1, 2), (2, 2)]),
    [[
        [(3, 0), (3, 1)],
        [(3, 2), (4, 1), (5, 2)],
    ], [(5, 0)]],
    [[
        [(6, 0), (7, 1), (8, 2)],
        [(6, 1), (7, 2)],
    ], [(8, 1)]],
    [[
        [(1, 4), (0, 3), (0, 4), (0, 5)],
        [(2, 3), (2, 4), (2, 5), (1, 5)],
    ], [(1, 4), (2, 4)]],
    [[
        [(3, 4), (4, 4), (5, 5)],
    ], [(4, 3), (5, 3)]],
    [[
        [(8, 3), (7, 3), (6, 3), (6, 4), (6, 5), (7, 5), (8, 5)],
    ], [(7, 4), (8, 4)]],
    [[
        [(0, 6), (1, 7)],
        [(0, 7), (0, 8), (1, 8), (2, 8), (2, 7)],
    ], [(0, 8), (1, 8)]],
    [[
        [(5, 6), (4, 6), (3, 6), (3, 7), (3, 8), (4, 8), (5, 8), (5, 7)],
    ], [(4, 7), (5, 7)]],
    [[
        [(6, 6), (7, 6), (7, 7)],
        [(6, 8), (7, 8), (8, 7), (8, 6)],
    ], [(7, 6), (8, 6)]],
]


def parity_paradox(s, vars):
    ks = []

    for i, (lines, sum_digits) in enumerate(LINES):
        sum = z3.Int(f"sum{i}")
        s.add(sum > 0)
        for line in lines:
            vs = [vars[r][c] for c, r in line]
            s.add(z3.Sum(vs) == sum)

        if len(sum_digits) > 1:
            (c0, r0), (c1, r1) = sum_digits
            v0 = vars[r0][c0]
            v1 = vars[r1][c1]

            s.add(sum / 10 == v0)
            s.add(sum % 10 == v1)

            ks.append(v0 * 10 + v1)
        else:
            c0, r0 = sum_digits[0]
            v0 = vars[r0][c0]

            s.add(sum == v0)

            ks.append(v0)

    # purple
    p = vars[5][3]

    s.add(p % 2 == 0, z3_count(lambda k: k % 2 == p % 2, ks) == p)


solver = (
    Solver()
    .extra_constraint(parity_paradox)
)


solution = solver.solve()

Solver.pretty_print(solution)
