from solver import Solver
from collections import defaultdict
from itertools import permutations
import z3

# https://www.youtube.com/watch?v=2tgiH5QldMM


CAGES = [
    ([(2, 0), (2, 1)], 20),
    ([(3, 0), (4, 0), (4, 1)], 6),
    ([(7, 0), (7, 1), (8, 1), (6, 2), (7, 2), (6, 3)], 38),
    ([(0, 2), (1, 2), (0, 3)], 12),
    ([(2, 2), (3, 2)], 2),
    ([(2, 3), (2, 4), (2, 5)], 21),
    ([(8, 3), (8, 4), (8, 5)], 21),
    ([(0, 5), (1, 5), (1, 6)], 12),
    ([(4, 5), (4, 6), (3, 6)], 18),
    ([(2, 6), (2, 7)], 8),
    ([(7, 6), (8, 6)], 16),
    ([(0, 7), (0, 8)], 6),
    ([(4, 7), (4, 8)], 18),
    ([(6, 7), (7, 7)], 20),
    ([(8, 7), (8, 8)], 14),
    ([(2, 8), (3, 8)], 12),
    ([(6, 8), (7, 8)], 16),
]

THERMOS = [
    [(1, 0), (0, 1), (0, 0)],
    [(3, 1), (4, 2), (4, 3), (4, 4)],
    [(8, 1), (8, 0)],
    [(8, 1), (8, 2)],
    [(5, 2), (5, 3), (6, 2), (7, 3)],
    [(5, 4), (5, 5), (5, 6)],
    [(7, 5), (6, 4), (6, 5), (7, 4), (6, 3), (7, 2)],
    [(6, 6), (7, 6), (8, 6), (8, 7)],
    [(7, 8), (8, 8)],
    [
        (4, 8), (4, 7), (3, 7), (3, 6), (4, 6), (4, 5), (3, 4), (2, 3), (2, 4), (2, 5),
        (2, 6), (2, 7), (1, 7), (0, 8), (0, 7), (1, 6), (1, 5), (0, 5), (1, 4), (0, 3),
        (0, 2), (1, 2), (2, 2), (3, 2), (4, 1), (4, 0), (3, 0)
    ],
]


s = z3.Solver()

DIGITS = list(range(1, 10))

# the board, made up of a list of list of integer variables
vars = []
for r in range(9):
    row = []
    for c in range(9):
        v = z3.Int("c%sr%s" % (c, r))
        s.add(z3.Or([v == d for d in DIGITS]))

        row.append(v)

    # digits must repeat in rows
    for d in DIGITS:
        count = z3.Sum([z3.If(v == d, 1, 0) for v in row])
        s.add(z3.Or(count == 0, count > 1))

    vars.append(row)

# digits must repeat in cols
for col in map(list, zip(*vars)):
    for d in DIGITS:
        count = z3.Sum([z3.If(v == d, 1, 0) for v in col])
        s.add(z3.Or(count == 0, count > 1))

# digits must repeat in regions
for region in Solver.REGULAR_9X9_REGIONS:
    for d in DIGITS:
        count = z3.Sum([z3.If(vars[r][c] == d, 1, 0) for c, r in region])
        s.add(z3.Or(count == 0, count > 1))

# there are exactly 9 of each digit
vs = [v for vv in vars for v in vv]
for d in DIGITS:
    count = z3.Sum([z3.If(v == d, 1, 0) for v in vs])
    s.add(count == 9)

# digits must repeat in cages
for cage, sum in CAGES:
    for d in DIGITS:
        count = z3.Sum([z3.If(vars[r][c] == d, 1, 0) for c, r in cage])
        s.add(z3.Or(count == 0, count > 1))

    # cages can not sum to the sum
    s.add(z3.Sum([vars[r][c] for c, r in cage]) != sum)

# digits must not increase along a thermo
for thermo in THERMOS:
    for (c0, r0), (c1, r1) in zip(thermo, thermo[1:]):
        s.add(vars[r1][c1] <= vars[r0][c0])

# black kropki
for (c0, r0), (c1, r1) in [[(1, 5), (2, 5)]]:
    v0 = vars[r0][c0]
    v1 = vars[r1][c1]

    s.add(v0 * 2 != v1, v1 * 2 != v0)

if s.check() == z3.sat:
    m = s.model()
    r = [[m.evaluate(vars[r][c]) for c in range(9)] for r in range(9)]
    Solver.pretty_print(r)
else:
    print("No solution")
