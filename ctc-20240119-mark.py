from solver import Solver, _
import z3
from utils import z3_max, z3_count

# https://www.youtube.com/watch?v=L3UsxYlP2_U

s = z3.Solver()

# the board, made up of a list of list of integer variables
vars = []
placeholders = []
for r in range(6):
    row = []
    prow = []
    for c in range(6):
        v = z3.Int("c%sr%s" % (c, r))
        s.add(v >= 0, v <= 6)

        row.append(v)

        p = z3.Int("p%sr%s" % (c, r))
        s.add(p == r * 6 + c + 1000)

        prow.append(p)

    # each row contains a digit at most once

    vars.append(row)
    placeholders.append(prow)

    s.add(z3.Distinct([z3.If(v == 0, p, v) for v, p in zip(row, prow)]))

    s.add(z3_max(row) == z3_count(lambda v: v > 0, row))
    s.add(z3_count(lambda v: v > 0, row) > 0)

# each column contains a digit at most once
tvars = map(list, zip(*vars))
tplaceholders = map(list, zip(*placeholders))
for col, pcol in zip(tvars, tplaceholders):
    s.add(z3.Distinct([z3.If(v == 0, p, v) for v, p in zip(col, pcol)]))

    s.add(z3_max(col) == z3_count(lambda v: v > 0, col))
    s.add(z3_count(lambda v: v > 0, col) > 0)

# verify regions are correct
for region in Solver.REGULAR_6X6_REGIONS:
    s.add(z3.Distinct([z3.If(vars[r][c] == 0, placeholders[r][c], vars[r][c]) for c, r in region]))

    rs = [vars[r][c] for c, r in region]
    s.add(z3_max(rs) == z3_count(lambda v: v > 0, rs))
    s.add(z3_count(lambda v: v > 0, rs) > 0)

# region sum lines
s.add(vars[3][0] == vars[4][1], vars[4][1] > 0)

k = z3.Int("rs0")
s.add(k > 0)
s.add(vars[0][3] + vars[0][4] + vars[1][3] == k)
s.add(vars[2][4] + vars[3][4] == k)
s.add(vars[4][3] == k)

k = z3.Int("rs1")
s.add(k > 0)
s.add(vars[0][5] + vars[1][4] + vars[1][5] == k)
s.add(vars[2][5] + vars[3][5] == k)
s.add(vars[4][5] == k)

# renbans
RENBANS = [
    [(1, 1), (0, 2), (0, 3)],
    [(2, 1), (1, 2), (1, 3)],
    [(3, 2), (2, 3), (1, 4)],
    [(0, 4), (1, 5), (2, 5), (3, 5), (4, 4)],
]

for renban in RENBANS:
    vs = [vars[r][c] for c, r in renban]
    ps = [placeholders[r][c] for c, r in renban]
    s.add(z3.Distinct([z3.If(v == 0, p, v) for v, p in zip(vs, ps)]))

    s.add(z3_count(lambda v: v > 0, vs) > 0)

    for i, v0 in enumerate(vs):
        for j, v1 in enumerate(vs):
            if i >= j:
                continue

            s.add(z3.Or(
                v0 == 0,
                v1 == 0,
                z3.Abs(v0 - v1) < z3_count(lambda v: v > 0, vs)
                ))


if s.check() == z3.sat:
    m = s.model()
    grid = [[m[vars[r][c]] for c in range(len(vars[0]))] for r in range(len(vars))]

    for row in grid:
        print(" ".join(map(str, row)))
else:
    print("No solution")
