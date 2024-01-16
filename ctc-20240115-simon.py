from solver import Solver, _
import z3
from utils import z3_max

# https://www.youtube.com/watch?v=ndSJVl17heo

s = z3.Solver()

# the board, made up of a list of list of integer variables
vars = []
for r in range(6):
    row = []
    for c in range(6):
        v = z3.Real("c%sr%s" % (c, r))
        s.add(v >= 1, v <= 9)

        row.append(v)

    # each row contains a digit at most once
    s.add(z3.Distinct(row))

    vars.append(row)

# each column contains a digit at most once
for col in map(list, zip(*vars)):
    s.add(z3.Distinct(col))

# verify regions are correct
for region in Solver.REGULAR_6X6_REGIONS:
    s.add(z3.Distinct([vars[r][c] for c, r in region]))

s.add(vars[0][1] == 2)
s.add(vars[5][2] == 1)

s.add(vars[1][1] + vars[1][2] == vars[1][3] * vars[1][4])
s.add(vars[2][0] + (vars[2][1] * vars[2][2]) == vars[2][3])

s.add(vars[4][1] + vars[4][2] + vars[4][3] + vars[4][4] == vars[4][5])
s.add(vars[5][0] + vars[5][1] + vars[5][2] + vars[5][3] == vars[5][4])

if s.check() == z3.sat:
    m = s.model()
    grid = [[m[vars[r][c]] for c in range(len(vars[0]))] for r in range(len(vars))]

    for row in grid:
        print(" ".join(map(str, row)))
else:
    print("No solution")
