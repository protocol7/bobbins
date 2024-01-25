from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=XBeH6hhF6MQ

REGIONS = [
    [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)],
    [(5, 0), (6, 0), (7, 0), (8, 0), (7, 1)],
    [(9, 0), (8, 1), (9, 1), (8, 2), (9, 2)],
    [(0, 1), (1, 1), (0, 2), (0, 3), (0, 4)],
    [(2, 1), (1, 2), (2, 2), (3, 2), (2, 3)],
    [(3, 1), (4, 1), (4, 2), (3, 3), (4, 3)],
    [(5, 1), (6, 1), (6, 2), (7, 2), (7, 3)],
    [(5, 2), (5, 3), (6, 3), (4, 4), (5, 4)],
    [(1, 3), (1, 4), (0, 5), (1, 5), (2, 5)],
    [(8, 3), (6, 4), (7, 4), (8, 4), (6, 5)],
    [(9, 3), (9, 4), (7, 5), (8, 5), (9, 5)],
    [(2, 4), (3, 4), (3, 5), (4, 5), (5, 5)],
]

REGION_IDS = {}
for i, region in enumerate(REGIONS):
    for cell in region:
        REGION_IDS[cell] = i

GIVEN = (
    (_, 1, 2, _, _, 1, _, _, _, _),
    (_, _, _, _, _, 1, _, _, _, 0),
    (_, _, _, _, _, _, _, _, _, _),
    (0, _, 2, _, _, _, _, _, _, 3),
    (_, _, _, _, _, _, _, _, _, 4),
    (4, _, _, 2, _, _, 3, _, _, _),
)

PRIMES = [2, 3, 5, 7]

# check regions
seen = set()
for region in REGIONS:
    assert len(set(region)) == 5

    assert not (set(region) & seen)

    seen.update(region)

assert len(seen) == 60

solver = z3.Solver()

# 1. Define the grid
vars = []
for r in range(6):
    row = []
    for c in range(10):
        v = z3.Int(f"c{c}r{r}")
        solver.add(v >= 0, v <= 4)

        if GIVEN[r][c] != _:
            solver.add(v == GIVEN[r][c])

        row.append(v)

    vars.append(row)

for region in REGIONS:
    rs = [vars[r][c] for c, r in region]

    solver.add(z3.Distinct(rs))

for r in range(6):
    for c in range(10):
        for dc, dr in Solver.ORTHOGONAL:
            cc = c + dc
            rr = r + dr

            if cc < 0 or rr < 0 or cc >= 10 or rr >= 6:
                continue

            # across region boundaries
            if REGION_IDS[(c, r)] == REGION_IDS[(cc, rr)]:
                continue

            #print((c, r), (cc, rr), REGION_IDS[(c, r)], REGION_IDS[(cc, rr)])
            or_terms = []
            for prime in PRIMES:
                or_terms.append(vars[r][c] + vars[rr][cc] == prime)

            solver.add(z3.Or(or_terms))

if solver.check() == z3.sat:
    m = solver.model()
    for r in range(6):
        row = []
        for c in range(10):
            row.append(m[vars[r][c]])
        print(" ".join(map(str, row)))
else:
    print("No solution")
