from solver import Solver, _
import z3
from snake import snake, pretty_print

# https://www.youtube.com/watch?v=jhql-MGWtPU

# very slow

given = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, 3, _, _, _, _, _),
    (_, _, _, _, _, _, 3, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, 4, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)

no_arrows = []
for r, row in enumerate(given):
    for c, v in enumerate(row):
        if v is not None:
            no_arrows.append((c, r))

CIRCLES = [
    (0, 0), (4, 0), (6, 0),
    (1, 1),
    (2, 2), (8, 2),
    (1, 3),
    (1, 4), (3, 4), (7, 4),
    (0, 5), (3, 5),
    (2, 6), (5, 6), (8, 6),
    (6, 7), (7, 7),
    (0, 8), (4, 8),
]

z3_solver = None
grid = []


ARROWS = [
    [(1, 0), (2, 0)],
    [(-1, 0), (-2, 0)],
    [(0, -1), (0, -2)],
    [(0, 1), (0, 2)],

    [(0, 1), (1, 1)],
    [(0, 1), (-1, 1)],

    [(0, -1), (1, -1)],
    [(0, -1), (-1, -1)],

    [(1, 0), (1, -1)],
    [(1, 0), (1, 1)],

    [(-1, 0), (-1, -1)],
    [(-1, 0), (-1, 1)],
]


def hidden_arrows(s, vars):
    global z3_solver, grid

    z3_solver = s

    for r in range(9):
        row = []
        for c in range(9):
            v = z3.Int("arrows_%s_%s" % (c, r))

            s.add(v >= 0, v <= len(CIRCLES))

            row.append(v)

        grid.append(row)

    vs = [v for row in vars for v in row]
    gs = [g for row in grid for g in row]

    for i, (c, r) in enumerate(CIRCLES, 1):
        or_terms = []
        for deltas in ARROWS:
            arrow = [(c + dc, r + dr) for dc, dr in deltas]

            ok = True
            for ac, ar in arrow:
                if ac < 0 or ac >= 9 or ar < 0 or ar >= 9:
                    ok = False
                    break

                if (ac, ar) in no_arrows:
                    ok = False
                    break

                if (ac, ar) in CIRCLES:
                    ok = False
                    break

            if not ok:
                continue

            #print(i, c, r, arrow)

            and_terms = []
            for rr in range(9):
                for cc in range(9):
                    if (cc, rr) in arrow:
                        and_terms.append(grid[rr][cc] == i)
                    else:
                        and_terms.append(grid[rr][cc] != i)

            or_terms.append(z3.And(and_terms))

        s.add(z3.Or(or_terms))

        # arrows must sum to the number of circle
        s.add(z3.Sum([z3.If(g == i, v, 0) for g, v in zip(gs, vs)]) == vars[r][c])

s = (
    Solver(given)
    .circles(CIRCLES)
    .extra_constraint(hidden_arrows)
)

solution = s.solve()

Solver.pretty_print(solution)

m = z3_solver.model()
r = [[m[grid[r][c]] for c in range(9)] for r in range(9)]

def pad(x):
    if x.as_long() > 0:
        return str(x).ljust(2)
    else:
        return ". "

for row in r:
    print(" ".join(map(pad, row)))

