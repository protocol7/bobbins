from solver import Solver, _
import z3
from regions import regions, pretty_print


# https://www.youtube.com/watch?v=TcwwvtZLQNw

GIVEN = (
    (_, _, _, _, _, _, 1, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)

XS = [
        [(1, 1), (2, 1)],
        [(4, 1), (5, 1)],
        [(2, 3), (3, 3)],
        [(5, 4), (5, 5)],
        [(2, 5), (2, 6)],
        [(0, 6), (1, 6)],
        [(0, 7), (1, 7)],
    ]

WHITES = [
        [(7, 0), (7, 1)],
        [(2, 1), (3, 1)],
        [(3, 1), (3, 2)],
        [(7, 4), (7, 5)],
        [(2, 7), (2, 8)],
        [(7, 7), (8, 7)],
        [(7, 7), (7, 8)],
        [(2, 8), (3, 8)],
    ]


z3_solver = None
region = None
solver = Solver(GIVEN)


def extras (s, vars):
    global z3_solver, region

    z3_solver = s
    region = regions(s, [None])[0]

    for (c0, r0), (c1, r1) in XS + WHITES:
        r0 = region[r0][c0]
        r1 = region[r1][c1]

        s.add(z3.Or(z3.And(r0 == 0, r1 > 0), z3.And(r0 > 0, r1 == 0)))

    # anti X if across the region
    for (c0, r0), v0, (c1, r1), v1 in solver.all_dominos(vars):
        if (c0, r0) > (c1, r1):
            continue

        s0 = region[r0][c0]
        s1 = region[r1][c1]

        if [(c0, r0), (c1, r1)] not in XS:
            s.add(z3.Or(
                z3.And(s0 == 0, s1 == 0),
                z3.And(s0 > 0, s1 > 0),
                v0 + v1 != 10
            ))

        if [(c0, r0), (c1, r1)] not in WHITES:
            s.add(z3.Or(
                z3.And(s0 == 0, s1 == 0),
                z3.And(s0 > 0, s1 > 0),
                z3.Abs(v0 - v1) != 1
            ))

    # 5 digits in the region, 4 outside
    ks = []
    for i in range(1, 10):
        k = z3.Int(f'k{i}')
        s.add(k >= 1, k <= 9)

        ks.append(k)

    s.add(z3.Distinct(ks))

    for r in range(9):
        for c in range(9):
            v = vars[r][c]
            g = region[r][c]

            s.add(z3.Or(
                z3.And(g > 0, v == ks[0]),
                z3.And(g > 0, v == ks[1]),
                z3.And(g > 0, v == ks[2]),
                z3.And(g > 0, v == ks[3]),
                z3.And(g > 0, v == ks[4]),

                z3.And(g == 0, v == ks[5]),
                z3.And(g == 0, v == ks[6]),
                z3.And(g == 0, v == ks[7]),
                z3.And(g == 0, v == ks[8]),
            ))

    # the puzzle solves without the squares or arrows constraint


solver = (
    solver
    .regions([
        [(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (3, 1), (0, 2), (1, 2)],
        [(4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (5, 1), (6, 1), (7, 1), (8, 1)],
        [(2, 1), (2, 2), (0, 3), (1, 3), (2, 3), (0, 4), (0, 5), (1, 5), (0, 6)],
        [(4, 1), (4, 2), (5, 2), (4, 3), (5, 3), (4, 4), (5, 4), (4, 5), (4, 6)],
        [(3, 2), (3, 3), (1, 4), (2, 4), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8)],
        [(6, 2), (7, 2), (8, 2), (8, 3), (7, 4), (8, 4), (8, 5), (8, 6), (8, 7)],
        [(6, 3), (7, 3), (6, 4), (5, 5), (6, 5), (7, 5), (5, 6), (7, 6), (5, 7)],
        [(2, 5), (1, 6), (2, 6), (0, 7), (1, 7), (2, 7), (0, 8), (1, 8), (2, 8)],
        [(6, 6), (4, 7), (6, 7), (7, 7), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8)],
    ])
    .xs(XS)
    .white_kropkis(WHITES)
    .extra_constraint(extras)
)

solution = solver.solve()

Solver.pretty_print(solution)

print()

pretty_print(z3_solver, region)
