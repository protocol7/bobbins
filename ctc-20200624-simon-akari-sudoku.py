from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=lSrflX09srw

givens = (
    (_, _, _, _, 9, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (5, _, _, _, _, _, _, 6, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, 7, _, _),
    (_, _, _, _, 3, _, _, _, _),
    (_, _, _, 4, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (4, _, _, _, _, _, _, _, 8),
)

bulbs = []
solver = Solver(givens)
z3_solver = None
GRAYS = set([
    (0, 0), (4, 0), (8, 0),
    (6, 1),
    (2, 2),
    (3, 3), (5, 3),
    (4, 4), (8, 4),
    (0, 5), (7, 5),
    (1, 6), (6, 6),
    (5, 7),
    (3, 8), (8, 8)
])


def akari(s, vars):
    global z3_solver
    z3_solver = s

    for r in range(9):
        row = []
        for c in range(9):
            v = z3.Int("bulb_c%sr%s" % (c, r))

            # 0 = black cell
            # 1 = lit up
            # 2 = light
            s.add(z3.Or(v == 0, v == 1, v == 2))

            row.append(v)

        bulbs.append(row)

        # two bulbs per row
        s.add(z3.Sum([z3.If(v == 2, 1, 0) for v in row]) == 2)

    # two bulbs per col
    for col in map(list, zip(*bulbs)):
        s.add(z3.Sum([z3.If(v == 2, 1, 0) for v in col]) == 2)

    # two bulbs per region
    for region in solver._regions:
        s.add(z3.Sum([z3.If(bulbs[r][c] == 2, 1, 0) for c, r in region]) == 2)

    # akair constraints
    for r, row in enumerate(vars):
        for c, v in enumerate(row):
            v = vars[r][c]

            if (c, r) in GRAYS:

                # gray cells can not be bulbs
                s.add(bulbs[r][c] == 0)

                ns = []
                for dc, dr in [(0, -1), (1, 0), (0, 1), (-1, 0)]:
                    nc = c + dc
                    nr = r + dr

                    if nc < 0 or nr < 0 or nc >= 9 or nr >= 9:
                        continue

                    ns.append(bulbs[nr][nc])

                s.add(z3.Or(
                    # 8 or 9 works as 0
                    z3.And(v >= 8, z3.Sum([z3.If(n == 2, 1, 0) for n in ns]) == 0),
                    # 1-4 works as normal
                    z3.And(v <= 4, z3.Sum([z3.If(n == 2, 1, 0) for n in ns]) == v),
                    # 5-7 has no constraint
                ))
            else:
                s.add(bulbs[r][c] > 0)

                seen = set()
                for dc, dr in [(0, -1), (1, 0), (0, 1), (-1, 0)]:
                    for i in range(1, 10):

                        nc = c + dc * i
                        nr = r + dr * i

                        if nc < 0 or nr < 0 or nc >= 9 or nr >= 9:
                            break

                        if (nc, nr) in GRAYS:
                            break

                        seen.add((nc, nr))

                # if this is a light, then all seen can not be light, and are lit up
                for nc, nr in seen:
                    s.add(bulbs[nr][nc] < z3.If(bulbs[r][c] == 2, 2, 3))

                # this is a light, or there must be at least one light in seen
                s.add(z3.Or(
                    bulbs[r][c] == 2,
                    z3.Sum([z3.If(bulbs[nr][nc] == 2, 1, 0) for nc, nr in seen]) > 0
                ))

                # a bulb will always have a value of 5, 6 or 7
                s.add(z3.Or(
                    bulbs[r][c] == 1,
                    z3.And(v >= 5, v <= 7)
                ))


solver.extra_constraint(akari)

solution = solver.solve()

if solution is None:
    print("No solution")
else:
    Solver.pretty_print(solution)
    print()

    m = z3_solver.model()

    r = [[m.evaluate(bulbs[r][c]) for c in range(9)] for r in range(9)]

    Solver.pretty_print(r)
