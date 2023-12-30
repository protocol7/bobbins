from solver import Solver
import z3

# https://www.youtube.com/watch?v=XPiF-OljHkY


multipliers = []

solver = Solver(Solver.EMPTY)
z3_solver = None


def doublers(s, vars):
    global z3_solver
    z3_solver = s

    for r in range(9):
        row = []
        for c in range(9):
            v = z3.Int("doubler_%s_%s" % (c, r))
            s.add(z3.Or(v == 1, v == 2))

            row.append(v)

        multipliers.append(row)

        # one doubler per row
        s.add(z3.Sum([z3.If(v == 2, 1, 0) for v in row]) == 1)

    for c in range(9):
        col = []
        for r in range(9):
            col.append(multipliers[r][c])

        # one doubler per col
        s.add(z3.Sum([z3.If(v == 2, 1, 0) for v in col]) == 1)

    for region in solver._regions:
        vs = [multipliers[r][c] for c, r in region]

        # one doubler per region
        s.add(z3.Sum([z3.If(v == 2, 1, 0) for v in vs]) == 1)

    # doublers must be distinct
    cs = []
    placeholders = []
    p_value = 1000
    for r in range(9):
        row = []
        for c in range(9):
            cs.append((c, r))

            p = z3.Int("placeholder_%s_%s" % (c, r))
            s.add(p == p_value)
            p_value += 1
            row.append(p)

        placeholders.append(row)

    s.add(z3.Distinct([z3.If(multipliers[r][c] == 2, vars[r][c], placeholders[r][c]) for c, r in cs]))
    #s.add(z3.Distinct([vars[r][c] for c, r in cs if z3.If(multipliers[r][c] == 2, True, False)]))



WHISPER_LINES = [
    [
        (1, 7), (0, 7), (0, 6), (0, 5), (0, 4), (0, 3), (0, 2), (0, 1), (0, 0),
        (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (8, 1),
        (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)
    ],
    [(2, 1), (2, 2), (2, 3), (2, 4), (2, 5)],
    [(4, 5), (5, 5), (5, 4)],
    [(2, 6), (3, 6), (4, 6), (5, 6), (6, 6), (6, 5)],
    [(5, 8), (6, 8), (6, 7)],
]


def doubler_whisper(s, vars):
    for line in WHISPER_LINES:
        for (c0, r0), (c1, r1) in zip(line, line[1:]):
            v0 = vars[r0][c0]
            v1 = vars[r1][c1]
            m0 = multipliers[r0][c0]
            m1 = multipliers[r1][c1]

            s.add(z3.Abs(v0 * m0 - v1 * m1) >= 5)


solver.extra_constraint(doublers)
solver.extra_constraint(doubler_whisper)

solution = solver.solve()

if solution is None:
    print("No solution")
else:
    m = z3_solver.model()
    r = [[m.evaluate(multipliers[r][c]) for c in range(9)] for r in range(9)]

    Solver.pretty_print(solution)
    print("")
    Solver.pretty_print(r)
