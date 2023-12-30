from solver import Solver
import z3

# https://www.youtube.com/watch?v=9RXpL65r2cU


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


ZIPPER_LINES = [
    [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0)],
    [(2, 1), (3, 1), (2, 2)],
    [(1, 2), (2, 3), (3, 4)],
    [(4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7)],
    [(7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)],
    [(0, 8), (1, 8), (1, 7), (1, 6), (2, 6)],
    [(2, 8), (3, 8), (4, 8), (5, 7), (5, 8)],
    [(6, 8), (7, 8), (8, 8)],
]


def doubler_zipper(s, vars):
    for line in ZIPPER_LINES:
        assert len(line) % 2 == 1

        middle_i = len(line) // 2
        part1 = line[:middle_i][::-1]
        part2 = line[middle_i+1:]

        assert len(part1) == len(part2)

        mc, mr = line[middle_i]
        vsum = vars[mr][mc] * multipliers[mr][mc]

        for (c0, r0), (c1, r1) in zip(part1, part2):
            s.add(vsum == vars[r0][c0] * multipliers[r0][c0] + vars[r1][c1] * multipliers[r1][c1])


BLACK_KROPKIS = [
    [(2, 5), (3, 5)],
    [(2, 5), (2, 6)],
    [(0, 6), (0, 7)],
]


def doubler_kropkis(s, vars):
    for (c0, r0), (c1, r1) in BLACK_KROPKIS:
        v0 = vars[r0][c0]
        v1 = vars[r1][c1]
        m0 = multipliers[r0][c0]
        m1 = multipliers[r1][c1]

        s.add(z3.Or(v0 * m0 * 2 == v1 * m1, v1 * m1 * 2 == v0 * m0))


BLUE_DOTS = [
    [(6, 0), (7, 0)],
    [(2, 4), (3, 4)],
]


def doubler_blue_dots(s, vars):
    for (c0, r0), (c1, r1) in BLUE_DOTS:
        v0 = vars[r0][c0]
        v1 = vars[r1][c1]
        m0 = multipliers[r0][c0]
        m1 = multipliers[r1][c1]

        s.add(z3.Or(v0 * m0 * 2 == v1 * m1 * 3, v1 * m1 * 2 == v0 * m0 * 3))


solver.extra_constraint(doublers)
solver.extra_constraint(doubler_zipper)
solver.extra_constraint(doubler_kropkis)
solver.extra_constraint(doubler_blue_dots)

solution = solver.solve()

if solution is None:
    print("No solution")
else:
    m = z3_solver.model()
    r = [[m.evaluate(multipliers[r][c]) for c in range(9)] for r in range(9)]

    Solver.pretty_print(solution)
    print("")
    Solver.pretty_print(r)
