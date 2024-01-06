from solver import Solver, _

# https://www.youtube.com/watch?v=REEw_ioi4J8


def no_nines(s, vars):
    for c, r in [(2, 2), (3, 2), (2, 3), (3, 3)]:
        s.add(vars[r][c] != 9)


def parity_line(s, vars):
    line = [
        (3, 4), (4, 5), (5, 4), (6, 5), (6, 6), (5, 7),
        (4, 8), (3, 7), (2, 6), (2, 5)
        ]

    for (c0, r0), (c1, r1) in zip(line, line[1:]):
        v0 = vars[r0][c0]
        v1 = vars[r1][c1]

        s.add(v0 % 2 != v1 % 2)


KINGS = [
    [(2, 1), (3, 2)],
    [(3, 1), (2, 2)],
    [(5, 1), (6, 2)],
    [(6, 1), (5, 2)],
    [(0, 2), (1, 3)],
    [(4, 2), (3, 3)],
    [(7, 2), (6, 3)],
    [(8, 2), (7, 3)],

    [(2, 3), (3, 4)],
    [(5, 3), (6, 4)],
    [(6, 3), (5, 4)],
    [(2, 4), (3, 5)],

    [(1, 5), (2, 6)],
    [(2, 5), (3, 6)],
    [(5, 5), (6, 6)],
    [(6, 5), (5, 6)],
    [(7, 5), (8, 6)],

    [(2, 7), (3, 8)],
    [(3, 7), (2, 8)],
    [(5, 7), (6, 8)],
]


def kings(s, vars):
    for r, row in enumerate(vars):
        for c, v in enumerate(row):
            for dc, dr in [(-1, 1), (1, 1)]:
                cc = c + dc
                rr = r + dr

                if cc < 0 or rr < 0 or cc >= 9 or rr >= 9:
                    continue

                vv = vars[rr][cc]

                if [(c, r), (cc, rr)] in KINGS:
                    s.add(v == vv)
                else:
                    s.add(v != vv)


s = (
    Solver()
    .killer_cage([(3, 0), (4, 0), (5, 0)], 14)
    .killer_cage([(5, 2), (6, 2), (5, 3), (6, 3)], 23)
    .renban_lines([
        [(0, 2), (0, 1), (0, 0), (1, 1), (2, 0), (2, 1), (2, 2)],
        [(7, 0), (7, 1), (7, 2)],
        [(3, 3), (3, 4), (3, 5), (4, 5), (5, 5)],
        [(0, 6), (0, 7), (0, 8), (1, 6), (1, 8)],
        [(7, 6), (7, 7), (7, 8)],
    ])
    .anti_knight()
    .extra_constraint(no_nines)
    .extra_constraint(parity_line)
    .extra_constraint(kings)
)

solution = s.solve()

Solver.pretty_print(solution)
print("")
