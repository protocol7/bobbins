from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=JFzuOQDTnr8

k_index = 0
COLS = None
ROWS = None


def rooms(s, vars):
    global COLS, ROWS

    def k():
        global k_index
        k = z3.Int(f"k{k_index}")
        k_index += 1
        s.add(k >= 1, k <= 9)
        return k

    COLS = {
        (0, 0): k(),
        (1, 0): k(),
        (5, 0): k(),
        (6, 0): k(),
        (7, 0): k(),
        (8, 0): k(),

        (0, 8): k(),
        (1, 8): k(),
        (2, 8): k(),
        (3, 8): k(),
        (7, 8): k(),
        (8, 8): k(),
    }

    ROWS = {
        (0, 0): k(),
        (0, 1): k(),
        (0, 2): k(),
        (0, 3): k(),
        (0, 5): k(),
        (0, 6): k(),
        (0, 7): k(),
        (0, 8): k(),

        (8, 0): k(),
        (8, 1): k(),
        (8, 5): k(),
        (8, 6): k(),
        (8, 7): k(),
        (8, 8): k(),
    }

    WHITES = [
        [((0, 0, COLS), (1, 0, COLS), (0, 0, None), (0, 0, None)), [2, 9]],
        [((8, 0, None), (8, 0, ROWS), (8, 1, None), (8, 1, ROWS)), [4, 5, 6]],
        [((6, 1, None), (7, 1, None), (6, 2, None), (7, 2, None)), [4, 6]],
        [((0, 2, ROWS), (0, 2, None), (0, 3, ROWS), (0, 3, None)), [9]],
        [((3, 2, None), (4, 2, None), (3, 3, None), (4, 3, None)), [4, 6]],
        [((4, 5, None), (5, 5, None), (4, 6, None), (5, 6, None)), [4, 6]],
        [((8, 5, None), (8, 5, ROWS), (8, 6, None), (8, 6, ROWS)), [7]],
        [((1, 6, None), (2, 6, None), (1, 7, None), (2, 7, None)), [4, 6]],
        [((0, 7, ROWS), (0, 7, None), (0, 8, ROWS), (0, 8, None)), [4, 5, 6]],
        [((7, 8, COLS), (8, 8, COLS), (7, 8, None), (8, 8, None)), [2, 9]],
    ]

    BLACKS = [
        [((5, 0, COLS), (6, 0, COLS), (5, 0, None), (6, 0, None)), [2]],
        [((7, 0, COLS), (8, 0, COLS), (7, 0, None), (8, 0, None)), [5, 9]],
        [((0, 0, ROWS), (0, 0, None), (0, 1, ROWS), (0, 1, None)), [1, 7]],
        [((1, 1, None), (2, 1, None), (1, 2, None), (2, 2, None)), [1, 7]],
        [((5, 3, None), (6, 3, None), (5, 4, None), (6, 4, None)), [3]],
        [((2, 4, None), (3, 4, None), (2, 5, None), (3, 5, None)), [3]],
        [((0, 5, ROWS), (0, 5, None), (0, 6, ROWS), (0, 6, None)), [7]],
        [((6, 6, None), (7, 6, None), (6, 7, None), (7, 7, None)), [3, 8]],
        [((8, 7, None), (8, 7, ROWS), (8, 8, None), (8, 8, ROWS)), [3, 8]],
        [((0, 8, None), (1, 8, None), (0, 8, COLS), (1, 8, COLS)), [5, 9]],
        [((2, 8, None), (3, 8, None), (2, 8, COLS), (3, 8, COLS)), [9]],
    ]

    for vs, digits in WHITES:
        for digit in digits:
            or_terms = []

            for c, r, xs in vs:
                if xs is None:
                    v = vars[r][c]
                else:
                    v = xs[(c, r)]
                or_terms.append(v == digit)
            s.add(z3.Or(or_terms))

    for vs, digits in BLACKS:
        for digit in digits:
            and_terms = []

            for c, r, xs in vs:
                if xs is None:
                    v = vars[r][c]
                else:
                    v = xs[(c, r)]
                and_terms.append(v != digit)
            s.add(z3.And(and_terms))

    def foo_col(col, row):
        return z3.If(row == 1, vars[0][col],
                     z3.If(row == 2, vars[1][col],
                           z3.If(row == 3, vars[2][col],
                                 z3.If(row == 4, vars[3][col],
                                       z3.If(row == 5, vars[4][col],
                                             z3.If(row == 6, vars[5][col],
                                                   z3.If(row == 7, vars[6][col],
                                                         z3.If(row == 8, vars[7][col], vars[8][col]))))))))

    def foo_row(col, row):
        return z3.If(col == 1, vars[row][0],
                     z3.If(col == 2, vars[row][1],
                           z3.If(col == 3, vars[row][2],
                                 z3.If(col == 4, vars[row][3],
                                       z3.If(col == 5, vars[row][4],
                                             z3.If(col == 6, vars[row][5],
                                                   z3.If(col == 7, vars[row][6],
                                                         z3.If(col == 8, vars[row][7], vars[row][8]))))))))

    # number rooms
    for (c, r), v in COLS.items():
        index = vars[r][c]

        if r == 8:
            index = 10 - index

        target = foo_col(c, index)
        s.add(target == v)

    for (c, r), v in ROWS.items():
        index = vars[r][c]

        if c == 8:
            index = 10 - index

        target = foo_row(index, r)
        s.add(target == v)


solver = (
    Solver()
    .extra_constraint(rooms)
)

solution = solver.solve()

vars = solution.grid
m = solution.z3_solver.model()
for r in range(9):
    if r == 0 or r == 8:
        extra_row = ["  "]
        for c in range(9):
            if (c, r) in COLS:
                extra_row.append(m[COLS[(c, r)]].as_long())
            else:
                extra_row.append(" ")

    if r == 0:
        print(" ".join(map(str, extra_row)))
        print()

    row = []
    if (0, r) in ROWS:
        row.append(m[ROWS[(0, r)]].as_long())
    else:
        row.append(" ")
    row.append("")

    for c in range(9):
        row.append(m[vars[r][c]].as_long())

    row.append("")
    if (8, r) in ROWS:
        row.append(m[ROWS[(8, r)]].as_long())
    else:
        row.append(" ")

    print(" ".join(map(str, row)))

    if r == 8:
        print()
        print(" ".join(map(str, extra_row)))
