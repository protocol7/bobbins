import z3

ORTHOGONAL = [(0, -1), (1, 0), (0, 1), (-1, 0)]


def loop(
        s,
        width=9,
        height=9,
        must_include_cells=[],
        must_include_regions=[],
        dont_touch_diagonally=True):

    grid = []
    vs = []
    for r in range(height):
        row = []
        for c in range(width):
            v = z3.Int("loop_%s_%s" % (c, r))

            s.add(z3.Or(v >= 0))

            row.append(v)
            vs.append(v)

        grid.append(row)

    # are there any cells that must be part of the loop?
    for c, r in must_include_cells:
        s.add(grid[r][c] > 0)

    # are there some regions which must be part of the loop?
    for region in must_include_regions:
        or_constraints = []
        for c, r in region:
            or_constraints.append(grid[r][c] > 0)

        s.add(z3.Or(or_constraints))

    # start cell
    start_c = z3.Int("start_c")
    start_r = z3.Int("start_r")

    for r, row in enumerate(grid):
        for c, v in enumerate(row):

            ns = []
            for dc, dr in ORTHOGONAL:
                nc = c + dc
                nr = r + dr

                if nc < 0 or nr < 0 or nc >= width or nr >= height:
                    continue

                ns.append(grid[nr][nc])

            # all loop cells must have exactly two orthogonal neighbours
            count = z3.Sum([z3.If(nv > 0, 1, 0) for nv in ns])
            s.add(z3.Or(
                v == 0,
                z3.And(v > 0, count == 2)
            ))

            # each part (except for a starting point) should be connected with
            # another part that has a natural number less than its number
            #
            # https://www.cs.ru.nl/bachelors-theses/2021/Gerhard_van_der_Knijff___1006946___Solving_and_generating_puzzles_with_a_connectivity_constraint.pdf

            or_constraints = []
            for i in range(len(ns)):
                for j in range(len(ns)):
                    if i == j:
                        continue

                    or_constraints.append(z3.And(
                        v > 1,
                        ns[i] > 0,
                        ns[j] > 0,
                        z3.Or(ns[i] < v, ns[j] < v))
                    )

            # each cell is either:
            # * not part of the loop
            # * the start cell of the loop, and thus has the value 1
            # * some other cell on the loop, and thus must have a connected
            #     cell with a lower value
            s.add(z3.Or(
                v == 0,
                z3.And(start_c == c, start_r == r, v == 1),
                z3.Or(
                    or_constraints
                )
            ))

    if dont_touch_diagonally:
        for r in range(height - 1):
            for c in range(width - 1):
                v0 = grid[r][c]
                v1 = grid[r][c + 1]
                v2 = grid[r + 1][c]
                v3 = grid[r + 1][c + 1]

                # no checker-boards (diagonal touches)
                s.add(z3.Not(z3.And(v0 > 0, v1 == 0, v2 == 0, v3 > 0)))
                s.add(z3.Not(z3.And(v0 == 0, v1 > 0, v2 > 0, v3 == 0)))

    return grid


def pretty_print(z3_solver, grid):
    if z3_solver.check() == z3.sat:
        m = z3_solver.model()
        r = [[m.evaluate(grid[r][c]) for c in range(9)] for r in range(9)]

        def pad(x):
            if x.as_long() > 0:
                return "#"
            else:
                return "."

        for row in r:
            print(" ".join(map(pad, row)))
    else:
        print("No solution")


if __name__ == "__main__":
    s = z3.Solver()
    MUST_INCLUDE = [(0, 0), (4, 0), (8, 0), (7, 2), (0, 4), (8, 4), (1, 5), (0, 8), (3, 8), (5, 8), (7, 8)]

    grid = loop(s, must_include_cells=MUST_INCLUDE)
    #from solver import Solver
    #grid = loop(s, must_include_regions=Solver.REGULAR_9X9_REGIONS)

    pretty_print(s, grid)
