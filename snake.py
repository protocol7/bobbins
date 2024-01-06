import z3
from utils import orthogonal, z3_count

snakes_counter = 0


def snake(
        s,
        width=9,
        height=9,
        must_include_cells=[],
        must_include_regions=[],
        dont_touch_diagonally=True):

    global snakes_counter

    grid = []
    vs = []
    for r in range(height):
        row = []
        for c in range(width):
            v = z3.Int("snake_%s_%s_%s" % (snakes_counter, c, r))

            s.add(v >= 0)

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

    # start and end cells
    start_c = z3.Int("start_c_%s" % snakes_counter)
    start_r = z3.Int("start_r_%s" % snakes_counter)

    s.add(start_c >= 0, start_c < width)
    s.add(start_r >= 0, start_r < height)

    end_c = z3.Int("end_c_%s" % snakes_counter)
    end_r = z3.Int("end_r_%s" % snakes_counter)

    s.add(end_c >= 0, end_c < width)
    s.add(end_r >= 0, end_r < height)

    # snake must be at least 2 cells long
    gs = [g for row in grid for g in row]
    s.add(z3_count(lambda s: s > 0, gs) >= 2)

    # not a loop
    s.add(z3.Not(z3.And(start_c == end_c, start_r == end_r)))

    for r, row in enumerate(grid):
        for c, v in enumerate(row):

            ns = [grid[nr][nc] for nc, nr in orthogonal(grid, c, r)]

            # all loop cells must have exactly two orthogonal neighbours, or be start or end and only have one
            count = z3.Sum([z3.If(nv > 0, 1, 0) for nv in ns])
            s.add(z3.Or(
                v == 0,
                z3.And(start_c == c, start_r == r, v > 0, count == 1),
                z3.And(end_c == c, end_r == r, v > 0, count == 1),
                z3.And(z3.Not(z3.And(start_c == c, start_r == r)), z3.Not(z3.And(end_c == c, end_r == r)), v > 0, count == 2),
            ))

            # each part (except for a starting point) should be connected with
            # another part that has a natural number less than its number
            #
            # https://www.cs.ru.nl/bachelors-theses/2021/Gerhard_van_der_Knijff___1006946___Solving_and_generating_puzzles_with_a_connectivity_constraint.pdf

            lower_neighbour_count = z3.Sum([z3.If(z3.And(nv > 0, nv < v), 1, 0) for nv in ns])

            # each cell is either:
            # * not part of the loop
            # * the start cell of the loop, and thus has the value 1
            # * some other cell on the loop, and thus must have a connected
            #     cell with a lower value
            s.add(z3.Or(
                v == 0,
                z3.And(start_c == c, start_r == r, v == 1),
                lower_neighbour_count > 0
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

    snakes_counter += 1

    return grid, (start_c, start_r), (end_c, end_r)


def pretty_print(z3_solver, grid):
    m = z3_solver.model()
    r = [[m[grid[r][c]] for c in range(9)] for r in range(9)]

    def pad(x):
        #return str(x).ljust(2)
        if x.as_long() > 0:
            return "#"
        else:
            return "."

    for row in r:
        print(" ".join(map(pad, row)))


if __name__ == "__main__":
    s = z3.Solver()
    #MUST_INCLUDE = [(4, 0), (8, 0), (7, 2), (0, 4), (8, 4), (1, 5), (0, 8), (3, 8), (5, 8), (7, 8)]
    MUST_INCLUDE = [(4, 0), (7, 8), (8, 0)]

    grid, (start_c, start_r), (end_c, end_r) = snake(s, must_include_cells=MUST_INCLUDE)
    #from solver import Solver
    #grid = loop(s, must_include_regions=Solver.REGULAR_9X9_REGIONS)

    if s.check() == z3.sat:
        pretty_print(s, grid)

        m = s.model()
        print(m[start_c], m[start_r])
        print(m[end_c], m[end_r])
    else:
        print("No solution")
