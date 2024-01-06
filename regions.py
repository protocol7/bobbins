import z3
from utils import orthogonal


def regions(
        s,
        sizes,
        region_widths=None,
        region_heights=None,
        grid_width=9,
        grid_height=9):

    grids = []
    # create one grid per region
    for region_i, size in enumerate(sizes):

        grid = []
        grids.append(grid)

        vs = []
        for r in range(grid_height):
            row = []
            for c in range(grid_width):
                v = z3.Int("region_%s_%s_%s" % (region_i, c, r))

                s.add(z3.Or(v >= 0))

                row.append(v)
                vs.append(v)

            grid.append(row)

        # each region has a start cell, this will have value 1
        start_c = z3.Int("start_c_%s" % region_i)
        start_r = z3.Int("start_r_%s" % region_i)

        # the region must have the configured size
        count = z3.Sum([z3.If(v > 0, 1, 0) for v in vs])
        s.add(count == size)

        if region_widths:
            # the region must have a certain width, check each row for either
            # 0 of width cells in the region
            width = region_widths[region_i]
            for row in grid:
                count = z3.Sum([z3.If(v > 0, 1, 0) for v in row])
                s.add(z3.Or(count == width, count == 0))

        if region_heights:
            # do the same for heights
            height = region_heights[region_i]
            for col in map(list, zip(*grid)):
                count = z3.Sum([z3.If(v > 0, 1, 0) for v in col])
                s.add(z3.Or(count == height, count == 0))

        for r, row in enumerate(grid):
            for c, v in enumerate(row):

                ns = [grid[nr][nc] for nc, nr in orthogonal(grid, c, r)]

                # each part (except for a starting point) should be connected
                # with another part that has a natural number less than its
                # number
                #
                # https://www.cs.ru.nl/bachelors-theses/2021/Gerhard_van_der_Knijff___1006946___Solving_and_generating_puzzles_with_a_connectivity_constraint.pdf

                # at least one neighbour must be in the region and have a
                # lower value
                count = z3.Sum([z3.If(z3.And(nv > 0, nv < v), 1, 0) for nv in ns])

                # each cell is either:
                # * not part of the region
                # * the start cell of the region, and thus has the value 1
                # * some other cell on the region, and thus must have a
                #     connected cell with a lower value
                s.add(z3.Or(
                    v == 0,
                    z3.And(start_c == c, start_r == r, v == 1),
                    z3.And(v > 1, count > 0)
                ))

    # regions must not overlap
    for r in range(grid_height):
        for c in range(grid_width):
            vs = [grid[r][c] for grid in grids]

            count = z3.Sum([z3.If(v > 0, 1, 0) for v in vs])
            if sum(sizes) == grid_height * grid_width:
                s.add(count == 1)
            else:
                s.add(z3.Or(count == 1, count == 0))

    return grids


def pretty_print(z3_solver, grid):
    m = z3_solver.model()
    r = [[m[grid[r][c]] for c in range(len(grid[0]))] for r in range(len(grid))]

    def pad(x):
        if x.as_long() > 0:
            return "#"
        else:
            return "."

    for row in r:
        print(" ".join(map(pad, row)))


def pretty_print_grids(z3_solver, grids):
    m = z3_solver.model()

    for r in range(len(grids[0])):
        out_row = []
        for c in range(len(grids[0][0])):
            for i, grid in enumerate(grids):
                v = m[grid[r][c]]

                if v.as_long() > 0:
                    out_row.append(i)
                    break

        print(" ".join(map(str, out_row)))


if __name__ == "__main__":
    s = z3.Solver()

    size = 8

    widths = []
    heights = []
    for i in range(size):
        width = z3.Int("width_%s" % i)
        height = z3.Int("height_%s" % i)
        s.add(z3.Or(
            z3.And(width == 2, height == 4),
            z3.And(width == 4, height == 2)
        ))

        widths.append(width)
        heights.append(height)

    grids = regions(s, sizes=[size] * size, grid_height=size, grid_width=size, region_widths=widths, region_heights=heights)

    if s.check() == z3.sat:
        for grid in grids:
            pretty_print(s, grid)
            print()

        pretty_print_grids(s, grids)
    else:
        print("No solution")
