from solver import Solver, _
import z3
from regions import regions, pretty_print

# https://www.youtube.com/watch?v=dXUzvJNkZBk

# slow

DIGITS = list(range(1, 9))

CIRCLES = [
    (3, 0), (4, 0), (5, 0), (6, 0),
    (4, 1), (5, 1), (6, 1), (7, 1),
    (3, 2), (5, 2),
    (0, 3), (2, 3), (4, 3), (6, 3),
    (1, 4), (4, 4), (5, 4), (6, 4), (7, 4),
    (1, 5), (4, 5), (5, 5), (6, 5), (7, 5),
    (0, 6), (1, 6), (5, 6), (6, 6), (7, 6),
    (0, 7), (3, 7), (4, 7), (5, 7), (6, 7), (7, 7),
]

region_grids = None
z3_solver = None


def _regions(s, vars):
    global region_grids, z3_solver

    z3_solver = s

    widths = []
    heights = []
    for i in range(8):
        width = z3.Int("width_%s" % i)
        height = z3.Int("height_%s" % i)
        s.add(z3.Or(
            z3.And(width == 2, height == 4),
            z3.And(width == 4, height == 2)
        ))

        widths.append(width)
        heights.append(height)

    grids = regions(
        s,
        sizes=[8] * 8,
        grid_width=8,
        grid_height=8,
        region_widths=widths,
        region_heights=heights
        )

    region_grids = grids

    # digits must be unique in each region
    # since Distinct is slow for large sets, we instead check that each digit
    # appears in a region
    vs = [v for row in vars for v in row]
    for grid in grids:
        gs = [v for row in grid for v in row]

        and_constraints = []
        for digit in DIGITS:
            or_constraints = [z3.And(g > 0, v == digit) for v, g in zip(vs, gs)]

            and_constraints.append(z3.Or(or_constraints))

        s.add(z3.And(and_constraints))


solver = (
    Solver(width=8, height=8)
    .digits(DIGITS)
    .regions([])
    .white_kropkis([
        [(0, 2), (0, 3)],
        [(3, 3), (3, 4)],
        [(4, 4), (5, 4)],
        [(7, 4), (7, 5)],
        [(5, 6), (6, 6)],
        [(6, 7), (7, 7)],
    ])
    .circles(CIRCLES)
    .extra_constraint(_regions)
)

solution = solver.solve()

Solver.pretty_print(solution)
print()

for grid in region_grids:
    pretty_print(z3_solver, grid)
    print()
