from solver import Solver, _
import z3
from utils import z3_count, orthogonal
from regions import regions, pretty_print

# https://www.youtube.com/watch?v=Zpc-km_WLUg

GIVEN = (
    (_, _, _, _, _, _, _, _, 8),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)

QUADS = [
    [(0, 0), 3],
    [(1, 0), None],
    [(5, 0), 4],
    [(2, 2), None],
    [(4, 2), 0],
    [(5, 2), None],
    [(7, 2), 3],
    [(0, 3), 1],
    [(7, 3), 2],
    [(4, 4), 1],
    [(5, 4), 3],
    [(7, 5), 2],
    [(0, 6), 0],
    [(5, 6), 3],
    [(7, 6), 1],
    [(2, 7), 3],
    [(7, 7), 3],
]

z3_solver = None
unshaded_grid = None


def circles(s, vars):
    global z3_solver, unshaded_grid

    z3_solver = s

    unshaded_grid = regions(s, [None])[0]

    for (c, r), v in QUADS:
        if v is None:
            v = z3.Int(f"v{c}{r}")
            s.add(v >= 0, v <= 4)

        vs = [vars[r][c], vars[r][c+1], vars[r+1][c], vars[r+1][c+1]]
        us = [unshaded_grid[r][c], unshaded_grid[r][c+1], unshaded_grid[r+1][c], unshaded_grid[r+1][c+1]]

        s.add(z3.Or([vv == v for vv in vs]))

        s.add(z3_count(lambda rr: rr > 0, us) == 4 - v)

    for r in range(9):
        for c in range(9):
            v0 = vars[r][c]
            r0 = unshaded_grid[r][c]

            for nc, nr in orthogonal(vars, c, r):
                v1 = vars[nr][nc]
                r1 = unshaded_grid[nr][nc]

                s.add(z3.Or(
                    r0 == 0,  # this is shaded
                    r1 == 0,  # or neighbor is shaded
                    z3.Abs(v1 - v0) >= 5,
                ))


solver = (
    Solver(GIVEN)
    .digits(list(range(9)))
    .extra_constraint(circles)
)

solution = solver.solve()

Solver.pretty_print(solution)

print()
print(solution.unique())
print()


pretty_print(z3_solver, unshaded_grid)
