from solver import Solver, _
import z3
from regions import regions, pretty_print

# https://www.youtube.com/watch?v=RibOCs_eQWo

z3_solver = None
grid = None

CAGES = [
    ([(3, 0), (3, 1), (3, 2)], 16),
    ([(4, 0), (4, 1), (4, 2)], 7),
    ([(5, 0), (5, 1)], 6),
    ([(8, 0), (7, 0), (7, 1)], 7),

    ([(0, 1), (0, 2)], 3),
    ([(1, 1), (1, 2), (2, 2)], 8),
    ([(8, 1), (8, 2)], 7),

    ([(0, 3), (1, 3)], 7),
    ([(2, 3), (1, 4), (2, 4), (2, 5)], 8),
    ([(3, 3), (3, 4)], 3),
    ([(4, 3), (5, 3)], 5),
    ([(6, 3), (6, 4), (7, 4), (6, 5)], 7),
    ([(7, 3), (8, 3)], 7),

    ([(4, 4)], 0),
    ([(5, 4), (5, 5)], 4),

    ([(0, 5), (1, 5)], 7),
    ([(3, 5), (4, 5)], 6),
    ([(7, 5), (8, 5)], 7),

    ([(0, 6), (0, 7)], 8),
    ([(4, 6), (4, 7), (4, 8)], 17),
    ([(5, 6), (5, 7), (5, 8)], 16),
    ([(6, 6), (7, 6), (7, 7)], 6),
    ([(8, 6), (8, 7)], 9),
    ([(1, 7), (1, 8), (0, 8)], 14),

    ([(3, 7), (3, 8)], 6),
]


def galaxy(s, vars):
    global z3_solver, grid

    z3_solver = s

    grids = regions(s, [None], grid_width=9, grid_height=9)

    assert len(grids) == 1

    grid = grids[0]

    for r in range(9):
        for c in range(9):
            nr = 8 - r
            nc = 8 - c

            g = grid[r][c]
            ng = grid[nr][nc]

            s.add(
                z3.Or(
                    g == 0,
                    z3.And(g > 0, ng > 0)
                )
            )

    for cage, sum in CAGES:
        vs = [vars[r][c] for c, r in cage]
        gs = [grid[r][c] for c, r in cage]

        s.add(z3.Sum([z3.If(g == 0, v, 0) for v, g in zip(vs, gs)]) == sum)


solver = (
    Solver()
    .extra_constraint(galaxy)
)

solution = solver.solve()

Solver.pretty_print(solution)

print()
pretty_print(z3_solver, grid)
