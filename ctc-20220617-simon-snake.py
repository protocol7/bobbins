from solver import Solver, _
from snake import snake, pretty_print
import z3
from utils import adjacent_with_cell, z3_count, orthogonal

# https://www.youtube.com/watch?v=ZU1xe6q4dpM

z3_solver = None
snake_grid = None

given = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, 4, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)

CIRCLES = [(4, 2), (7, 2), (1, 4)]


def _snakes(s, vars):
    global z3_solver, snake_grid

    z3_solver = s
    # Snake must visit each circle.

    snake_grid, (start_c, start_r), (end_c, end_r) = snake(s, must_include_cells=CIRCLES, dont_touch_diagonally=False)
    s.add(start_c == 0, start_r == 8)
    s.add(end_c == 6, end_r == 8)

    # A digit in a circle is equal to the number of snake cells in the (up to) 9 surrounding cells, including itself.
    for c, r in CIRCLES:
        ns = [snake_grid[ar][ac] for ac, ar in adjacent_with_cell(vars, c, r)]

        count = z3_count(lambda s: s > 0, ns)

        s.add(count == vars[r][c])

    for r in range(9):
        for c in range(9):
            v = vars[r][c]
            ss = snake_grid[r][c]
            nss = [snake_grid[ar][ac] for ac, ar in orthogonal(vars, c, r)]
            vss = [vars[ar][ac] for ac, ar in orthogonal(vars, c, r)]

            # Adjacent snake cells must differ by at least 5.
            for nv, ns in zip(vss, nss):
                s.add(z3.Or(
                    ss == 0,  # this is not snake
                    ns == 0,  # neighbour is not snake
                    z3.And(ns > 0, z3.Abs(v - nv) >= 5)
                ))


solver = (
    Solver(given)
    .extra_constraint(_snakes)
)

solution = solver.solve()

Solver.pretty_print(solution)

print()
pretty_print(z3_solver, snake_grid)
