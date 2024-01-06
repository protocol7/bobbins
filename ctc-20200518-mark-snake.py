from solver import Solver, _
from snake import snake, pretty_print
import z3
from utils import adjacent_with_cell, z3_count

# https://www.youtube.com/watch?v=IDp1EjkerR0

z3_solver = None
snake_grid0 = None
snake_grid1 = None

given = (
    (9, _, _, _, _, 8, _, 7, _),
    (_, _, _, _, _, _, 4, _, _),
    (_, _, _, _, _, 1, _, 5, _),
    (_, _, _, 6, _, _, _, _, _),
    (_, _, _, _, 9, _, _, _, _),
    (1, _, 2, _, _, 3, _, _, _),
    (_, 3, _, _, _, _, _, _, _),
    (4, _, 5, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, 8),
)


def _snakes(s, vars):
    global z3_solver, snake_grid0, snake_grid1

    z3_solver = s
    snake_grid0, (start_c, start_r), (end_c, end_r) = snake(s)
    s.add(start_c == 0, start_r == 0)
    s.add(end_c == 5, end_r == 5)

    snake_grid1, (start_c, start_r), (end_c, end_r) = snake(s)
    s.add(start_c == 3, start_r == 3)
    s.add(end_c == 8, end_r == 8)

    for r in range(9):
        for c in range(9):
            s0 = snake_grid0[r][c]
            s1 = snake_grid1[r][c]
            v = vars[r][c]

            # snake 0 is all odd cells
            s.add(z3.Or(
                s0 == 0,
                v % 2 == 1
            ))

            # snake 1 is all even cells
            s.add(z3.Or(
                s1 == 0,
                v % 2 == 0
            ))

            # snakes can not touch
            ns0 = [snake_grid0[nr][nc] for nc, nr in adjacent_with_cell(vars, c, r)]
            ns1 = [snake_grid1[nr][nc] for nc, nr in adjacent_with_cell(vars, c, r)]

            count0 = z3_count(lambda s: s > 0, ns0)
            count1 = z3_count(lambda s: s > 0, ns1)

            s.add(z3.Or(
                z3.And(s0 == 0, s1 == 0),  # not either snake
                z3.And(s0 > 0, count1 == 0),
                z3.And(s1 > 0, count0 == 0),
            ))


solver = (
    Solver(given)
    .extra_constraint(_snakes)
)

solution = solver.solve()

Solver.pretty_print(solution)

print()
pretty_print(z3_solver, snake_grid0)

print()
pretty_print(z3_solver, snake_grid1)
