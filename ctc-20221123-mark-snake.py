from solver import Solver
from snake import snake, pretty_print
import z3
from utils import adjacent_with_cell, z3_count

# https://www.youtube.com/watch?v=B8mjmYstpMg

EVENS = [
    (7, 0),
    (1, 1), (4, 1),
    (4, 3),
    (3, 4), (6, 4),
    (1, 5),
    (5, 6),
    (0, 7), (3, 7),
]

ODDS = [
    (0, 0), (1, 0), (8, 0),
    (0, 2), (3, 2), (6, 2), (8, 2),
    (4, 4),
    (2, 5),
    (3, 6), (6, 6),
    (4, 7),
]

z3_solver = None
snake_grid = None


def _snake(s, vars):
    global z3_solver, snake_grid

    z3_solver = s
    snake_grid, (start_c, start_r), (end_c, end_r) = snake(s)

    # start end end must be 9
    for r, row in enumerate(vars):
        for c, v in enumerate(row):
            s.add(z3.Or(
                start_c != c,
                start_r != r,
                z3.And(start_c == c, start_r == r, v == 9)
            ))

            s.add(z3.Or(
                end_c != c,
                end_r != r,
                z3.And(end_c == c, end_r == r, v == 9)
            ))

    # odd and even cells must count the number of snake cells surrounding it
    for c, r in ODDS + EVENS:
        ss = [snake_grid[nr][nc] for nc, nr in adjacent_with_cell(vars, c, r)]

        count = z3_count(lambda s: s > 0, ss)
        s.add(vars[r][c] == count)


solver = (
    Solver()
    .odds(ODDS)
    .evens(EVENS)
    .extra_constraint(_snake)
)

solution = solver.solve()

Solver.pretty_print(solution)
print()

pretty_print(z3_solver, snake_grid)
