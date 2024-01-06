from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=8swp3pYKkYM

DIAGONALS = [
    ([(2, 0), (1, 1), (0, 2)], 15),
    ([(3, 8), (4, 7), (5, 6), (6, 5), (7, 4), (8, 3)], 19),
    ([(5, 8), (6, 7), (7, 6), (8, 5)], 22),
    ([(5, 8), (4, 7), (3, 6), (2, 5), (1, 4), (0, 3)], 22),

    ([(8, 7), (7, 6), (6, 5), (5, 4), (4, 3), (3, 2), (2, 1), (1, 0)], 35),
]

s = (
    Solver(Solver.EMPTY)
    .v((1, 1), (1, 2))
    .v((4, 1), (5, 1))
    .v((8, 2), (8, 3))

    .sandwhiches([(8, 35)], [(2, 19), (3, 15), (4, 22), (6, 22)])
)

for diagonal, sum in DIAGONALS:
    s.little_killer(diagonal, sum)


def look_and_tell(s, vars):
    for diagonal, sum in DIAGONALS:
        a = sum // 10
        b = sum % 10

        count = z3.Sum([z3.If(vars[r][c] == b, 1, 0) for c, r in diagonal])
        s.add(count == a)


s.extra_constraint(look_and_tell)

solution = s.solve()

Solver.pretty_print(solution)
