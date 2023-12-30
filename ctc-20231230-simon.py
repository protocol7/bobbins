from solver import Solver

# https://www.youtube.com/watch?v=4K_UvuHhdWw


def rotate_10(s, vars):
    for r in range(9):
        for c in range(9):
            if r in (0, 8) or c in (0, 8):
                s.add(vars[r][c] + vars[8 - r][8 - c] == 10)


s = (
    Solver(Solver.EMPTY)
    .killer_cage([(0, 1), (1, 1)], 10)
    .killer_cage([(0, 2), (1, 2)], 9)
    .killer_cage([(2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (6, 0)], 29)
    .killer_cage([(7, 0), (8, 0), (8, 1), (8, 2)], 19)
    .killer_cage([(5, 2), (6, 2)], 10)
    .killer_cage([(7, 2), (7, 3), (7, 4), (8, 4), (7, 5)], 27)
    .killer_cage([(1, 3), (1, 4), (0, 4), (1, 5), (1, 6)], 27)
    .killer_cage([(2, 3), (3, 3)], 12)
    .killer_cage([(0, 5), (0, 6)], 13)
    .killer_cage([(2, 5), (2, 6)], 9)
    .killer_cage([(4, 5), (5, 5), (5, 6), (6, 6)], 14)
    .killer_cage([(2, 8), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7)], 28)
    .killer_cage([(3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (7, 7), (7, 6), (8, 6)])

    .extra_constraint(rotate_10)
)

solution = s.solve()

Solver.pretty_print(solution)
