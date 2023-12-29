from solver import Solver

# https://www.youtube.com/watch?v=9myLUpi3zXc

given = (
    (4, 0, 0, 0, 0, 0, 0, 0, 7),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 5, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
)


def anti_knight_ten(s, cells):
    for r in range(9):
        for c in range(9):
            for dc, dr in ((-1, -2), (1, -2), (2, -1), (2, 1), (1, 2), (-1, 2), (-2, 1), (-2, -1), ):
                cc = c + dc
                rr = r + dr

                if cc >= 0 and rr >= 0 and cc < 9 and rr < 9:
                    s.add(cells[r][c] + cells[rr][cc] != 10)


s = (
    Solver(given)
    .unique_negative_diagonal()
    .unique_positive_diagonal()
    .thermo([(2, 2), (2, 1), (1, 2), (0, 2), (1, 1)])
    .thermo([(6, 2), (6, 1), (7, 2), (8, 2), (7, 1), (6, 0)])
    .thermo([(1, 6), (2, 7), (1, 7), (0, 7), (1, 8)])
    .arrow([(3, 1), (3, 2), (4, 1), (5, 1)])
    .extra_constraint(anti_knight_ten)
)

solution = s.solve()

Solver.pretty_print(solution)
