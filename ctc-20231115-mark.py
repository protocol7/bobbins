from solver import Solver

# https://www.youtube.com/watch?v=3KaGJPM-N1I

s = (
    Solver(Solver.EMPTY)
    .unique_negative_diagonal()
    .unique_positive_diagonal()
    .killer_cage([(3, 0), (4, 0), (5, 0)], 23)
    .killer_cage([(3, 2), (4, 2)], 6)
    .killer_cage([(0, 3), (0, 4), (0, 5)], 24)
    .killer_cage([(2, 4), (2, 5)], 7)
    .killer_cage([(6, 3), (6, 4)], 7)
    .killer_cage([(8, 3), (8, 4), (8, 5)], 21)
    .killer_cage([(4, 6), (5, 6)], 8)
    .killer_cage([(3, 8), (4, 8), (5, 8)], 22)
    .white_kropkis([((7, 4), (7, 5))])
    .palindrom_lines([
        [(4, 0), (3, 0), (2, 1), (1, 2), (0, 3)],
        [(0, 4), (0, 5), (1, 6), (2, 7), (3, 8)],
        [(4, 8), (5, 8), (6, 7), (7, 6), (8, 5)],
        [(8, 4), (8, 3), (7, 2), (6, 1), (5, 0)],
        [(3, 2), (2, 3), (2, 4)],
        [(2, 5), (3, 6), (4, 6)],
        [(5, 6), (6, 5), (6, 4)],
        [(6, 3), (5, 2), (4, 2)],
    ])
)
solution = s.solve()

Solver.pretty_print(solution)
