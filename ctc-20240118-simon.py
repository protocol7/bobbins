from solver import Solver, _

# https://www.youtube.com/watch?v=0i6N8UkfwNg

solver = (
    Solver()
    .unique_positive_diagonal()
    .killer_cage([(6, 0), (6, 1)], 11)
    .killer_cage([(5, 1), (5, 2)], 11)
    .killer_cage([(4, 2), (4, 3)], 11)
    .killer_cage([(3, 3), (3, 4)], 11)
    .killer_cage([(2, 4), (2, 5)], 11)
    .killer_cage([(1, 5), (1, 6)], 11)
    .killer_cage([(0, 6), (0, 7)], 11)

    .killer_cage([(7, 2), (8, 2)], 11)
    .killer_cage([(6, 3), (7, 3)], 11)
    .killer_cage([(5, 4), (6, 4)], 10)
    .killer_cage([(4, 5), (5, 5)], 11)
    .killer_cage([(3, 6), (4, 6)], 11)
    .killer_cage([(2, 7), (3, 7)], 11)
    .killer_cage([(1, 8), (2, 8)], 11)
    .black_kropkis([
        [(2, 1), (3, 1)],
        [(4, 7), (4, 8)],
    ])
    .white_kropkis([
        [(0, 3), (0, 4)],
        [(6, 7), (7, 7)],
    ])
)

solution = solver.solve()

Solver.pretty_print(solution)
