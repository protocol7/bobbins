from solver import Solver

# https://www.youtube.com/watch?v=ZorNxTzwEBc

s = (
    Solver(Solver.EMPTY)
    .killer_cage([(3, 1), (2, 1), (1, 1), (1, 2), (1, 3)], 21)
    .killer_cage([(1, 5), (1, 6), (1, 7), (2, 7), (3, 7)], 21)
    .killer_cage([(5, 7), (6, 7), (7, 7), (7, 6), (7, 5)], 20)
    .killer_cage([(5, 1), (6, 1), (7, 1), (7, 2), (7, 3)], 19)
    .whisper_lines([
        ((0, 1), (0, 2), (0, 3)),
        ((3, 1), (2, 1), (1, 1), (1, 2)),
        ((6, 1), (7, 1), (7, 2), (7, 3)),
        ((8, 1), (8, 2), (8, 3)),
        ((1, 5), (1, 6), (1, 7), (2, 7)),
        ((5, 7), (6, 7), (7, 7), (7, 6)),

        ((3, 5), (2, 4), (3, 3), (4, 2), (5, 3), (6, 4), (5, 5)),
    ])
)
solution = s.solve()

Solver.pretty_print(solution)
