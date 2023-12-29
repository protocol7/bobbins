from solver import Solver, _

# https://www.youtube.com/watch?v=nH3vat8z9uM

given = (
    (_, _, _, _, 1, _, _, _, _),
    (_, 5, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (6, _, _, _, _, _, _, _, 9),
    (_, _, _, _, _, _, _, _, _),
    (_, _, 3, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, 3, _),
    (_, _, _, _, 3, _, _, _, _),
)


s = (
    Solver(given)
    .whisper_lines([
        [(2, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0), (6, 0), (7, 1), (7, 2),
         (6, 3), (5, 4), (5, 5), (5, 6), (4, 7), (3, 6)],
        [(0, 7), (0, 6), (1, 6), (2, 7), (2, 8), (1, 8)],
        [(4, 3), (5, 3), (6, 2)],
        [(5, 8), (6, 7), (6, 6), (7, 6), (8, 5), (7, 4)],
    ])
)
solution = s.solve()

Solver.pretty_print(solution)