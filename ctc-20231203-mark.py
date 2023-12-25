from solver import Solver

# https://www.youtube.com/watch?v=fIgzzwWzNSA

s = (
    Solver(Solver.EMPTY)
    .thermo([(2, 8), (2, 7), (2, 6), (2, 5)])
    .thermo([(3, 5), (4, 5), (5, 5), (6, 5)])
    .thermo([(3, 5), (3, 6), (3, 7), (3, 8)])
    .whisper_lines(
        [
            [(0, 2), (1, 1)],
            [(1, 2), (2, 3)],
            [(2, 2), (3, 2)],
            [(5, 1), (5, 2)],
            [(6, 1), (6, 2), (7, 2), (8, 2)],
            [(4, 3), (5, 3)],
            [(2, 8), (1, 7), (1, 6), (1, 5), (1, 4), (2, 4), (3, 4), (3, 5)],
            [(5, 4), (5, 5), (5, 6)],
            [(7, 4), (8, 5)],
            [(6, 7), (7, 7)],
            [(2, 6), (3, 6)],
        ]
    )
)
solution = s.solve()

Solver.pretty_print(solution)
