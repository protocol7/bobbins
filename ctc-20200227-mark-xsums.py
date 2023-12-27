from solver import Solver

# https://www.youtube.com/watch?v=fnCzYnsC4Ow


s = (
    Solver(Solver.EMPTY)
    .xsums([
        ((0, 1), 8),
        ((0, 3), 17),
        ((0, 5), 30),
        ((0, 7), 28),

        ((8, 1), 8),
        ((8, 3), 17),
        ((8, 5), 30),
        ((8, 7), 28),
    ], [
        ((1, 0), 27),
        ((3, 0), 11),
        ((5, 0), 21),
        ((6, 0), 16),

        ((1, 8), 27),
        ((3, 8), 11),
        ((6, 8), 16),
    ])
)
solution = s.solve()

Solver.pretty_print(solution)
