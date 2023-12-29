from solver import Solver
import z3

# https://www.youtube.com/watch?v=ztKGB9yQfD8

x = z3.Int("x")

s = (
    Solver(Solver.EMPTY)
    .unique_positive_diagonal()
    .xsums([
        [(0, 0), x],
        [(0, 3), x],
        [(0, 7), x],
        [(8, 0), x],
        [(8, 1), x],
    ], [
        [(0, 0), x],
        [(3, 0), x],
        [(7, 0), x],
        [(8, 0), x],

        [(1, 8), x],
        [(4, 8), x],
        [(6, 8), x],
    ])
)
solution = s.solve()

Solver.pretty_print(solution)
