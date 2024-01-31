from solver import Solver
import z3
from utils import orthogonal, z3_count

# https://www.youtube.com/watch?v=ioh5b30VCKw

LINES = [
    [(2, 0), (2, 1), (1, 1)],
    [(6, 2), (5, 1), (6, 0), (7, 1), (6, 1)],
    [(1, 3), (2, 2), (2, 3), (1, 4), (2, 4)],
    [(4, 2), (5, 3), (6, 3)],
    [(4, 4), (5, 4), (5, 5)],
    [(7, 4), (8, 4), (8, 5)],
    [(7, 6), (6, 7), (7, 7)],
]


def fib_lines(s, vars):
    for line in LINES:
        def fib(vs):
            and_terms = []

            and_terms.append(vs[1] - vs[0] == 1)
            for v0, v1, v2 in zip(vs, vs[1:], vs[2:]):
                and_terms.append(v0 + v1 == v2)

            return z3.And(and_terms)

        vs = [vars[r][c] for c, r in line]

        s.add(z3.Or(
            fib(vs),
            fib(vs[::-1]),
        ))


def twos_threes(s, vars):
    for r in range(9):
        for c in range(9):
            v = vars[r][c]

            ns = [vars[nr][nc] for nc, nr in orthogonal(vars, c, r)]

            def odd(n):
                return z3.Or(n == 1, n == 3, n == 5, n == 7, n == 9)

            def even(n):
                return z3.Or(n == 2, n == 4, n == 6, n == 8)

            s.add(z3.Or(
                v != 2,
                z3_count(odd, ns) == 2,
            ))

            s.add(z3.Or(
                v != 3,
                z3_count(even, ns) == 3,
            ))


solver = (
    Solver()
    .extra_constraint(twos_threes)
    .extra_constraint(fib_lines)
)


solution = solver.solve()

Solver.pretty_print(solution)
