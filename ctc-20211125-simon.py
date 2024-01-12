from solver import Solver
import z3

# https://www.youtube.com/watch?v=GWu9pM4JtpQ


def anti_anti_knight(s, vars):
    for r in range(9):
        for c in range(9):
            v = vars[r][c]

            ks = []
            for dc, dr in ((-1, -2), (1, -2), (2, -1), (2, 1), (1, 2), (-1, 2), (-2, 1), (-2, -1), ):
                kc = c + dc
                kr = r + dr

                if kc < 0 or kr < 0 or kc >= 9 or kr >= 9:
                    continue

                ks.append(vars[kr][kc])

            s.add(
                z3.Implies(
                    v % 2 == 0,
                    z3.Or([k == v for k in ks]))
                )


solver = (
    Solver()
    .quadruple((0, 0), [2, 3])
    .quadruple((1, 1), [5])
    .quadruple((2, 2), [8, 9])
    .quadruple((7, 0), [3, 4])
    .quadruple((6, 1), [8, 9])
    .quadruple((5, 2), [5, 6])
    .quadruple((2, 5), [4, 5])
    .quadruple((1, 6), [1])
    .quadruple((0, 7), [6, 7])
    .quadruple((5, 5), [1, 2])
    .quadruple((6, 6), [2, 5])
    .quadruple((7, 7), [8])
    .extra_constraint(anti_anti_knight)
)

solution = solver.solve()

Solver.pretty_print(solution)
