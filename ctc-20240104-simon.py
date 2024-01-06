from solver import Solver
import z3

# https://www.youtube.com/watch?v=TykXTMjfhec

solver = Solver()


CAGES = [
    ([(2, 0), (3, 0), (2, 1)], z3.Q(1, 2)),
    ([(4, 0), (5, 0), (6, 0), (7, 0), (8, 0)], 15),
    ([(0, 2), (1, 2), (0, 3)], z3.Q(1, 2)),
    ([(4, 2), (5, 2), (5, 3), (6, 3)], 10),
    ([(8, 2), (8, 3), (8, 4), (8, 5), (8, 6)], 15),
    ([(1, 3), (2, 3), (3, 3), (1, 4), (3, 4)], 4),
    ([(2, 4), (2, 5), (3, 5)], z3.Q(7, 2)),
    ([(5, 4), (6, 4), (5, 5), (5, 6)], 10),
    ([(6, 5), (6, 6), (7, 6)], z3.Q(5, 2)),
    ([(0, 6), (1, 6), (2, 6), (3, 6), (4, 6)], 14),
    ([(3, 7), (1, 8), (2, 8), (3, 8), (4, 8)], z3.Q(15, 2)),
    ([(6, 7), (6, 8), (5, 8)], z3.Q(5, 2)),
    ([(8, 7), (8, 8), (7, 8)], z3.Q(7, 2)),
]


def divisor_cages(s, vars):
    seen = set()
    for cage, sum in CAGES:
        assert len(set(cage)) == len(cage)
        assert not (set(cage) & seen)

        s.add(z3.Distinct([vars[r][c] for c, r in cage]))

        or_constraints = []
        for c, r in cage:
            rest = [cell for cell in cage if cell != (c, r)]

            v = vars[r][c]

            or_constraints.append(
                z3.ToReal(z3.Sum([vars[r][c] for c, r in rest])) / z3.ToReal(v) == sum
            )

        s.add(z3.Or(or_constraints))


solver.extra_constraint(divisor_cages)

solution = solver.solve()

Solver.pretty_print(solution)
