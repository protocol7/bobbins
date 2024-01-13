from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=yIM8zjcfC3M

given = (
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, 2, _, _, _, _, _),
    (_, _, _, _, _, 1, _, _, _),
    (_, _, _, _, 3, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
    (_, _, _, _, _, _, _, _, _),
)

sum0 = z3.Int("sum0")
sum1 = z3.Int("sum1")


def outside_renban(s, vars):
    s.add(z3.Abs(vars[8][4] - sum0) == 1)


def outside_region_sum(s, vars):
    s.add(vars[6][8] == sum1)


solver = (
    Solver(given)
    .xsums([
        [(8, 7), sum1]
    ], [
        [(1, 0), 22],
        [(5, 0), 16],
        [(5, 8), sum0],
    ])
    .killer_cage([(0, 0), (1, 0), (2, 0)], 13)
    .killer_cage([(6, 0), (7, 0), (8, 0)], 16)
    .killer_cage([(5, 1), (6, 1)], 16)
    .killer_cage([(0, 3), (1, 3)], 11)
    .killer_cage([(6, 3), (7, 3)], 9)
    .killer_cage([(0, 4), (0, 5)], 11)
    .killer_cage([(7, 4), (7, 5)], 11)
    .killer_cage([(1, 6), (2, 6)], 17)
    .killer_cage([(5, 7), (6, 7), (7, 7)], 17)

    .thermo([(2, 2), (2, 1), (2, 0)])
    .thermo([(5, 6), (4, 7)])
    .thermo([(7, 5), (6, 6)])
    .thermo([(5, 8), (6, 7)])

    .renban_lines([
        [(4, 2), (4, 3), (4, 4)],
        [(7, 6), (6, 7)],
        [(4, 7), (3, 8)],
        [(7, 7), (6, 8)],
        [(8, 7), (7, 8)],
    ])
    .extra_constraint(outside_renban)
    .region_sum_line([
        [(7, 1), (7, 2), (7, 3)],
        [(1, 4), (1, 5), (1, 6)],
        [(6, 5), (5, 6)],
        [(8, 5), (7, 6)],
        [(6, 6), (5, 7)],
    ])
    .extra_constraint(outside_region_sum)
)

solution = solver.solve()

Solver.pretty_print(solution)
