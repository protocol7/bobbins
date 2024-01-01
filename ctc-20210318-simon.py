from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=u0FhERdlWFc

vs = []
for i in range(26):
    vs.append(z3.Int("cage_%s" % i))


def custom(s, vars):
    for i, v in enumerate(vs):
        s.add(v > 0, v < 45)

        for j, vv in enumerate(vs):
            if i == j:
                continue

            s.add(v != vv)

    #s.add(z3.Distinct(vs))

s = (
    Solver(Solver.EMPTY)
    .smaller_than((4, 3), (3, 3))

    .killer_cage([(1, 0), (0, 0), (0, 1), (0, 2)], vs[0])
    .killer_cage([(2, 0), (3, 0), (3, 1)], vs[1])
    .killer_cage([(4, 0), (4, 1)], vs[2])
    .killer_cage([(5, 0), (5, 1), (6, 1)], vs[3])
    .killer_cage([(6, 0), (7, 0), (8, 0), (8, 1)], vs[4])

    .killer_cage([(2, 1), (1, 1), (1, 2)], vs[5])

    .killer_cage([(2, 2), (2, 3), (1, 3)], vs[6])
    # x
    .killer_cage([(3, 2), (4, 2), (5, 2)], vs[7])
    .killer_cage([(6, 2), (6, 3), (6, 4)], vs[8])
    .killer_cage([(8, 2), (7, 2), (7, 3)], vs[9])

    .killer_cage([(0, 3), (0, 4), (0, 5)], vs[10])
    .killer_cage([(4, 3), (3, 3), (3, 4)], vs[11])

    .killer_cage([(5, 3), (5, 4), (4, 4), (5, 5)], vs[12])
    .killer_cage([(8, 3), (8, 4), (8, 5)], vs[13])

    .killer_cage([(1, 4), (2, 4)], vs[14])
    .killer_cage([(7, 4), (7, 5)], vs[15])

    .killer_cage([(1, 5), (1, 6), (2, 6)], vs[16])
    .killer_cage([(2, 5), (3, 5), (4, 5)], vs[17])
    .killer_cage([(6, 5), (6, 6), (7, 6)], vs[18])

    .killer_cage([(0, 6), (0, 7), (0, 8)], vs[19])
    .killer_cage([(3, 6), (3, 7), (2, 7)], vs[20])
    .killer_cage([(4, 6), (4, 7), (4, 8)], vs[21])
    .killer_cage([(5, 6), (5, 7), (5, 8)], vs[22])
    .killer_cage([(8, 6), (8, 7), (8, 8), (7, 8)], vs[23])

    .killer_cage([(7, 7), (6, 7), (6, 8)], vs[24])
    .killer_cage([(1, 8), (2, 8), (3, 8)], vs[25])

    .little_killer([(2, 8), (3, 7), (4, 6), (5, 5), (6, 4), (7, 3), (8, 2)], 2 * vs[7])

    .extra_constraint(custom)

)
solution = s.solve()

Solver.pretty_print(solution)
