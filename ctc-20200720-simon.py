from solver import Solver
import z3

# https://www.youtube.com/watch?v=Bv0LcQJ3pp4

ks = [z3.Int("thirteen_%s" % i) for i in range(19)]


def thirteen(s, vars):
    for k in ks:
        s.add(z3.Or(k == 13, k == 26, k == 39))


s = (
    Solver(Solver.EMPTY)
    .killer_cage([(0, 0), (1, 0), (2, 0), (2, 1)], ks[0])
    .killer_cage([(3, 0), (4, 0), (5, 0), (4, 1), (5, 1), (5, 2)], ks[1])
    .killer_cage([(6, 0), (7, 0), (8, 0), (7, 1)], ks[2])

    .killer_cage([(0, 1), (0, 2), (0, 3), (0, 4)], ks[3])
    .killer_cage([(1, 1), (1, 2), (2, 2)], ks[4])
    .killer_cage([(6, 1), (6, 2)], ks[5])

    .killer_cage([(7, 2), (8, 2), (7, 3)], ks[6])
    .killer_cage([(1, 3), (2, 3), (1, 4), (2, 4), (1, 5)], ks[7])
    .killer_cage([(3, 3), (4, 3), (5, 3), (3, 4), (4, 4), (5, 4)], ks[8])

    .killer_cage([(6, 3), (6, 4), (6, 5), (5, 5)], ks[9])
    .killer_cage([(0, 5), (0, 6), (0, 7), (0, 8)], ks[10])
    .killer_cage([(2, 5), (3, 5)], ks[11])

    .killer_cage([(4, 5), (4, 6), (5, 6)], ks[12])
    .killer_cage([(7, 5), (8, 5), (6, 6), (7, 6)], ks[13])
    .killer_cage([(1, 6), (1, 7)], ks[14])

    .killer_cage([(2, 6), (2, 7), (2, 8), (1, 8)], ks[15])
    .killer_cage([(3, 6), (3, 7), (4, 7), (4, 8)], ks[16])

    .killer_cage([(8, 6), (8, 7), (8, 8), (7, 8), (6, 8)], ks[17])
    .killer_cage([(5, 7), (5, 8)], ks[18])

    .extra_constraint(thirteen)
)

solution = s.solve()

Solver.pretty_print(solution)
