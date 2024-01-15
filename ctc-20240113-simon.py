from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=0T90bpnvE50

k = []

for i in range(25):
    v = z3.Int("k_%s" % i)
    k.append(v)


def contains_three(s, vars):
    for v in k:
        or_terms = []
        for i in [3, 13, 23, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 43]:
            or_terms.append(v == i)

        s.add(z3.Or(or_terms))


solver = (
    Solver()
    .killer_cage([(0, 0), (0, 1), (0, 2)], k[0])

    .killer_cage([(1, 0), (2, 0)], k[1])
    .killer_cage([(3, 0), (3, 1), (4, 1)], k[2])
    .killer_cage([(4, 0), (5, 0), (5, 1), (5, 2), (6, 0), (7, 0), (7, 1)], k[3])
    .killer_cage([(8, 0), (8, 1), (8, 2)], k[4])
    .killer_cage([(1, 1), (1, 2), (1, 3)], k[5])
    .killer_cage([(2, 1), (2, 2)], k[6])
    .killer_cage([(6, 1), (6, 2), (7, 2)], k[7])
    .killer_cage([(3, 2), (4, 2)], k[8])
    .killer_cage([(0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8)], k[9])
    .killer_cage([(2, 3), (3, 3)], k[10])
    .killer_cage([(4, 3), (5, 3)], k[11])
    .killer_cage([(6, 3), (7, 3), (8, 3)], k[12])
    .killer_cage([(1, 4), (2, 4), (3, 4), (4, 4), (5, 4), (6, 4), (7, 4), (8, 4)], k[13])

    .killer_cage([(1, 5), (1, 6)], k[14])
    .killer_cage([(2, 5), (2, 6), (2, 7), (1, 7), (1, 8)], k[15])
    .killer_cage([(3, 5), (4, 5), (4, 6)], k[16])
    .killer_cage([(5, 5), (6, 5), (7, 5), (8, 5)], k[17])
    .killer_cage([(3, 6), (3, 7), (4, 7)], k[18])
    .killer_cage([(5, 6), (5, 7)], k[19])
    .killer_cage([(6, 6), (6, 7)], k[20])
    .killer_cage([(7, 6), (8, 6)], k[21])
    .killer_cage([(7, 7), (8, 7)], k[22])
    .killer_cage([(2, 8), (3, 8), (4, 8)], k[23])
    .killer_cage([(5, 8), (6, 8), (7, 8), (8, 8)], k[24])
    .extra_constraint(contains_three)
)

solution = solver.solve()

Solver.pretty_print(solution)
