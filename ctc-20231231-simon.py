from solver import Solver
from collections import defaultdict
from itertools import permutations
import z3

# https://www.youtube.com/watch?v=dtdF-ncUOS4


CAGES = [
    [(1, 0)],
    [(0, 0), (0, 1)],
    [(2, 0), (3, 0)],
    [(4, 0), (5, 0), (6, 0), (7, 0), (6, 1), (7, 1), (8, 1), (8, 2)],
    [(3, 1), (4, 1), (5, 1)],
    [(0, 2), (1, 2), (2, 2)],
    [(3, 2), (4, 2), (3, 3), (4, 3)],
    [(5, 2), (5, 3), (5, 4)],
    [(6, 2), (7, 2)],
    [(0, 3), (0, 4), (0, 5), (0, 6), (1, 6), (0, 7), (1, 7), (1, 8)],
    [(2, 3), (2, 4), (2, 5)],
    [(6, 3), (7, 3), (6, 4), (7, 4), (8, 4), (7, 5), (8, 5)],
    [(3, 4)],
    [(4, 5), (4, 6)],
    [(6, 5), (6, 6), (5, 6)],
    [(3, 6), (3, 7)],
    [(7, 6), (8, 6), (6, 7), (7, 7)],
    [(5, 7)],
    [(2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8)],
]


def cages(s, vars):

    ks = []
    for i in range(len(CAGES)):
        v = z3.Int("k_%s" % i)

        s.add(v > 0, v <= 45)
        s.add(v % 10 != 0)

        ks.append(v)

    # add killer cage constraints
    for i, (cage, k) in enumerate(zip(CAGES, ks)):
        # digits in the cage must be unique
        s.add(z3.Distinct([vars[r][c] for c, r in cage]))

        s.add(k == z3.Sum([vars[r][c] for c, r in cage]))

    # circles
    for d in range(1, 10):
        sum = z3.Sum([z3.If(k % 10 == d, 1, 0) for k in ks])
        sum_tens = z3.Sum([z3.If(k / 10 == d, 1, 0) for k in ks])
        s.add(z3.Or(sum + sum_tens == 0, sum + sum_tens == d))

    # composition of cages of the same size must be unique
    # first group by size
    by_size = defaultdict(list)
    for cage in CAGES:
        by_size[len(cage)].append(cage)

    # for each size group of cages, make sure they are unique by checking
    # every combination
    for cages in by_size.values():
        for i, cage0 in enumerate(cages):
            for cage1 in cages[i+1:]:
                for perm in permutations(cage1):
                    not_and_constraints = []
                    for (c0, r0), (c1, r1) in zip(cage0, perm):
                        v0 = vars[r0][c0]
                        v1 = vars[r1][c1]

                        not_and_constraints.append(v0 == v1)

                    s.add(z3.Not(z3.And(not_and_constraints)))


s = (
    Solver(Solver.EMPTY)
    .thermo([(7, 1), (8, 0), (7, 0), (6, 0)])
    .thermo([(6, 7), (7, 7)])

    .extra_constraint(cages)

)

solution = s.solve()

Solver.pretty_print(solution)
