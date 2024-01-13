from solver import Solver
import z3
from utils import z3_count

# https://www.youtube.com/watch?v=XySonxfLEpI


def tree_leafs(s, vars, multipliers):
    TREE_LEAFS = [
        [(0, 4), (1, 4), (2, 5), (0, 6)],
        [(1, 0), (2, 0), (3, 1), (1, 2)],
        [(3, 2), (4, 2), (5, 3), (3, 4)],
        [(6, 1), (7, 1), (8, 2), (6, 3)],
    ]

    # trees have doublers
    for leafs in TREE_LEAFS:
        vs = [multipliers[r][c] for c, r in leafs]
        s.add(z3_count(lambda v: v == 2, vs) == 1)


REGION_SUMS = [
    [[(6, 1), (7, 1), (7, 2)], [(8, 2)], [(6, 3), (7, 3), (7, 4), (7, 5)]],
    [[(0, 4), (1, 4), (1, 5)], [(2, 5)], [(0, 6), (1, 6), (1, 7), (1, 8)]],
]


def doubler_region_sums(s, vars, multipliers):
    for sums in REGION_SUMS:
        vss = []
        for sum in sums:
            vs = [vars[r][c] * multipliers[r][c] for c, r in sum]
            vss.append(vs)

        for vs0, vs1 in zip(vss, vss[1:]):
            s.add(z3.Sum(vs0) == z3.Sum(vs1))


solver = (
    Solver()
    .multipliers(2)
    .thermo([(2, 4), (2, 3), (1, 2)])
    .thermo([(2, 4), (2, 3), (2, 2), (3, 1)])
    .thermo([(2, 4), (2, 3), (2, 2), (2, 1), (2, 0)])
    .thermo([(2, 4), (2, 3), (2, 2), (2, 1), (1, 0)])
    .renban_lines([[(3, 2), (4, 2), (4, 3), (5, 3), (3, 4), (4, 4), (4, 5), (4, 6)]])
    .killer_cage([(0, 0), (1, 0), (2, 0)], 13, unique=False)
    .killer_cage([(6, 0), (7, 0), (8, 0)], 16, unique=False)
    .killer_cage([(1, 1), (2, 1), (3, 1)], 22, unique=False)
    .killer_cage([(5, 1), (6, 1), (7, 1)], 16, unique=False)
    .killer_cage([(5, 3), (6, 3)], 16, unique=False)
    .killer_cage([(0, 5), (1, 5)], 11, unique=False)
    .killer_cage([(6, 5), (7, 5)], 9, unique=False)
    .killer_cage([(0, 6), (0, 7)], 11, unique=False)
    .killer_cage([(8, 6), (8, 7)], 11, unique=False)
    .killer_cage([(1, 8), (2, 8)], 17, unique=False)
    .killer_cage([(6, 8), (7, 8)], 17, unique=False)
    .extra_constraint(tree_leafs, with_multipliers=True)
    .extra_constraint(doubler_region_sums, with_multipliers=True)
)

solution = solver.solve()

if solution is None:
    print("No solution")
else:
    Solver.pretty_print(solution)
