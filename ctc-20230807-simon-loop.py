from solver import Solver
from loops import loop, pretty_print
from utils import orthogonal
import z3

# https://www.youtube.com/watch?v=ndxTwCxbFOo

solver = Solver()
loop_grid = None
z3_solver = None


def loops(s, vars):
    global loop_grid, z3_solver

    z3_solver = s

    # cells will be > 0 if part of the loop
    loop_grid = loop(s, must_include_regions=Solver.REGULAR_9X9_REGIONS, dont_touch_diagonally=False)

    for r in range(9):
        for c in range(9):
            v = vars[r][c]
            l = loop_grid[r][c]

            for nc, nr in orthogonal(vars, c, r):
                nv = vars[nr][nc]
                nl = loop_grid[nr][nc]

                constraint = z3.Or(
                    l == 0,  # this is not loop
                    nl == 0,  # neighbour is not loop
                    z3.And(
                        l > 0,
                        nl > 0,
                        z3.Abs(nv - v) >= 5
                    )
                )
                s.add(constraint)

ks = [z3.Int("k_%s" % i) for i in range(11)]

CAGES = [
    ([(3, 0), (4, 0)], ks[0]),
    ([(8, 0), (8, 1)], ks[1]),
    ([(2, 1), (2, 2)], ks[2]),
    ([(0, 2), (1, 2)], ks[3]),
    ([(2, 3), (2, 4)], ks[4]),
    ([(4, 3), (5, 3)], ks[5]),
    ([(4, 5), (5, 5)], ks[6]),
    ([(0, 6), (1, 6)], ks[7]),  # 6
    ([(4, 6), (4, 7)], ks[8]),
    ([(5, 6), (6, 6)], ks[9]),
    ([(6, 8), (7, 8)], ks[10]),
]


def cage_pointers(s, vars):
    for k in ks:
        if k == ks[7]:
            s.add(k == 6)
        else:
            s.add(k != 6)

    for cage, sum in CAGES:
        (c0, r0), (c1, r1) = cage

        vr = vars[r0][c0]
        vc = vars[r1][c1]

        for r, row in enumerate(vars):
            for c, v in enumerate(row):
                s.add(z3.Or(
                    vr != r + 1,
                    vc != c + 1,
                    z3.And(vr == r + 1, vc == c + 1, v == sum, loop_grid[r][c] > 0)
                ))


for cage, sum in CAGES:
    solver.killer_cage(cage, sum)

solver.extra_constraint(loops)
solver.extra_constraint(cage_pointers)

solution = solver.solve()

Solver.pretty_print(solution)

print()

# print the loop as well
pretty_print(z3_solver, loop_grid)

