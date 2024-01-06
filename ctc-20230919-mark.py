from solver import Solver
import z3

# https://www.youtube.com/watch?v=CfVgawWSh6A

CAGES = [
    set([(1, 4), (1, 5), (1, 6)]),
    set([(3, 5), (3, 6)]),
    set([(6, 5), (7, 5), (8, 5)]),
    set([(7, 7), (8, 7), (7, 8)]),
]

solver = Solver(Solver.EMPTY)


def negative(s, vars):
    def oob(x):
        return x < 0 or x >= 9

    for r in range(9):
        for c in range(9):
            v = vars[r][c]
            for dc, dr in ((1, 0), (0, 1)):
                cc = c + dc
                rr = r + dr

                if oob(cc) or oob(rr):
                    continue

                # un-caged dominoes can not sum to 10
                if set([(c, r), (cc, rr)]) in CAGES:
                    continue

                s.add(v + vars[rr][cc] != 10)

            for dc0, dr0, dc1, dr1 in [
                (1, 0, 2, 0), # horisontal
                (0, 1, 0, 2), # vertical
                (0, 1, 1, 0), # bend with middle
                # (1, 0, 1, -1), # bend right-up
                # (1, 0, 1, 1), # bend right-down
                # (0, 1, -1, 1), # bend down-left
                # (0, 1, 1, 1), # bend down-right
            ]:
                cc0 = c + dc0
                rr0 = r + dr0
                cc1 = c + dc1
                rr1 = r + dr1

                if oob(cc0) or oob(rr0) or oob(cc1) or oob(rr1):
                    continue

                trio = set([(c, r), (cc0, rr0), (cc1, rr1)])
                if trio in CAGES:
                    print((c, r), (cc0, rr0), (cc1, rr1))
                    continue

                v0 = vars[rr0][cc0]
                v1 = vars[rr1][cc1]

                #print(v, v0, v1)
                s.add(v + v0 + v1 != 10)


solver.whisper_lines([
    [(2, 0), (3, 0), (4, 0), (4, 1), (4, 2), (5, 2), (6, 2), (6, 1)],
    [(6, 0), (7, 0), (8, 0)],
    [(0, 4), (1, 5), (2, 5), (2, 6)],
])

for cage in CAGES:
    solver.killer_cage(cage, 10)

solver.extra_constraint(negative)

solution = solver.solve()

Solver.pretty_print(solution)
