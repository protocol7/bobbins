from solver import Solver

# https://www.youtube.com/watch?v=aExUrn4fh8o

LINES = [
    [(0, 3), [(0, 2), (0, 1), (0, 0)], [(1, 2), (2, 2), (2, 1)], [(0, 4), (0, 5), (0, 6)]],
    [(3, 3), [(3, 2), (4, 1)], [(2, 3), (1, 3)], [(3, 4), (4, 5)]],
    [(7, 0), [(6, 0), (5, 0)], [(8, 0), (8, 1)], [(7, 1), (7, 2)]],
    [(6, 6), [(6, 5), (5, 5)], [(7, 6), (7, 7)], [(5, 7), (4, 7)]],
    [(2, 8), [(1, 8), (0, 8)], [(2, 7), (2, 6)], [(3, 8), (4, 8)]],

    [(7, 3), [(6, 3)], [(8, 3)], [(7, 4)]],
]

def thripple(s, cells):
    for (mc, mr), leg0, leg1, leg2 in LINES:
        assert len(leg0) == len(leg1) == len(leg2)
        mv = cells[mr][mc]

        for (c0, r0), (c1, r1), (c2, r2) in zip(leg0, leg1, leg2):
            v0 = cells[r0][c0]
            v1 = cells[r1][c1]
            v2 = cells[r2][c2]

            s.add(v0 + v1 + v2 == mv)


s = (
    Solver(Solver.EMPTY)
    .extra_constraint(thripple)
)
solution = s.solve()

Solver.pretty_print(solution)
