from solver import Solver, _

# https://www.youtube.com/watch?v=wSPu8nH59iY

ARROWS = [
    [(1, 0), (1, 1)],
    [(5, 1), (1, 1)],
    [(7, 1), (-1, 1)],
    [(1, 2), (-1, -1)],
    [(2, 2), (-1, 1)],
    [(5, 2), (1, -1)],
    [(4, 3), (1, 0)],
    [(6, 3), (1, -1)],
    [(5, 4), (-1, 1)],
    [(6, 4), (1, 1)],
    [(1, 5), (-1, 0)],
    [(2, 5), (1, -1)],
    [(3, 5), (1, 1)],
    [(4, 5), (-1, 0)],
    [(7, 5), (-1, 1)],
    [(8, 5), (0, -1)],
    [(1, 7), (-1, 0)],
]

def arrows(s, vars):
    for (c, r), (dc, dr) in ARROWS:
        v = vars[r][c]

        nc = c + dc
        nr = r + dr
        while nc >= 0 and nc < 9 and nr >= 0 and nr < 9:
            nv = vars[nr][nc]

            s.add(v > nv)

            nc += dc
            nr += dr



solver = (
    Solver()
    .extra_constraint(arrows)
)

solution = solver.solve()

Solver.pretty_print(solution)
