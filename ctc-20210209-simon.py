from solver import Solver, _
import z3
from utils import z3_count, orthogonal

# https://www.youtube.com/watch?v=NCUveHxyZZo

CAGES = [
    ([(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (1, 1), (3, 1)], 31),
    ([(5, 0), (6, 0), (7, 0), (8, 0), (6, 1)], 30),
    ([(0, 1), (0, 2), (0, 3), (1, 3)], None),
    ([(2, 1), (1, 2), (2, 2), (3, 2), (2, 3)], None),
    ([(4, 1), (5, 1), (4, 2), (4, 3)], None),
    ([(7, 1), (8, 1), (8, 2), (8, 3)], None),
    ([(5, 2), (6, 2), (7, 2), (5, 3), (6, 3), (7, 3), (5, 4), (6, 4), (7, 4)], None),
    ([(3, 3), (2, 4), (3, 4), (4, 4), (3, 5)], None),
    ([(0, 4), (1, 4), (0, 5), (0, 6), (0, 7), (0, 8)], None),
    ([(8, 4), (8, 5), (8, 6), (8, 7)], 16),
    ([(1, 5), (2, 5), (1, 6), (2, 6)], 23),
    ([(4, 5), (3, 6), (4, 6), (5, 6), (4, 7)], 31),
    ([(5, 5), (6, 5), (7, 5), (7, 6)], None),
    ([(6, 6), (5, 7), (6, 7), (4, 8), (5, 8)], 26),
    ([(1, 7), (2, 7), (3, 7)], 17),
    ([(7, 7), (6, 8), (7, 8), (8, 8)], 20),
    ([(1, 8), (2, 8), (3, 8)], None),
]

shading = []
z3_solver = None


def norinori(s, vars):
    global shading, z3_solver

    z3_solver = s

    for r in range(9):
        row = []
        for c in range(9):
            v = z3.Int(f"shading_{c}_{r}")

            s.add(z3.Or(v == 0, v == 1))

            row.append(v)

        shading.append(row)

    # each shaded cell has exactly on shaded neighbor
    for r in range(9):
        for c in range(9):
            v = shading[r][c]

            ns = []
            for nc, nr in orthogonal(shading, c, r):
                ns.append(shading[nr][nc])

            s.add(z3.Or(
                v == 0,
                z3_count(lambda v: v == 1, ns) == 1
            ))

    # each cage has two shaded cells
    for cage in CAGES:
        s.add(z3_count(lambda v: v == 1, [shading[r][c] for c, r in cage[0]]) == 2)

    # shaded cells are odd
    for r in range(9):
        for c in range(9):
            v = vars[r][c]
            sv = shading[r][c]

            s.add(z3.Or(
                sv == 0,
                v == 1,
                v == 3,
                v == 5,
                v == 7,
                v == 9,
            ))


solver = (
    Solver()
    .extra_constraint(norinori)
)

seen = set()
for cage, sum in CAGES:
    assert not (set(cage) & seen)
    seen.update(cage)

    solver.killer_cage(cage, sum)

assert len(seen) == 81

solution = solver.solve()

Solver.pretty_print(solution)
print()

m = z3_solver.model()
for row in shading:
    r = []
    for v in row:
        r.append(m[v].as_long())

    print(" ".join(map(str, r)))
