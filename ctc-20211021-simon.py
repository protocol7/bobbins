from solver import Solver
import z3

# https://www.youtube.com/watch?v=La7Yg_rav24

solver = Solver(Solver.EMPTY)


# Box 1 (NW) will contain all the 2-digit square numbers (16, 25, 36, 49, 64, and 81), which may overlap but must be entirely contained within the box
def box1_squares(s, vars):
    box1 = solver._regions[0]

    for square in (16, 25, 36, 49, 64, 81):
        a = square // 10
        b = square % 10

        or_constraints = []

        for cell0, v0, cell1, v1 in solver.all_dominos(vars):
            if cell0 in box1 and cell1 in box1 and (cell0[0] < cell1[0] or cell0[1] < cell1[1]):
                or_constraints.append(z3.And(v0 == a, v1 == b))

        s.add(z3.Or(or_constraints))


# In each of boxes 3 (NE), 5 (centre) and 7 (SW), each digit will contribute to at least one 2-digit prime number contained within that box.
def primes(s, vars):
    ps = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    boxes = solver._regions[2] + solver._regions[4] + solver._regions[6]

    for c, r in boxes:
        v = vars[r][c]
        or_constraints = []

        for dc, dr in [(0, -1), (1, 0), (0, 1), (-1, 0)]:
            cc = c + dc
            rr = r + dr

            if (cc, rr) not in boxes:
                continue

            vv = vars[rr][cc]

            for p in ps:
                a = p // 10
                b = p % 10

                if a == b:
                    continue

                if c < cc or r < rr:
                    # cell has to be a
                    or_constraints.append(z3.And(v == a, vv == b))
                else:
                    or_constraints.append(z3.And(vv == a, v == b))

        s.add(z3.Or(or_constraints))


# In each of box 6 (E) and 8 (S), the two 3-digit diagonals sum to the same
# number (NB box 6's number may be different from box 8's number)
def diagonals(s, cells):
    for cc, cr in [(7, 4), (4, 7)]:
        v0, _, v2 = cells[cr - 1][cc - 1], cells[cr - 1][cc], cells[cr - 1][cc + 1]
        _, v4, _ = cells[cr][cc - 1], cells[cr][cc], cells[cr][cc + 1]
        v6, _, v8 = cells[cr + 1][cc - 1], cells[cr + 1][cc], cells[cr + 1][cc + 1]

        # diagonals
        print(v0 + v4 + v8 == v2 + v4 + v6)
        s.add(v0 + v4 + v8 == v2 + v4 + v6)


# Box 9 (SE) is a clone of box 1, rotated through 180°
solver.clones([
    [(0, 0), (8, 8)],
    [(1, 0), (7, 8)],
    [(2, 0), (6, 8)],
    [(0, 1), (8, 7)],
    [(1, 1), (7, 7)],
    [(2, 1), (6, 7)],
    [(0, 2), (8, 6)],
    [(1, 2), (7, 6)],
    [(2, 2), (6, 6)],
])

solver.extra_constraint(box1_squares)
solver.extra_constraint(primes)
solver.magic_squares([(1, 4)])
solver.extra_constraint(diagonals)

solution = solver.solve()

Solver.pretty_print(solution)
