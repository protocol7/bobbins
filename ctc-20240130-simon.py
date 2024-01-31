from solver import Solver, _
import z3

# https://www.youtube.com/watch?v=tZd3StxpVzo


def extras(s, vars):
    # - A horizontal Arrow pointing east (with a one-cell circle)
    or_terms = []
    for r in range(9):
        end_c = 6 if r < 8 else 4
        for c in range(end_c):
            head = vars[r][c]
            arrow = [vars[r][c+1] + vars[r][c+2] + vars[r][c+3]]

            or_terms.append(head == z3.Sum(arrow))

    s.add(z3.Or(or_terms))

    # - A horizontal Thermometer
    or_terms = []
    for r in range(8):
        vs = [vars[r][c] for c in range(9)]

        and_terms = []
        for i, v in enumerate(vs, 1):
            and_terms.append(v == i)

        or_terms.append(z3.And(and_terms))

        and_terms = []
        for i, v in enumerate(vs[::-1], 1):
            and_terms.append(v == i)

        or_terms.append(z3.And(and_terms))

    s.add(z3.Or(or_terms))

    # - A horizontal German Whispers line
    or_terms = []
    for r in range(8):
        for i in [0, 1]:
            vs = [vars[r][c] for c in range(i, i + 8)]

            and_terms = []
            for v0, v1 in zip(vs, vs[1:]):
                and_terms.append(z3.Abs(v0 - v1) >= 5)

            or_terms.append(z3.And(and_terms))

    s.add(z3.Or(or_terms))

    # - A vertical German Whispers line
    or_terms = []
    for c in range(9):
        for i in [0, 1]:
            if c in (7, 8):
                continue

            vs = [vars[r][c] for r in range(i, i + 8)]

            and_terms = []
            for v0, v1 in zip(vs, vs[1:]):
                and_terms.append(z3.Abs(v0 - v1) >= 5)

            or_terms.append(z3.And(and_terms))

    s.add(z3.Or(or_terms))

    # - A vertical Zipper line
    or_terms = []
    for c in range(7):
        sum = vars[4][c]
        vs0 = [vars[r][c] for r in range(4)][::-1]
        vs1 = [vars[r][c] for r in range(5, 9)]

        and_terms = []
        for v0, v1 in zip(vs0, vs1):
            and_terms.append(v0 + v1 == sum)

        or_terms.append(z3.And(and_terms))

    s.add(z3.Or(or_terms))

    # I'd also like some sort of anti-chess constraint: anti-knight, anti-king, or anti-bishop (up to you, whichever works).
    or_terms = []

    # anti-knight
    and_terms = []
    for r in range(9):
        for c in range(9):
            v = vars[r][c]

            for dc, dr in ((-1, -2), (1, -2), (2, -1), (2, 1), (1, 2), (-1, 2), (-2, 1), (-2, -1), ):
                cc = c + dc
                rr = r + dr

                if cc >= 0 and rr >= 0 and cc < 9 and rr < 9:
                    and_terms.append(vars[r][c] != vars[rr][cc])

    or_terms.append(z3.And(and_terms))

    # anti-king
    and_terms = []
    for r in range(9):
        for c in range(9):
            v = vars[r][c]

            for dc, dr in ((-1, -1), (1, -1), (1, 1), (-1, 1)):
                cc = c + dc
                rr = r + dr

                if cc >= 0 and rr >= 0 and cc < 9 and rr < 9:
                    and_terms.append(vars[r][c] != vars[rr][cc])

    or_terms.append(z3.And(and_terms))

    # anti-bishop
    and_terms = []
    for r in range(9):
        for c in range(9):
            v = vars[r][c]

            for dc, dr in ((-1, -1), (1, -1), (1, 1), (-1, 1)):
                cc = c + dc
                rr = r + dr

                while cc >= 0 and rr >= 0 and cc < 9 and rr < 9:
                    and_terms.append(vars[r][c] != vars[rr][cc])

                    cc += dc
                    rr += dr

    or_terms.append(z3.And(and_terms))

    s.add(z3.Or(or_terms))

    # Oh, and make sure the solution has a 3 in the corner, won't you?
    or_terms = []
    for r in (0, 8):
        for c in (0, 8):
            v = vars[r][c]

            or_terms.append(v == 3)

    s.add(z3.Or(or_terms))


solver = (
    Solver()
    .extra_constraint(extras)
)

solution = solver.solve()

Solver.pretty_print(solution)
