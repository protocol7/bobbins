import z3
from collections import defaultdict


class Solver:
    EMPTY = (
        (0, 0, 0, 0, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 0, 0, 0, 0),
    )

    def __init__(self, given):
        self.given = given
        self._regions = [
            ((0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (2, 1), (0, 2), (1, 2), (2, 2)),
            ((3, 0), (4, 0), (5, 0), (3, 1), (4, 1), (5, 1), (3, 2), (4, 2), (5, 2)),
            ((6, 0), (7, 0), (8, 0), (6, 1), (7, 1), (8, 1), (6, 2), (7, 2), (8, 2)),
            ((0, 3), (1, 3), (2, 3), (0, 4), (1, 4), (2, 4), (0, 5), (1, 5), (2, 5)),
            ((3, 3), (4, 3), (5, 3), (3, 4), (4, 4), (5, 4), (3, 5), (4, 5), (5, 5)),
            ((6, 3), (7, 3), (8, 3), (6, 4), (7, 4), (8, 4), (6, 5), (7, 5), (8, 5)),
            ((0, 6), (1, 6), (2, 6), (0, 7), (1, 7), (2, 7), (0, 8), (1, 8), (2, 8)),
            ((3, 6), (4, 6), (5, 6), (3, 7), (4, 7), (5, 7), (3, 8), (4, 8), (5, 8)),
            ((6, 6), (7, 6), (8, 6), (6, 7), (7, 7), (8, 7), (6, 8), (7, 8), (8, 8)),
        ]
        self._unique_positive_diagonal = False
        self._unique_negative_diagonal = False
        self._thermos = []
        self._arrows = []
        self._black_kropkis = []
        self._white_kropkis = []
        self._region_sum_lines = []
        self._zipper_lines = []
        self._smaller_thans = []
        self._killer_cages = []
        self._whisper_lines = []
        self._x_v = []
        self._anti_x_v = False
        self._renban_lines = []
        self._anti_knight = False
        self._anti_king = False
        self._anti_consecutive = False
        self._disjoint = False
        self._entropic_lines = []

    def regions(self, regions):
        self._regions = regions

    def unique_positive_diagonal(self):
        self._unique_positive_diagonal = True
        return self

    def unique_negative_diagonal(self):
        self._unique_negative_diagonal = True
        return self

    def thermo(self, thermo, slow=False):
        self._thermos.append((thermo, slow))
        return self

    def arrow(self, arrow):
        self._arrows.append(arrow)
        return self

    def arrows(self, arrows):
        self._arrows.extend(arrows)
        return self

    def black_kropkis(self, dots):
        assert all(len(d) == 2 for d in dots)

        self._black_kropkis.extend(dots)
        return self

    def white_kropkis(self, dots):
        assert all(len(d) == 2 for d in dots)

        self._white_kropkis.extend(dots)
        return self

    def region_sum_line(self, line):
        return self.region_sum_lines([line])

    def region_sum_lines(self, lines):
        self._region_sum_lines.extend(lines)
        return self

    def zipper_line(self, line):
        self._zipper_lines.append(line)
        return self

    def zipper_lines(self, lines):
        self._zipper_lines.extend(lines)
        return self

    def smaller_than(self, smaller, larger):
        self._smaller_thans.append((smaller, larger))
        return self

    def killer_cage(self, cage, sum=None, unique=True):
        self._killer_cages.append((cage, sum, unique))
        return self

    def little_killer(self, cage, sum):
        self._killer_cages.append((cage, sum, False))
        return self

    def whisper_lines(self, lines, min_diff=5):
        self._whisper_lines.extend([(line, min_diff) for line in lines])
        return self

    def x(self, cell1, cell2):
        self._x_v.append((cell1, cell2, 10))
        return self

    def v(self, cell1, cell2):
        self._x_v.append((cell1, cell2, 5))
        return self

    def renban_lines(self, lines):
        self._renban_lines.extend(lines)
        return self

    def anti_knight(self):
        self._anti_knight = True
        return self

    def anti_king(self):
        self._anti_king = True
        return self

    def anti_consecutive(self):
        self._anti_consecutive = True
        return self

    def disjoiint(self):
        self._disjoint = True
        return self

    def entropic_lines(self, lines):
        self._entropic_lines.extend(lines)
        return self

    def anti_x_v(self):
        self._anti_x_v = True
        return self

    def solve(self):
        s = z3.Solver()

        # 9x9 matrix of integer variables
        vars = []
        for r in range(9):
            row = []
            for c in range(9):
                v = z3.Int("r%sc%s" % (r, c))
                s.add(v >= 1, v <= 9)

                row.append(v)

            # each row contains a digit at most once
            s.add(z3.Distinct(row))

            vars.append(row)

        # each column contains a digit at most once
        for col in map(list, zip(*vars)):
            s.add(z3.Distinct(col))

        # add region constraints
        for region in self._regions:
            s.add(z3.Distinct([vars[r][c] for c, r in region]))

        # add diagnoal constraints
        if self._unique_positive_diagonal:
            diagonal = []
            for r in range(8, -1, -1):
                c = 8 - r
                diagonal.append(vars[r][c])

            s.add(z3.Distinct(diagonal))

        if self._unique_negative_diagonal:
            diagonal = []
            for r in range(9):
                diagonal.append(vars[r][r])

            s.add(z3.Distinct(diagonal))

        # add thermo constraints
        for thermo, slow in self._thermos:
            for (c0, r0), (c1, r1) in zip(thermo, thermo[1:]):
                if slow:
                    s.add(vars[r1][c1] >= vars[r0][c0])
                else:
                    s.add(vars[r1][c1] > vars[r0][c0])

        # add arrow constraints
        for arrow in self._arrows:
            (hc, hr), arrow = arrow[0], arrow[1:]

            s.add(vars[hr][hc] == z3.Sum([vars[r][c] for c, r in arrow]))

        # add kropki constraints
        for (c0, r0), (c1, r1) in self._black_kropkis:
            v0 = vars[r0][c0]
            v1 = vars[r1][c1]

            s.add(z3.Or(v0 * 2 == v1, v1 * 2 == v0))

        for (c0, r0), (c1, r1) in self._white_kropkis:
            v0 = vars[r0][c0]
            v1 = vars[r1][c1]

            s.add(z3.Or(v0 - v1 == 1, v1 - v0 == 1))

        # add region sum lines constraints
        for line in self._region_sum_lines:
            # divide up per region
            chunks = defaultdict(set)
            for cell in line:
                for region in self._regions:
                    if cell in region:
                        chunks[region].add(cell)

            chunks = [c for c in chunks.values()]

            # each pair of chunks must have the same sum
            for c1, c2 in zip(chunks, chunks[1:]):
                s1 = z3.Sum([vars[r][c] for c, r in c1])
                s2 = z3.Sum([vars[r][c] for c, r in c2])
                s.add(s1 == s2)

        # add zipper line constraints
        for line in self._zipper_lines:
            middle_i = len(line) // 2
            part1 = line[:middle_i][::-1]
            part2 = line[middle_i+1:]

            assert len(part1) == len(part2)

            mc, mr = line[middle_i]

            for (c0, r0), (c1, r1) in zip(part1, part2):
                s.add(vars[mr][mc] == vars[r0][c0] + vars[r1][c1])

        # add smaller-than constraints
        for (sc, sr), (lc, lr) in self._smaller_thans:
            s.add(vars[sr][sc] < vars[lr][lc])

        # add killer cage constraints
        for cage, sum, unique in self._killer_cages:
            if unique:
                # digits in the cage must be unique
                s.add(z3.Distinct([vars[r][c] for c, r in cage]))

            if sum is not None:
                s.add(sum == z3.Sum([vars[r][c] for c, r in cage]))

        # add whisper line constraints
        for line, min_diff in self._whisper_lines:
            for (c0, r0), (c1, r1) in zip(line, line[1:]):
                v0 = vars[r0][c0]
                v1 = vars[r1][c1]

                s.add(z3.Abs(v0 - v1) >= min_diff)

        def all_dominos(vars):
            for r in range(9):
                for c in range(9):
                    for dc, dr in ((0, -1), (1, 0), (0, 1), (-1, 0)):
                        cc = c + dc
                        rr = r + dr

                        if cc >= 0 and rr >= 0 and cc < 9 and rr < 9:
                            v0 = vars[r][c]
                            v1 = vars[rr][cc]

                            yield (c, r), v0, (cc, rr), v1

        # add X/V constraints
        for (c0, r0), (c1, r1), sum in self._x_v:
            v0 = vars[r0][c0]
            v1 = vars[r1][c1]
            s.add(v0 + v1 == sum)

        if self._anti_x_v:
            for cell0, v0, cell1, v1 in all_dominos(vars):
                if cell0 in self._x_v and cell1 in self._x_v:
                    # has an X or V
                    continue

                s.add(v0 + v1 != 5)
                s.add(v0 + v1 != 10)

        # add renban line constraints
        for line in self._renban_lines:
            cells = [vars[r][c] for c, r in line]
            # must by unique
            s.add(z3.Distinct(cells))

            # must be consecutive
            for i, c0 in enumerate(cells):
                for j, c1 in enumerate(cells):
                    if i >= j:
                        continue

                    s.add(z3.Abs(c0 - c1) < len(line))

        # add anti-knight constraint
        if self._anti_knight:
            for r in range(9):
                for c in range(9):
                    for dc, dr in ((-1, -2), (1, -2), (2, -1), (2, 1), (1, 2), (-1, 2), (-2, 1), (-2, -1), ):
                        cc = c + dc
                        rr = r + dr

                        if cc >= 0 and rr >= 0 and cc < 9 and rr < 9:
                            s.add(vars[r][c] != vars[rr][cc])

        # add anti-king constraint
        if self._anti_king:
            for r in range(9):
                for c in range(9):
                    for dc, dr in ((-1, -1), (1, -1), (1, 1), (-1, 1)):
                        cc = c + dc
                        rr = r + dr

                        if cc >= 0 and rr >= 0 and cc < 9 and rr < 9:
                            s.add(vars[r][c] != vars[rr][cc])

        # add anti-consecutive constraint
        if self._anti_consecutive:
            for _, v0, _, v1 in all_dominos(vars):
                s.add(z3.Abs(v0 - v1) != 1)

        # add disjoint constraint
        if self._disjoint:
            for ss in zip(*self._regions):
                cells = [vars[r][c] for c, r in ss]
                s.add(z3.Distinct(cells))

        # add entropic lines constraints
        for line in self._entropic_lines:
            def same_entropy(offset):
                items = [line[i] for i in range(offset, len(line), 3)]
                cells = [vars[r][c] for c, r in items]

                for v0, v1 in zip(cells, cells[1:]):
                    s.add((v0 - 1) / 3 == (v1 - 1) / 3)

            for offset in range(3):
                same_entropy(offset)

            # above we check that we have chains of the same entropy
            # throughout the line, so here we only need to check the
            # first three cells on the line and make sure they don't
            # have the same entropy

            # TODO fix
            assert len(line) >= 3

            (c0, r0), (c1, r1), (c2, r2) = line[:3]
            v0 = vars[r0][c0]
            v1 = vars[r1][c1]
            v2 = vars[r2][c2]

            s.add((v0 - 1) / 3 != (v1 - 1) / 3)
            s.add((v1 - 1) / 3 != (v2 - 1) / 3)
            s.add((v0 - 1) / 3 != (v2 - 1) / 3)

        # add givens
        for r, row in enumerate(self.given):
            for c, x in enumerate(row):
                if x != 0:
                    s.add(vars[r][c] == x)

        # solve
        if s.check() == z3.sat:
            m = s.model()
            r = [[m.evaluate(vars[i][j]) for j in range(9)] for i in range(9)]
            return r
        else:
            return None

    @staticmethod
    def pretty_print(solution):
        if solution is None:
            print("No solution")
            return

        for row in solution:
            print(" ".join(map(str, row)))
