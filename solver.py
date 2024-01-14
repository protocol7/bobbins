import z3
from collections import defaultdict
from itertools import combinations
from utils import z3_count

_ = None


class Solver:

    def grid(width, height, value=None):
        return [[value] * width for _ in range(height)]

    def empty(width, height):
        return [[None] * width for _ in range(height)]

    EMPTY_9X9 = empty(9, 9)
    EMPTY = EMPTY_9X9

    EMPTY_6X6 = empty(6, 6)

    EMPTY_4X4 = empty(4, 4)

    REGULAR_9X9_REGIONS = [
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

    REGULAR_6X6_REGIONS = [
            ((0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (2, 1)),
            ((3, 0), (4, 0), (5, 0), (3, 1), (4, 1), (5, 1)),
            ((0, 2), (1, 2), (2, 2), (0, 3), (1, 3), (2, 3)),
            ((3, 2), (4, 2), (5, 2), (3, 3), (4, 3), (5, 3)),
            ((0, 4), (1, 4), (2, 4), (0, 5), (1, 5), (2, 5)),
            ((3, 4), (4, 4), (5, 4), (3, 5), (4, 5), (5, 5)),
        ]

    REGULAR_4X4_REGIONS = [
            ((0, 0), (1, 0), (0, 1), (1, 1)),
            ((2, 0), (3, 0), (2, 1), (3, 1)),
            ((0, 2), (1, 2), (0, 3), (1, 3)),
            ((2, 2), (3, 2), (2, 3), (3, 3)),
        ]

    ORTHOGONAL = [(0, -1), (1, 0), (0, 1), (-1, 0)]

    @staticmethod
    def regular_4x4(given=None):
        return (
            Solver(given=given, width=4, height=4)
            .digits(list(range(1, 4 + 1)))
            .regions(Solver.REGULAR_4X4_REGIONS)
        )

    @staticmethod
    def regular_6x6(given=None):
        return (
            Solver(given=given, width=6, height=6)
            .digits(list(range(1, 6 + 1)))
            .regions(Solver.REGULAR_6X6_REGIONS)
        )

    def __init__(self, given=None, width=9, height=9):
        self._given = given
        self._width = width
        self._height = height
        self._regions = Solver.REGULAR_9X9_REGIONS
        self._digits = list(range(1, 9 + 1))
        self._unique_positive_diagonal = False
        self._unique_negative_diagonal = False
        self._thermos = []
        self._arrows = []
        self._black_kropkis = []
        self._white_kropkis = []
        self._white_kropkis_anti = False
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
        self._odd_cells = []
        self._even_cells = []
        self._nabner_lines = []
        self._palindrom_lines = []
        self._between_lines = []
        self._quadruples = []
        self._xsums_rows = []
        self._xsums_cols = []
        self._clones = []
        self._sandwhich_rows = []
        self._sandwhich_cols = []
        self._magic_squares = []
        self._circles = []
        self._multiplier = (1, False, False, False, False)

        self._extra_constraints = []

    def regions(self, regions):
        self._regions = regions
        return self

    def digits(self, digits):
        self._digits = digits
        return self

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

    def white_kropkis(self, dots, anti=False):
        assert all(len(d) == 2 for d in dots)

        self._white_kropkis.extend(dots)
        self._white_kropkis_anti = anti
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

    def xs(self, pairs):
        self._x_v.extend((cell1, cell2, 10) for cell1, cell2 in pairs)
        return self

    def vs(self, pairs):
        self._x_v.extend((cell1, cell2, 5) for cell1, cell2 in pairs)
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

    def odds(self, cells):
        self._odd_cells.extend(cells)
        return self

    def evens(self, cells):
        self._even_cells.extend(cells)
        return self

    def nabner_lines(self, lines):
        self._nabner_lines.extend(lines)
        return self

    def palindrom_lines(self, lines):
        self._palindrom_lines.extend(lines)
        return self

    def between_lines(self, lines):
        self._between_lines.extend(lines)
        return self

    def quadruple(self, upper_left_cell, digits):
        self._quadruples.append((upper_left_cell, digits))
        return self

    def xsums(self, rows, cols):
        self._xsums_rows.extend(rows)
        self._xsums_cols.extend(cols)
        return self

    def clones(self, clones):
        self._clones.extend(clones)
        return self

    def sandwhiches(self, rows, cols, low_digit=1, high_digit=9):
        for row in rows:
            self._sandwhich_rows.append((row, low_digit, high_digit))
        for col in cols:
            self._sandwhich_cols.append((col, low_digit, high_digit))
        return self

    # a list of center points of 3x3 magic squares
    def magic_squares(self, centers):
        self._magic_squares.extend(centers)
        return self

    def circles(self, circles):
        """A digit in a circled cell indicates the total number of times that
           digit appears in circled cells in the grid"""
        self._circles.extend(circles)
        return self

    def multipliers(self, multiplier, one_per_row=True, one_per_col=True, one_per_region=True, unique=True):
        self._multiplier = (multiplier, one_per_row, one_per_col, one_per_region, unique)
        return self

    # fn(solver, cells)
    def extra_constraint(self, fn, with_multipliers=False):
        self._extra_constraints.append((fn, with_multipliers))
        return self

    # here are methods for adding each type of constraint

    def _add_diagonals(self, s, vars):
        # add diagonal constraints
        if self._unique_positive_diagonal:
            assert self._height == self._width

            diagonal = []
            for r in range(self._height - 1, -1, -1):
                c = (self._width - 1) - r
                diagonal.append(vars[r][c])

            s.add(z3.Distinct(diagonal))

        if self._unique_negative_diagonal:
            assert self._height == self._width

            diagonal = []
            for r in range(self._height):
                diagonal.append(vars[r][r])

            s.add(z3.Distinct(diagonal))

    def _add_thermos(self, s, vars, multipliers):
        # add thermo constraints
        for thermo, slow in self._thermos:
            vs = [vars[r][c] * multipliers[r][c] for c, r in thermo]
            for v0, v1 in zip(vs, vs[1:]):
                if slow:
                    s.add(v1 >= v0)
                else:
                    s.add(v1 > v0)

    def _add_arrows(self, s, vars):
        # add arrow constraints
        for arrow in self._arrows:
            (hc, hr), arrow = arrow[0], arrow[1:]

            s.add(vars[hr][hc] == z3.Sum([vars[r][c] for c, r in arrow]))

    def _add_kropkis(self, s, vars, multipliers):
        # add kropki constraints
        for (c0, r0), (c1, r1) in self._black_kropkis:
            assert (c0, r0) != (c1, r1)
            v0 = vars[r0][c0] * multipliers[r0][c0]
            v1 = vars[r1][c1] * multipliers[r1][c1]

            s.add(z3.Or(v0 * 2 == v1, v1 * 2 == v0))

        whites = set()
        for (c0, r0), (c1, r1) in self._white_kropkis:
            assert (c0, r0) != (c1, r1)
            whites.add(frozenset([(c0, r0), (c1, r1)]))
            v0 = vars[r0][c0] * multipliers[r0][c0]
            v1 = vars[r1][c1] * multipliers[r1][c1]

            s.add(z3.Or(v0 - v1 == 1, v1 - v0 == 1))

        if self._white_kropkis_anti:
            for (c0, r0), v0, (c1, r1), v1 in self.all_dominos(vars):
                k = frozenset([(c0, r0), (c1, r1)])
                if k in whites:
                    continue

                v0 = v0 * multipliers[r0][c0]
                v1 = v1 * multipliers[r1][c1]

                s.add(z3.And(z3.Abs(v0 - v1) != 1))

    def _add_region_sum_lines(self, s, vars):
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

    def _add_zipper_lines(self, s, vars, multipliers):
        # add zipper line constraints

        # Digits an equal distance from the centre of a
        # zipper line must sum to the same total.

        for i, line in enumerate(self._zipper_lines):
            # For odd length lines, the total is the digit in the centre of
            # the line.
            if len(line) % 2 == 1:
                middle_i = len(line) // 2
                part1 = line[:middle_i][::-1]
                part2 = line[middle_i+1:]

                assert len(part1) == len(part2)

                mc, mr = line[middle_i]
                vsum = vars[mr][mc] * multipliers[mr][mc]
            else:
                middle_i = len(line) // 2
                part1 = line[:middle_i][::-1]
                part2 = line[middle_i:]

                assert len(part1) == len(part2)

                vsum = z3.Int("zipper_%s" % i)

            for (c0, r0), (c1, r1) in zip(part1, part2):
                s.add(vsum == vars[r0][c0] * multipliers[r0][c0] + vars[r1][c1] * multipliers[r1][c1])

    def _add_smaller_than(self, s, vars):
        # add smaller-than constraints
        for (sc, sr), (lc, lr) in self._smaller_thans:
            s.add(vars[sr][sc] < vars[lr][lc])

    def _add_killer_cages(self, s, vars, multipliers):
        # add killer cage constraints
        # supports multiplers
        seen = set()
        for cage, sum, unique in self._killer_cages:
            assert not set(cage) & seen
            seen.update(cage)
            vs = [vars[r][c] * multipliers[r][c] for c, r in cage]
            if unique:
                # digits in the cage must be unique
                s.add(z3.Distinct(vs))

            if sum is not None:
                s.add(sum == z3.Sum(vs))

    def _add_whisper_lines(self, s, vars, multipliers):
        # add whisper line constraints
        for line, min_diff in self._whisper_lines:
            for (c0, r0), (c1, r1) in zip(line, line[1:]):
                v0 = vars[r0][c0] * multipliers[r0][c0]
                v1 = vars[r1][c1] * multipliers[r1][c1]

                s.add(z3.Abs(v0 - v1) >= min_diff)

    def _add_x_v(self, s, vars):
        # add X/V constraints
        for (c0, r0), (c1, r1), sum in self._x_v:
            v0 = vars[r0][c0]
            v1 = vars[r1][c1]
            s.add(v0 + v1 == sum)

        if self._anti_x_v:
            for cell0, v0, cell1, v1 in self.all_dominos(vars):
                if cell0 in self._x_v and cell1 in self._x_v:
                    # has an X or V
                    continue

                s.add(v0 + v1 != 5)
                s.add(v0 + v1 != 10)

    def _add_renban_nabner_lines(self, s, vars, multipliers):
        # add renban line constraints
        # supports multiplers
        for line in self._renban_lines:
            vs = [vars[r][c] * multipliers[r][c] for c, r in line]
            # must by unique
            s.add(z3.Distinct(vs))

            # must be consecutive
            for i, v0 in enumerate(vs):
                for j, v1 in enumerate(vs):
                    if i >= j:
                        continue

                    s.add(z3.Abs(v0 - v1) < len(line))

        # add nabner line constraints
        for line in self._nabner_lines:
            vs = [vars[r][c] * multipliers[r][c] for c, r in line]
            # must by unique
            s.add(z3.Distinct(vs))

            # must not be consecutive
            for i, v0 in enumerate(vs):
                for j, v1 in enumerate(vs):
                    if i >= j:
                        continue

                    s.add(z3.Abs(v0 - v1) != 1)

    def _add_anti_knight(self, s, vars):
        # add anti-knight constraint
        if self._anti_knight:
            for r in range(self._height):
                for c in range(self._width):
                    for dc, dr in ((-1, -2), (1, -2), (2, -1), (2, 1), (1, 2), (-1, 2), (-2, 1), (-2, -1), ):
                        cc = c + dc
                        rr = r + dr

                        if cc >= 0 and rr >= 0 and cc < self._width and rr < self._height:
                            s.add(vars[r][c] != vars[rr][cc])

    def _add_anti_king(self, s, vars):
        # add anti-king constraint
        if self._anti_king:
            for r in range(self._height):
                for c in range(self._width):
                    for dc, dr in ((-1, -1), (1, -1), (1, 1), (-1, 1)):
                        cc = c + dc
                        rr = r + dr

                        if cc >= 0 and rr >= 0 and cc < self._width and rr < self._height:
                            s.add(vars[r][c] != vars[rr][cc])

    def _add_non_consecutive(self, s, vars):
        # add anti-consecutive constraint
        if self._anti_consecutive:
            for _, v0, _, v1 in self.all_dominos(vars):
                s.add(z3.Abs(v0 - v1) != 1)

    def _add_disjoint(self, s, vars):
        # add disjoint constraint
        if self._disjoint:
            for ss in zip(*self._regions):
                cells = [vars[r][c] for c, r in ss]
                s.add(z3.Distinct(cells))

    def _add_entropic_lines(self, s, vars):
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

            assert len(line) >= 2

            (c0, r0), (c1, r1) = line[:2]
            v0 = vars[r0][c0]
            v1 = vars[r1][c1]
            s.add((v0 - 1) / 3 != (v1 - 1) / 3)

            if len(line) > 2:
                (c2, r2) = line[2]
                v2 = vars[r2][c2]

                s.add((v1 - 1) / 3 != (v2 - 1) / 3)
                s.add((v0 - 1) / 3 != (v2 - 1) / 3)

    def _add_odd_evens(self, s, vars):
        # add odd/even constraints
        for c, r in self._odd_cells:
            s.add(vars[r][c] % 2 == 1)

        for c, r in self._even_cells:
            s.add(vars[r][c] % 2 == 0)

    def _add_palindroms(self, s, vars):
        # add palindrom constraints
        for line in self._palindrom_lines:
            middle_i = len(line) // 2
            part1 = line[:middle_i][::-1]
            if len(line) % 2 == 1:
                part2 = line[middle_i+1:]
            else:
                part2 = line[middle_i:]

            assert len(part1) == len(part2)

            for (c0, r0), (c1, r1) in zip(part1, part2):
                s.add(vars[r0][c0] == vars[r1][c1])

    def _add_between_lines(self, s, vars):
        # add between line constraints
        for line in self._between_lines:
            xc, xr = line[0]
            yc, yr = line[-1]
            line = line[1:-1]
            xv = vars[xr][xc]
            yv = vars[yr][yc]

            for c, r in line:
                v = vars[r][c]
                s.add(z3.Or(z3.And(v < xv, v > yv), z3.And(v > xv, v < yv)))

    def _add_quadruples(self, s, vars):
        # add quadruple constraints
        for (c, r), digits in self._quadruples:
            # TODO add support for repeated digits in quadruples
            assert len(digits) == len(set(digits))

            cs = [(c, r), (c + 1, r), (c, r + 1), (c + 1, r + 1)]
            v0, v1, v2, v3 = [vars[r][c] for c, r in cs]

            constraints = []
            for d in digits:
                constraints.append(z3.Or(v0 == d, v1 == d, v2 == d, v3 == d))

            s.add(z3.And(constraints))

    def _add_xsums(self, s, vars):
        # add xsum constraints
        def _xsums(cc, cr, sum, vr, max_x):
            vx = vars[cr][cc]
            or_constraints = []
            for x in range(1, max_x + 1):
                sub_vr = vr[:x]

                or_constraints.append(z3.And(vx == x, z3.Sum(sub_vr) == sum))

            s.add(z3.Or(or_constraints))

        # xsums rows
        for (cc, cr), sum in self._xsums_rows:
            vr = vars[cr]
            if cc == 8:
                vr = vr[::-1]

            _xsums(cc, cr, sum, vr, self._width)

        # xsums cols
        for (cc, cr), sum in self._xsums_cols:
            vc = [vars[r][cc] for r in range(0, self._height)]
            if cr == 8:
                vc = vc[::-1]

            _xsums(cc, cr, sum, vc, self._height)

    def _add_clones(self, s, vars):
        for clone in self._clones:
            vs = [vars[r][c] for c, r in clone]
            for a, b in combinations(vs, 2):
                s.add(a == b)

    def _add_sandwhiches(self, s, vars):
        def _sandwhiches(vs, size, low_digit, high_digit):
            or_constraints = []
            for low in range(0, size):
                vlow = vs[low]

                for high in range(0, size):
                    if low == high:
                        continue

                    vhigh = vs[high]
                    sub_vs = vs[min(low, high) + 1: max(low, high)]

                    or_constraints.append(z3.And(vlow == low_digit, vhigh == high_digit, z3.Sum(sub_vs) == sum))

            s.add(z3.Or(or_constraints))

        # sandwhich rows
        for (row, sum), low_digit, high_digit in self._sandwhich_rows:
            vrow = vars[row]
            _sandwhiches(vrow, self._width, low_digit, high_digit)

        # sandwhich cols
        for (col, sum), low_digit, high_digit in self._sandwhich_cols:
            vcol = [vars[r][col] for r in range(0, self._height)]
            _sandwhiches(vcol, self._height, low_digit, high_digit)

    def _add_magic_squares(self, s, vars):
        for c, r in self._magic_squares:
            v0, v1, v2 = vars[r - 1][c - 1], vars[r - 1][c], vars[r - 1][c + 1]
            v3, v4, v5 = vars[r][c - 1], vars[r][c], vars[r][c + 1]
            v6, v7, v8 = vars[r + 1][c - 1], vars[r + 1][c], vars[r + 1][c + 1]

            total = z3.Int("magic_square_%s_%s" % (c, r))

            # rows
            s.add(v0 + v1 + v2 == total)
            s.add(v3 + v4 + v5 == total)
            s.add(v6 + v7 + v8 == total)

            # cols
            s.add(v0 + v3 + v6 == total)
            s.add(v1 + v4 + v7 == total)
            s.add(v2 + v5 + v8 == total)

            # diagonals
            s.add(v0 + v4 + v8 == total)
            s.add(v2 + v4 + v6 == total)

    def _add_circles(self, s, vars):
        for digit in self._digits:
            count = z3.Sum([z3.If(vars[r][c] == digit, 1, 0) for c, r in self._circles])
            s.add(z3.Or(count == digit, count == 0))

    def _multipliers(self, s, vars):
        multiplier, one_per_row, one_per_col, one_per_region, unique = self._multiplier

        multipliers = []
        for r in range(self._height):
            row = []
            for c in range(self._width):
                v = z3.Int("multiplier_%s_%s" % (c, r))
                s.add(z3.Or(v == 1, v == multiplier))

                row.append(v)

            multipliers.append(row)

        if one_per_row:
            for row in multipliers:
                # one multiplier per row
                s.add(z3_count(lambda v: v == multiplier, row) == 1)

        if one_per_col:
            for col in map(list, zip(*multipliers)):
                # one multiplier per col
                s.add(z3_count(lambda v: v == multiplier, col) == 1)

        if one_per_region:
            for region in self._regions:
                vs = [multipliers[r][c] for c, r in region]

                # one multiplier per region
                s.add(z3_count(lambda v: v == multiplier, vs) == 1)

        if unique:
            # multipliers must be distinct
            cs = []
            placeholders = []
            p_value = 1000
            for r in range(self._height):
                row = []
                for c in range(self._width):
                    cs.append((c, r))

                    p = z3.Int("multiplier_placeholder_%s_%s" % (c, r))
                    s.add(p == p_value)
                    p_value += 1
                    row.append(p)

                placeholders.append(row)

            s.add(z3.Distinct([z3.If(multipliers[r][c] == multiplier, vars[r][c], placeholders[r][c]) for c, r in cs]))

        return multipliers

    def solve(self):
        s = z3.Solver()

        # the board, made up of a list of list of integer variables
        vars = []
        for r in range(self._height):
            row = []
            for c in range(self._width):
                v = z3.Int("c%sr%s" % (c, r))
                s.add(z3.Or([v == d for d in self._digits]))

                row.append(v)

            # each row contains a digit at most once
            s.add(z3.Distinct(row))

            vars.append(row)

        # each column contains a digit at most once
        for col in map(list, zip(*vars)):
            s.add(z3.Distinct(col))

        # verify regions are correct
        if self._regions:
            seen = set()
            for region in self._regions:
                assert len(region) == len(self._digits)

                # no duplicates
                assert len(set(region) & seen) == 0, region
                seen.update(region)

            assert len(seen) == self._width * self._height

            # add region constraints
            for region in self._regions:
                s.add(z3.Distinct([vars[r][c] for c, r in region]))

        multipliers = self._multipliers(s, vars)

        self._add_diagonals(s, vars)

        self._add_thermos(s, vars, multipliers)

        self._add_arrows(s, vars)

        self._add_kropkis(s, vars, multipliers)

        self._add_region_sum_lines(s, vars)

        self._add_zipper_lines(s, vars, multipliers)

        self._add_smaller_than(s, vars)

        self._add_killer_cages(s, vars, multipliers)

        self._add_whisper_lines(s, vars, multipliers)

        self._add_x_v(s, vars)

        self._add_renban_nabner_lines(s, vars, multipliers)

        self._add_anti_knight(s, vars)

        self._add_anti_king(s, vars)

        self._add_non_consecutive(s, vars)

        self._add_disjoint(s, vars)

        self._add_entropic_lines(s, vars)

        self._add_odd_evens(s, vars)

        self._add_palindroms(s, vars)

        self._add_between_lines(s, vars)

        self._add_quadruples(s, vars)

        self._add_xsums(s, vars)

        self._add_clones(s, vars)

        self._add_sandwhiches(s, vars)

        self._add_magic_squares(s, vars)

        self._add_circles(s, vars)

        # add extra constraints
        for extra_constraint, with_multipliers in self._extra_constraints:
            if with_multipliers:
                extra_constraint(s, vars, multipliers)
            else:
                extra_constraint(s, vars)

        # add givens
        if self._given:
            for r, row in enumerate(self._given):
                for c, x in enumerate(row):
                    if x in self._digits:
                        s.add(vars[r][c] == x)

        class Solution:
            def __init__(self, solver, z3_solver, vars, multipliers):
                self.solver = solver
                self.z3_solver = z3_solver
                self.grid = vars
                self.multipliers = multipliers

        # solve
        if s.check() == z3.sat:
            return Solution(self, s, vars, multipliers)
        else:
            return None

    def all_dominos(self, vars):
        for r in range(self._height):
            for c in range(self._width):
                for dc, dr in ((0, -1), (1, 0), (0, 1), (-1, 0)):
                    cc = c + dc
                    rr = r + dr

                    if cc >= 0 and rr >= 0 and cc < self._width and rr < self._height:
                        v0 = vars[r][c]
                        v1 = vars[rr][cc]

                        yield (c, r), v0, (cc, rr), v1

    def orthogonal(self, c, r):
        for dc, dr in Solver.ORTHOGONAL:
            cc = c + dc
            rr = r + dr

            if cc < 0 or rr < 0 or cc >= self._width or rr >= self._height:
                continue

            yield cc, rr

    @staticmethod
    def pretty_print(solution):
        if solution is None:
            print("No solution")
            return

        m = solution.z3_solver.model()
        vars = solution.grid
        grid = [[m[vars[r][c]] for c in range(len(vars[0]))] for r in range(len(vars))]

        for row in grid:
            print(" ".join(map(str, row)))

        if solution.solver._multiplier[0] > 1:
            print()

            mvars = solution.multipliers
            grid = [[m[mvars[r][c]] for c in range(len(mvars[0]))] for r in range(len(mvars))]

            for row in grid:
                s = []
                for v in row:
                    if v.as_long() > 1:
                        s += str(v.as_long())
                    else:
                        s += "."
                print(" ".join(s))
