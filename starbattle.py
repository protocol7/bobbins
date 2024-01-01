import z3

class Solver:

    def __init__(self, regions, width=9, height=9, stars=2):
        self._regions = regions
        self._width = width
        self._height = height
        self._stars = stars

    def solve(self):
        s = z3.Solver()

        # check regions
        seen = set()
        for region in self._regions:
            # no dups in the region
            assert len(set(region)) == len(region)

            # must not have been seen in some other region
            assert len(set(region) & seen) == 0

            seen.update(region)

        assert len(seen) == self._width * self._height

        # the board, made up of a list of list of integer variables
        vars = []
        for r in range(self._height):
            row = []
            for c in range(self._width):
                v = z3.Int("c%sr%s" % (c, r))
                s.add(z3.Or(v == 0, v == 1))

                row.append(v)

            # each row contains exactly K stars
            s.add(z3.Sum(row) == self._stars)

            vars.append(row)

        # each column contains exactly K stars
        for col in map(list, zip(*vars)):
            s.add(z3.Sum(col) == self._stars)

        # add region constraints
        for region in self._regions:
            s.add(z3.Sum([vars[r][c] for c, r in region]) == self._stars)

        # stars do not touch any other stars
        for r, row in enumerate(vars):
            for c, v in enumerate(row):
                ns = []

                for dc, dr in [(0, -1), (1, -1), (1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1)]:
                    nc = c + dc
                    nr = r + dr

                    if nc < 0 or nr < 0 or nc >= self._width or nr >= self._height:
                        continue

                    ns.append(vars[nr][nc])

                s.add(z3.Or(
                    v == 0,
                    z3.And(v == 1, z3.Sum(ns) == 0)
                ))

        # solve
        if s.check() == z3.sat:
            m = s.model()
            r = [[m.evaluate(vars[r][c]) for c in range(self._width)] for r in range(self._height)]
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
