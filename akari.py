import z3

class Solver:

    def __init__(self, black_cells, width=9, height=9):
        self._black_cells = black_cells
        self._width = width
        self._height = height

    def solve(self):
        s = z3.Solver()

        # the board, made up of a list of list of integer variables
        vars = []
        for r in range(self._height):
            row = []
            for c in range(self._width):
                v = z3.Int("c%sr%s" % (c, r))

                # 0 = black cell
                # 1 = lit up
                # 2 = light
                s.add(z3.Or(v == 0, v == 1, v == 2))

                row.append(v)
            vars.append(row)

        for r, row in enumerate(vars):
            for c, v in enumerate(row):
                if (c, r) in self._black_cells:
                    s.add(vars[r][c] == 0)

                    k = self._black_cells[(c, r)]
                    if k is not None:
                        ns = []
                        for dc, dr in [(0, -1), (1, 0), (0, 1), (-1, 0)]:
                            nc = c + dc
                            nr = r + dr

                            if nc < 0 or nr < 0 or nc >= self._width or nr >= self._height:
                                continue

                            ns.append(vars[nr][nc])

                        s.add(z3.Sum([z3.If(n == 2, 1, 0) for n in ns]) == k)
                else:
                    s.add(v > 0)

                    seen = set()
                    for dc, dr in [(0, -1), (1, 0), (0, 1), (-1, 0)]:
                        for i in range(1, max(self._width, self._height) + 1):

                            nc = c + dc * i
                            nr = r + dr * i

                            if nc < 0 or nr < 0 or nc >= self._width or nr >= self._height:
                                break

                            if (nc, nr) in self._black_cells:
                                break

                            seen.add((nc, nr))

                    # if this is a light, then all seen can not be light, and are lit up
                    for nc, nr in seen:
                        s.add(z3.If(v == 2, 2, 3) > vars[nr][nc])

                    # this is a light, or there must be at least one light in seen
                    s.add(z3.Or(
                        v == 2,
                        z3.Sum([z3.If(vars[nr][nc] == 2, 1, 0) for nc, nr in seen]) > 0
                    ))


        # solve
        if s.check() == z3.sat:
            m = s.model()

            r = [[m.evaluate(vars[r][c]) for c in range(self._width)] for r in range(self._height)]
            return r
        else:
            return None

    def pretty_print(self, solution):
        if solution is None:
            print("No solution")
            return

        for r, row in enumerate(solution):
            s = ""
            for c, v in enumerate(row):
                if (c, r) in self._black_cells:
                    k = self._black_cells[(c, r)]
                    if k is None:
                        s += "-"
                    else:
                        s += str(k)
                elif v == 2:
                    s += "I"
                elif v == 1:
                    s += "."
                else:
                    s += "!"

            print(s)
