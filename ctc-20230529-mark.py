from solver import Solver
from utils import flatten
import z3

# https://www.youtube.com/watch?v=6dEauzpAwGo

RENBANS = [
    [(0, 0), (1, 1), (0, 2)],
    [(3, 1), (4, 0), (5, 1)],
    [(8, 0), (7, 1), (8, 2)],
    [(0, 3), (1, 4)],
    [(0, 6), (1, 7), (0, 8)],
    [(4, 7), (4, 8)],
    [(8, 6), (7, 7), (8, 8)],
]

def indexing(s, vars):
    def index(c, row):
        return z3.If(c == 0, row[0],
                     z3.If(c == 1, row[1],
                           z3.If(c == 2, row[2],
                                 z3.If(c == 3, row[3],
                                       z3.If(c == 4, row[4],
                                             z3.If(c == 5, row[5],
                                                   z3.If(c == 6, row[6],
                                                         z3.If(c == 7, row[7], row[8]))))))))

    for c, r in flatten(RENBANS):
        v = vars[r][c]
        rs = [vars[r][i] for i in range(9)]

        print(index(v - 1, rs) == c + 1)
        s.add(index(v - 1, rs) == c + 1)


solver = (
    Solver()
    .killer_cage([(0, 5), (0, 6)], 6)
    .killer_cage([(8, 5), (8, 6)], 14)
    .odds([(6, 1)])
    .renban_lines(RENBANS)
    .extra_constraint(indexing)
)

solution = solver.solve()

Solver.pretty_print(solution)
