from solver import Solver

# https://www.youtube.com/watch?v=-tuEhXyXV8s

s = (
        Solver(Solver.EMPTY)
        .thermo([(1, 0), (2, 1), (3, 2), (4, 3), (5, 4), (6, 5), (7, 6)])
        .thermo([(0, 4), (0, 3)])
        .thermo([(8, 4), (8, 3)])
        .white_kropkis(
            [
                ((4, 0), (5, 0)),
                ((3, 4), (4, 4)),
                ((3, 5), (3, 6)),
                ((4, 5), (4, 6)),
                ((5, 5), (5, 6)),
                ((2, 6), (2, 7)),
                ((6, 6), (6, 7)),
                ((7, 6), (7, 7)),
             ]
        )
        .black_kropkis([
            ((1, 6), (1, 7))
        ])
        .entropic_lines([
            [
                (2, 1), (2, 2), (2, 3), (2, 4), (1, 5), (0, 6), (0, 7), (0, 8), (1, 8), (2, 8), (3, 8), (4, 8),
                (5, 8), (6, 8), (7, 8), (8, 8), (8, 7), (8, 6), (7, 5), (6, 4), (6, 3), (6, 2), (6, 1)
             ]
        ])
)
solution = s.solve()

Solver.pretty_print(solution)
