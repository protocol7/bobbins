from solver import Solver

# https://www.youtube.com/watch?v=63CHpW3HPno

for k in (7, 8, 12, 13):

    s = (
        Solver(Solver.EMPTY)
        .thermo([(3, 0), (3, 1), (3, 2), (2, 3)])
        .thermo([(7, 1), (7, 2), (7, 3)])
        .thermo([(5, 4), (6, 4), (7, 5)])
        .thermo([(2, 5), (3, 5)])
        .thermo([(5, 5), (6, 6)])
        .thermo([(2, 7), (3, 7)])

        .white_kropkis([
            [(0, 1), (1, 1)],
            [(5, 2), (5, 3)],
            [(4, 5), (4, 6)],
            [(7, 7), (8, 7)],
        ])

        .killer_cage([(0, 0), (0, 1)], k)
        .killer_cage([(1, 0), (1, 1)], k)
        .killer_cage([(2, 0), (3, 0)], k)
        .killer_cage([(3, 1), (3, 2)], k)
        .killer_cage([(0, 2), (0, 3)], k)
        .killer_cage([(4, 2), (5, 2)], k)
        .killer_cage([(1, 3), (2, 3)], k)
        .killer_cage([(5, 3), (5, 4)], k)
        .killer_cage([(2, 4), (2, 5)], k)
        .killer_cage([(6, 4), (7, 4)], k)
        .killer_cage([(3, 5), (4, 5)], k)
        .killer_cage([(7, 5), (7, 6)], k)
        .killer_cage([(4, 6), (4, 7)], k)
        .killer_cage([(5, 7), (6, 7)], k)
        .killer_cage([(7, 7), (7, 8)], k)
        .killer_cage([(8, 7), (8, 8)], k)
    )

    solution = s.solve()

    Solver.pretty_print(solution)
    print("")
