from solver import Solver

# https://www.youtube.com/watch?v=lgFzP5oPr6c

solver = (
    Solver()
    .anti_knight()
    .black_kropkis([
        [(4, 0), (5, 0)],
        [(6, 0), (6, 1)],
        [(8, 3), (8, 4)],
        [(6, 6), (7, 6)],
        [(6, 6), (6, 7)],
    ])
    .killer_cage([(4, 1), (5, 1), (4, 2), (5, 2), (5, 3), (6, 3), (7, 3), (6, 4), (7, 4)], 45)
    .little_killer([(5, 0), (4, 1), (3, 2), (2, 3), (1, 4), (0, 5)], 32)
    .little_killer([(0, 4), (1, 5), (2, 6), (3, 7), (4, 8)], 23)
    .arrows([
        [(3, 4), (2, 3)],
        [(3, 5), (2, 4)],
        [(3, 5), (4, 4), (4, 3), (5, 4)],
        [(3, 5), (2, 5), (1, 5), (0, 5)],
        [(3, 5), (3, 6), (3, 7), (3, 8)],
        [(3, 5), (4, 6)],
        [(7, 5), (8, 6)],
    ])
)

solution = solver.solve()

Solver.pretty_print(solution)
