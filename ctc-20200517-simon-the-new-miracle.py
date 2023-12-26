from solver import Solver

# https://www.youtube.com/watch?v=Tv-48b-KuxI

given = (
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 4, 0, 0, 0, 0),
    (0, 0, 3, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 0, 0, 0, 0),
)


s = (
    Solver(given)
    .anti_king()
    .anti_knight()
    .anti_consecutive()
)
solution = s.solve()

Solver.pretty_print(solution)
