from akari import Solver

# https://www.puzzle-light-up.com/?size=2

s = (
    Solver({
        (5, 0): 2,
        (0, 1): 0,
        (2, 1): 0,
        (5, 2): 1,
        (1, 4): 3,
        (4, 5): 2,
        (6, 5): 2,
        (1, 6): None,
    }, width=7, height=7)
)
solution = s.solve()

s.pretty_print(solution)
