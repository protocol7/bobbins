from akari import Solver

# https://www.puzzle-light-up.com/?size=2

s = (
    Solver({
        (5, 0): None,
        (0, 1): 1,
        (4, 1): 0,
        (1, 2): 0,
        (5, 4): 3,
        (2, 5): None,
        (6, 5): 3,
        (1, 6): 2,
    }, width=7, height=7)
)
solution = s.solve()

s.pretty_print(solution)
