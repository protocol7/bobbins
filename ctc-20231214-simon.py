from solver import Solver

# https://www.youtube.com/watch?v=STlbZKN4EtU

DISK = [
    [(-2, -2), (2, 2)],
    [(-1, -2), (1, 2)],
    [(0, -2), (0, 2)],
    [(1, -2), (-1, 2)],
    [(2, -2), (-2, 2)],

    [(-2, -1), (2, 1)],
    [(-1, -1), (1, 1)],
    [(0, -1), (0, 1)],
    [(1, -1), (-1, 1)],
    [(2, -1), (-2, 1)],

    [(-2, 0), (2, 0)],
    [(-1, 0), (1, 0)],
    [(0, 0), (0, 0)],
]

DISKS = [
    (2, 2), (6, 4)
]


def disk(s, cells):
    for dc, dr in DISKS:
        for (dc0, dr0), (dc1, dr1) in DISK:
            v0 = cells[dr + dr0][dc + dc0]
            v1 = cells[dr + dr1][dc + dc1]

            s.add(v0 + v1 == 10)


s = (
    Solver(Solver.EMPTY)
    .killer_cage([(5, 3), (6, 3), (7, 3)], 17)
    .killer_cage([(1, 5), (1, 6)], 8)
    .killer_cage([(5, 6), (5, 7)], 15)
    .killer_cage([(7, 6), (8, 6)], 11)
    .extra_constraint(disk)
)

solution = s.solve()

Solver.pretty_print(solution)
