import z3

ORTHOGONAL = [(0, -1), (1, 0), (0, 1), (-1, 0)]


def orthogonal(grid, c, r):
    for dc, dr in ORTHOGONAL:
        cc = c + dc
        rr = r + dr

        if cc < 0 or rr < 0 or cc >= len(grid[0]) or rr >= len(grid):
            continue

        yield cc, rr


def z3_count(predicate, vs):
    return z3.Sum([z3.If(predicate(v), 1, 0) for v in vs])
