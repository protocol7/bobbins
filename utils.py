import z3

ORTHOGONAL = [(0, -1), (1, 0), (0, 1), (-1, 0)]
CORNERS = [(-1, -1), (-1, 1), (1, -1), (1, 1)]
ADJACENT = ORTHOGONAL + CORNERS
ADJACENT_WITH_CELL = ADJACENT + [(0, 0)]


def orthogonal(grid, c, r) -> tuple[int, int]:
    return _neighbours(grid, c, r, ORTHOGONAL)


def adjacent_with_cell(grid, c, r) -> tuple[int, int]:
    return _neighbours(grid, c, r, ADJACENT_WITH_CELL)


def _neighbours(grid, c, r, neighbours) -> tuple[int, int]:
    for dc, dr in neighbours:
        cc = c + dc
        rr = r + dr

        if cc < 0 or rr < 0 or cc >= len(grid[0]) or rr >= len(grid):
            continue

        yield cc, rr

def z3_count(predicate, vs):
    return z3.Sum([z3.If(predicate(v), 1, 0) for v in vs])
