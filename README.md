# Bobbins

z3 based variant Sudoku solver. Also includes some example Cracking the Cryptic puzzles.

Supports the following constraints:

* Given digits
* Regular/irregular regions
* Non-repeating diagonals
* X/V
* Kropki (TODO: anti-Kropki)
* Thermos, including slow thermos
* Arrows
* Region sum lines
* Whisper lines
* Zipper lines
* Small than
* Killer cages (with or without sum, with or without uniqueness)
* Little killers
* Anti-knight
* Anti-king
* Anti-consecutive (orthogonal cells can not be consecutive)
* Disjoint sets (cells in the same position in a region can not have the same digits)

## TODO

* Non-9x9 grid
* Odd/even cells
* Modular lines
* Entropic lines
