# Bobbins

z3 based variant Sudoku solver. Also includes some example Cracking the Cryptic puzzles.

Supports the following features:

* Any set of digits (default 1-9)
* Any sized grid
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
* Entropic lines
* Odd/even cells
* Renban lines
* Nabner lines
* Palindroms
* Between lines
* Quadruples
* Xsums

Also supports adding custom constraints per solve. There are a fair amount of examples of these, e.g 10 sum lines, magic squares and thripples.

## TODO

* Modular lines
