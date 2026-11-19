# golo_square

- Statement: `Arxiv.«1609.08688».maximalLength_ge_of_isSquare` (category research solved)
- Source: `FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean:217`
- Statement: for `IsSquare n`, `n.sqrt ^ 3 ≤ maximalLength n` (Gowers–Long, F(n) ≥ n^{3/2} for square n).

Proof idea: write n = k·k. Take all (x, y, z) ∈ [0,k)³ in lexicographic order (a nested `List.flatMap`
over `List.range k`) and map them to the triple (xk+y+1, xk+z+1, yk+z+1) ∈ [1, k²]³. If (x,y,z) <lex (x',y',z'),
then two coordinates strictly increase: coordinates 1 and 2 when x < x', coordinates 1 and 3 when x = x' and y < y',
and coordinates 2 and 3 when only z < z'. All of these come from one lemma: a < b and c < k give ak+c < bk+d.
The list has length k³. `le_csSup` needs the set of lengths to be bounded above. That bound, (n+2)², comes from
the file's own pigeonhole lemma `exists_pair_of_mem_Icc` (copied verbatim), applied with n+2.
The definitions (`lt₂`, `IsIncreasing₂`, `maximalLength`) are restated locally, and the file uses targeted Mathlib imports.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-10-31
