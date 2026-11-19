# erdos1033_three_halves

- Statement: `Erdos1033.erdos_1033.variants.three_halves` (research solved). Source: FormalConjectures/ErdosProblems/1033.lean:69. It says that it is not true that every graph on n vertices with more than n²/4 edges has a triangle with degree sum ≥ 3n/2.
- Proof idea: an explicit counterexample with n = 23. Take K_{14,9} (parts {0..13} and {14..22}) and add the perfect matching {2i, 2i+1} inside the 14-part. The 14-part vertices have degree 10 and the 9-part vertices have degree 14, so there are 266/2 = 133 edges and 4·133 = 532 > 529 = 23². The 9-part is independent and the matching has no triangle, so every triangle is a matched pair plus one vertex of the 9-part. Its degree sum is 10+10+14 = 34, and 2·34 = 68 < 69 = 3·23. The degrees are checked by kernel `decide` (23 filter cards). The edge count comes from the handshake lemma, and the triangle case analysis is done with `omega`. This is a simpler family than Erdős–Laskar's: the bipartite graph plus a matching reaches about 1.469n, which is not enough for the 2(√3−1) variant.
- Axioms: `propext, Classical.choice, Quot.sound`
- Date: 2026-11-14
