# Erdos1048.erdos_1048 (main statement)

- Source: `FormalConjectures/ErdosProblems/1048.lean:55` (category research solved, question; the answer is "no", Pommerenke 1961)
- Lean file: `results/erdos1048_pommerenke_diam.lean`, which also contains pommerenke_diam_tendsto_zero. The verified file is `work/erdos1048_diam.lean`. The results copy was written by hand from it and not compiled separately.
- Date: 2026-11-05

**Proof idea.** Take r = 3/2 and ε = 2 − r = 1/2. By pommerenke_diam_tendsto_zero, there is an n for which every connected component of the closed level set {|Xⁿ − rⁿ| ≤ 1} has ediam < 1/2. The polynomial f = Xⁿ − rⁿ is monic of degree n ≥ 1, and all its roots satisfy |z| = r. The open level set lies inside the closed one, so each of its connected components is preconnected and contained in the closed-set component through the same point (`IsPreconnected.subset_connectedComponentIn`). By `Metric.ediam_mono`, that component also has ediam < 1/2 = 2 − r, which contradicts the universal claim.

Axioms: `[propext, Classical.choice, Quot.sound]`
