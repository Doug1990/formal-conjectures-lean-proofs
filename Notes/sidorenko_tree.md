# sidorenko_tree

- Statement: `SidorenkoConjecture.sidorenko_tree` (category research solved, Sidorenko 1993)
- Source: `FormalConjectures/Wikipedia/SidorenkoConjecture.lean:736` in the checkout (upstream proof is `sorry` beyond the subsingleton case)
- Verified file: `work/sidtree_a.lean` (5 compiles). `results/sidorenko_tree.lean` is a hand-written copy of it and was not compiled separately.
- `homCount` / `homDensity` are restated locally (same definitions as FormalConjecturesForMathlib), as in the earlier Sidorenko results.

## Proof idea
Root the tree at r and order its vertices by distance from r (`Tuple.sort`). Each vertex other than the root then has a unique parent with a smaller index (tree path uniqueness via `IsAcyclic.subsingleton_path`). Every edge of H is a parent–child pair, so tuples `f : Fin (n+2) → W` that respect all parent edges give injective homomorphisms H →g G. On these tuples put the tree-indexed Markov chain weight P(f) = d(f₀)/D · ∏ 1[f_par ~ f_j]/d(f_par). By leaf-peeling induction (`Fin.snoc`), P is a probability distribution whose one-vertex marginals are all stationary (d/D). Its entropy is therefore log D + n·Σ(d/D)log d. Gibbs' inequality (log-Jensen) bounds the entropy by log #support ≤ log hom(H,G). Jensen for x log x gives Σ(d/D)log d ≥ log(D/N). Together, hom(H,G) ≥ D(D/N)^n = N^{n+2}·(D/N²)^{n+1}, which is exactly t(K₂,G)^{e(H)} ≤ t(H,G) because e(H) = n+1.

## Axioms
`'SidorenkoConjecture.sidorenko_tree' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-03
