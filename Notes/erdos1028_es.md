# erdos1028_es

- Statements: `Erdos1028.erdos_1028.variants.erdos_spencer` (n^{3/2} ≪ H(n), ErdosProblems/1028.lean:83, research solved, ErSp71) and `Erdos1028.erdos_1028` (H(n) = Θ(n^{3/2}), ErdosProblems/1028.lean:60, research solved).
- Source: formal-conjectures/FormalConjectures/ErdosProblems/1028.lean (defs `imbalance`, `H` restated verbatim; Mathlib-only targeted imports).
- File: results/erdos1028_es.lean (identical to work/erdos1028_es.lean, which compiled cleanly).

## Proof idea
Erdős–Spencer, with no probability. Split [1,n] into U = [1,m] and W = [m+1,2m] (m = ⌊n/2⌋). For a ±1 row a and all sign vectors ε ∈ {±1}^m, T = Σ a_i ε_i satisfies Σ_ε T² = m·2^m and Σ_ε T⁴ = (3m²−2m)·2^m (`ES.mom`, by induction over `Fin.consEquiv` with a shift parameter c). The pointwise truncation K²T² ≤ K³|T| + T⁴ with K = 3√m gives Σ_ε |T| ≥ (2/9)√m·2^m (`ES.avg`, a discrete Khintchine bound). Averaging over the rows u ∈ U gives an ε with Σ_u |T_u(ε)| ≥ (2/9)m^{3/2}. Splitting U by the sign of T_u and W by ε gives a block V × W' with 4|Σ_{V×W'} f| ≥ Σ_u |T_u| (`ES.block_gen`). Since V < W', S(V∪W') = S(V) + S(W') + cross (`ES.S_union`), so the cross sum is ≤ 3·(max imbalance) (`ES.cross`). Hence n√n ≤ 324·H(n) for n ≥ 2. The Θ statement combines this with the earlier Sylvester–Hadamard upper bound (copied from results/erdos1028_ub.lean).

## Axioms
'Erdos1028.erdos_1028.variants.erdos_spencer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1028.erdos_1028' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-14
