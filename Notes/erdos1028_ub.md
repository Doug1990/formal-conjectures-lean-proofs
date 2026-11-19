# erdos1028_ub

- Statement: `Erdos1028.erdos_1028.variants.upper_bound` (H(n) ≪ n^{3/2}), checkout file `FormalConjectures/ErdosProblems/1028.lean:77`, tag `research solved` (Erdős Er63d).
- `≪` is written out as `=O[atTop]` (IsBigO atTop), the same convention as earlier results. `imbalance` and `H` are restated verbatim, with targeted Mathlib imports.

## Proof idea
The proof is deterministic and needs no probability. Use the Sylvester–Hadamard colouring f(x,y) = (−1)^{popcount(x AND y)}, written as h(φx, φy) with φx = the first k bits of x and k = log₂ n + 1, so that n < 2^k ≤ 2n. The rows of the 2^k × 2^k matrix h are orthogonal: the sum over v factors as a product over the bits (`Fintype.prod_sum`). Lindsey's lemma follows by Cauchy–Schwarz plus orthogonality: for X ⊆ [1,n] (φ is injective there), (Σ_{x,y∈X} f)² ≤ |X|²·2^k ≤ 2n³. Because f is symmetric, the full double sum equals 2·(sum over x<y) plus the diagonal, and the diagonal has absolute value ≤ |X| ≤ n. So imbalance ≤ ⌊√(n²2^k)⌋ + n, and H(n) ≤ 2n^{3/2} + n ≤ 3n^{3/2} for n ≥ 1.

## Axioms
`'Erdos1028.erdos_1028.variants.upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-13
