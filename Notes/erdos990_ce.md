# erdos_990.variants.counterexample

- Statement: `Erdos990.erdos_990.variants.counterexample`, source `FormalConjectures/ErdosProblems/990.lean` (line 117), tagged `research solved` (construction of APSSV26b).
- Verified file: `work/erdos990_ce.lean`. It compiles cleanly with targeted imports and the statement and `M` definition are unchanged. A copy in `results/erdos990_ce.lean` still has to be made (the run ran out of budget before copying).

## Proof idea
For n = 1 take f = 1. For n = m+2, choose exponents e_0 = 0, e_j = K^j (1 ≤ j ≤ m, K = 200n), e_{m+1} = 2^r (r huge). Set the divided-difference weights w_j = 1/∏_{i≠j}(e_j − e_i) and f = Σ_j w_j t^{−e_j} X^{e_j}. Then t^k·f^{(k)}(t) = Σ_j w_j (e_j)_k, which by `Lagrange.coeff_eq_sum` equals the X^{n−1}-coefficient of the falling-factorial polynomial `descPochhammer k`. That is 0 for k ≤ n−2 and 1 for k = n−1, so t > 0 is a root of multiplicity exactly n−1. Choose t so that |c_top| = 2|c_0|. Because the exponents grow fast, each middle coefficient is at most (1+δ)^{n+1}|c_0| (and δ times that for j ≥ 2). The t-factors are ≤ 1+δ because 2^{p} ≤ 1+p for the tiny exponent p. This gives M ≤ (3 + 1.05)/√2 < 3. The polynomial has exactly n nonzero coefficients and c_0 ≠ 0.

## Axioms
`'Erdos990.erdos_990.variants.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-13
