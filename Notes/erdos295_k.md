# Erdos295.exists_k

- Source: `FormalConjectures/ErdosProblems/295.lean:37` (category textbook)
- Statement: for every N there are k and N ≤ n_1 < … < n_k with Σ 1/n_i = 1 (in ℝ).

Proof idea: WLOG N ≥ 2. Since Σ_{i∈[N,2N)} 1/i ≥ 1/2, the harmonic block over [N,4N) is ≥ 1, so there is a least m+1 with Σ_{[N,m+1)} 1/i ≥ 1; then H = Σ_{[N,m)} 1/i < 1 and r = 1 − H ≤ 1/m < 1/(m−1). Write r = a/b and expand it with the Fibonacci–Sylvester greedy algorithm (lemma `egypt`, strong induction on the numerator: n = ⌊b/a⌋+1, a/b − 1/n = (na−b)/(nb) with smaller numerator), giving distinct denominators ≥ m, disjoint from [N,m). The resulting Finset is enumerated by `Finset.orderEmbOfFin` (strictly monotone) and the ℚ sum is cast to ℝ.

Axioms: `'Erdos295.exists_k' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-30
