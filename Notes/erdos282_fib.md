# Erdos282.erdos_282.variants.fibonacci

- Source: `FormalConjectures/ErdosProblems/282.lean:81` (category textbook)
- Statement: for x ∈ (0,1) ∩ ℚ, `greedyUnitFractionRem .univ x =ᶠ[atTop] 0` (the Fibonacci–Sylvester greedy algorithm terminates).

Proof idea: strong induction on the numerator k of x = k/q, using the invariant "A contains
every n with 1/x ≤ n" (true for A = univ). Under that invariant the greedy choice is
N = ⌈1/x⌉₊ (`sInf_eq`). From q ≤ Nk < q + k and k < q, the new remainder
x − 1/N = (Nk − q)/(qN) has a numerator Nk − q < k and satisfies x − 1/N < 1/N. So every n
with 1/(x − 1/N) ≤ n is > N and ≥ 1/x, and the invariant holds for A \ {N}. Once the
remainder is ≤ 0 the sequence stays 0 (`zero_of_nonpos`). One unfolding step (`step`)
connects index t+1 to the recursive call. The definition is restated locally, with targeted
Mathlib imports instead of FormalConjecturesUtil.

Axioms: `'Erdos282.erdos_282.variants.fibonacci' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-30. Compiles: 2 (1st clean except an unused `ring`).
