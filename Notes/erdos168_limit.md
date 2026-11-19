# erdos168_limit

- Statement: `Erdos168.erdos_168.variants.limit_exists` (research solved, Graham–Spencer–Witsenhausen).
- Source: `FormalConjectures/ErdosProblems/168.lean:106` in the checkout.
- The statement is unchanged. Instead of `FormalConjecturesUtil` it uses targeted Mathlib imports, with `NonTernary`, `IntervalNonTernarySets`, `F` and `mem_IntervalNonTernarySets_iff` restated verbatim from the checkout.

## Proof idea

Every n ≥ 1 is uniquely m·2^a·3^b with 2 ∤ m and 3 ∤ m (uniqueness comes from `Nat.factorization` at 2 and 3). The triples n, 2n, 3n stay within one chain m, so F(N) = Σ_{m ≤ N, (m,6)=1} g(⌊N/m⌋). Here g(k) is the largest set of exponent pairs (a,b) with 2^a3^b ≤ k that avoids the corner (a,b), (a+1,b), (a,b+1).

Write g as the telescoping sum g(k) = Σ_{j≤k} d_j and swap the order of summation. This gives F(N) = Σ_{j≤N} d_j·c(⌊N/j⌋), where c(y) = #{m ≤ y : (m,6) = 1}, and |3c(y) − y| ≤ 3 by inclusion–exclusion with `Nat.Ioc_filter_dvd_card_eq_div`.

Two facts about d_j: 0 ≤ d_j ≤ 1, and d_j = 0 unless j = 2^a3^b. So Σ d_j/j ≤ Σ 2^{-a}2^{-b} ≤ 4, which makes d_j/j summable.

Each term d_j·c(⌊N/j⌋)/N tends to d_j/(3j) and is bounded by d_j/j. Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) then gives F(N)/N → Σ_j d_j/(3j).

## Axioms

`'Erdos168.erdos_168.variants.limit_exists' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-14
