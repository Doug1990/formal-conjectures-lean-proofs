# Erdős 292 variants: mul, two_mul, prime_pow

- Statements: `Erdos292.erdos_292.variants.mul`, `Erdos292.erdos_292.variants.two_mul`, `Erdos292.erdos_292.variants.prime_pow`
- Source: `FormalConjectures/ErdosProblems/292.lean` lines 71, 81, 76 (all `category research solved`)
- The definition `A` is restated verbatim in the namespace. Targeted imports are used instead of FormalConjecturesUtil.

Proof idea. `mul` (Straus): if Σ_{S} 1/a = 1 with max m, and Σ_{T} 1/b = 1 with max n, then (S∖{m}) ∪ m·T works. The two parts are disjoint, because elements of S∖{m} are < m ≤ m·t. The sum is (1 − 1/m) + (1/m)·1, and the maximum is mn. `two_mul` (van Doorn): {2} ∪ 2·S. Here 1 ∉ S, since otherwise the sum would be ≥ 1 + 1/n > 1, so 2 ∉ 2·S. `prime_pow`: for n = p^k, every other a ∈ S satisfies a < p^k, so v_p(a) ≤ k−1. The p-adic norm of their reciprocal sum is then ≤ p^(k−1) (non-archimedean, `padicNorm.sum_le'`). But 1/p^k = 1 − Σ' has norm p^k, which is a contradiction.

Axioms (each of the three): `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-10. 3 compiles (1: positivity not loaded, a no-progress simp, wrong argument to `Nat.pow_lt_pow_iff_right`; 2: clean; 3: clean + axioms).
