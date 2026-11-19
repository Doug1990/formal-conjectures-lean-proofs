# Erdos443.erdos_443.parts.ii

- Source: FormalConjectures/ErdosProblems/443.lean:68 (category research solved; Hegyvári 2025 / Cambie)
- Statement: ∀ ε > 0, ∃ n₀, ∀ m n, n₀ < n → n < m → #(A n ∩ A m) < (mn)^ε, where A m = {k(m−k) : 1 ≤ k ≤ m/2}.
- Date: 2026-11-12. Compiles: 3. Verified file: work/erdos443_ii.lean (results/erdos443_ii.lean is an identical copy).

Proof idea: if x = k(m−k) = l(n−l), then u = m−2k and v = n−2l satisfy u² + 4x = m² and v² + 4x = n², so
(u+v)(u−v) = m² − n². The map x ↦ √(m²−4x) + √(n²−4x) = u+v sends A n ∩ A m into the divisors of m² − n². It is
injective, because u+v determines u−v and hence u and x. So #(A n ∩ A m) ≤ τ(m²−n²). The divisor bound
τ(N) ≤ C_ε N^ε is proved from scratch (T.tau_bound): τ(N) = ∏(a_p+1), with (a+1) ≤ (p^a)^ε for p ≥ 2^{1/ε} and
(a+1) ≤ K·(p^a)^ε for all p ≥ 2 (via exp x ≥ 1+x). Then τ(m²−n²) ≤ C m^ε < n^ε m^ε once n^ε > C.
This is the weaker (mn)^{o(1)} form that the formal statement asks for, not the m^{O(1/loglog m)} rate.
Def A is restated locally (same definition as in the source). The `@[category]` attribute is dropped.

Axioms: `'Erdos443.erdos_443.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound]`
