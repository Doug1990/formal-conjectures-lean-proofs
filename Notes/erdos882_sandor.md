# erdos882_sandor

- Statement: `Erdos882.erdos_882.variants.sandor` (category research solved)
- Source: `FormalConjectures/ErdosProblems/882.lean:141` in the checkout
- Date: 2026-11-12

Proof idea: write N = m·2^m. A subset of A = {2^i + N : i < m} comes from an index set I ⊆ [0,m), and its sum is |I|·N + s with s = Σ_{i∈I} 2^i < 2^m ≤ N. The number of binary 1-digits of s, ν(s), equals |I| (via `Finset.toFinset_bitIndices_sum_two_pow`), and different I give different s (`Finset.geomSum_injective`). Suppose (k₁N+s₁)·q = k₂N+s₂. For q = 1 the bound s < N forces k₁ = k₂, s₁ = s₂, so the subsets are equal. For q ≥ 2 compare q·k₁ with k₂. If q·k₁ > k₂ the left side is too large. If q·k₁ < k₂ then q ≤ m and q·s₁ ≥ N = m·2^m > q·s₁, a contradiction. If q·k₁ = k₂ then q·s₁ = s₂, and ν(s₂) = q·ν(s₁). But the self-proved bounds ν(a+b) ≤ ν(a)+ν(b), ν(qs) ≤ ν(q)ν(s) and ν(q) < q for q ≥ 2 rule this out. The hypothesis 1 ≤ m is not needed.

Axioms: `'Erdos882.erdos_882.variants.sandor' depends on axioms: [propext, Classical.choice, Quot.sound]`

Imports: Mathlib.Combinatorics.Colex, Mathlib.Data.Nat.BitIndices, Mathlib.Tactic.Ring, Mathlib.Tactic.Linarith. Reusable: SD.nu (binary digit sum) with nu_add, nu_mul_le, nu_lt, nu_card.
