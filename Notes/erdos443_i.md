# Erdos443.erdos_443.parts.i

- Source: FormalConjectures/ErdosProblems/443.lean:52 (category research solved; Hegyvári 2025 / Cambie)
- Statement: ∀ s, ∃ m n, n < m ∧ s ≤ #(A n ∩ A m), where A m = {k(m−k) : 1 ≤ k ≤ m/2}.
- Date: 2026-11-12. Compiles: 2. Verified file: work/erdos443_i.lean (results/erdos443_i.lean is an identical copy).

Proof idea: let D = (2p+1)(2q+1) with 1 ≤ p ≤ q. Then 4pq(p+1)(q+1) = 2pq·(D+1−2pq) = (2pq+2p)·(D−1−(2pq+2p)),
so this value lies in A(D−1) ∩ A(D+1) (lemma H.mem). Take D = 3^(2s+1), m = D+1, n = D−1, and the s factorizations
3^i · 3^(2s+1−i), i = 1..s. Distinct factorizations give distinct values (H.injZ / H.injN): equal values plus equal
products force pq and p+q to agree, so p = p'. The identity injection i ↦ value then gives at least s common elements.
Def A is restated locally (same definition as in the source). The `@[category]` attribute is dropped.

Axioms: `'Erdos443.erdos_443.parts.i' depends on axioms: [propext, Classical.choice, Quot.sound]`
