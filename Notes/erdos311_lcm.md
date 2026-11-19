# erdos311_lcm

- Statement: `Erdos311.delta_ge_inv_lcm` (category textbook)
- Source: `FormalConjectures/ErdosProblems/311.lean:65`
- Date: 2026-10-30

Proof idea: let L = lcm(1..N). Every n in A ⊆ [1, N] divides L, so
L·(1 − Σ_{n∈A} 1/n) = L − Σ_{n∈A} L/n is an integer m (`Nat.cast_div`). Hence every element
|1 − Σ 1/n| of the set equals |m|/L. If it is nonzero then m ≠ 0, so |m| ≥ 1 and the element is
at least 1/L. The set is nonempty (A = ∅ gives 1), so `le_csInf` gives δ(N) ≥ 1/L.
The definition of `delta` is restated verbatim with targeted imports.

Axioms: `propext, Classical.choice, Quot.sound`
