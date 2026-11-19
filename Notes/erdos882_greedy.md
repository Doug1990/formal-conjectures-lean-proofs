# erdos882_greedy

- Statement: `Erdos882.erdos_882.variants.greedy` (category research solved)
- Source: `FormalConjectures/ErdosProblems/882.lean:149` in the checkout
- Date: 2026-11-12

Proof idea: this does not use the greedy algorithm. It reuses Sándor's construction, which is proved in the same file (`erdos_882.variants.sandor`, see erdos882_sandor.md). For n ≥ 32 let m be the least integer with n < (m+2)·2^(m+1). Then m ≥ 3 and (m+1)·2^m ≤ n. So the set {2^i + m·2^m : i < m} lies in [1, n], has m elements and is a subset-sum antichain, which gives m ≤ maxAntichainCard n (`le_csSup`, bounded by n). By induction, (k+2)·2^(k+1) ≤ 3^(k+1) for k ≥ 3, so n ≤ 3^(m+1). Hence logb 3 n ≤ m + 1, i.e. logb 3 n − 1 ≤ m ≤ maxAntichainCard n. The construction actually gives the stronger (1−o(1))·log₂ n.

Axioms: `'Erdos882.erdos_882.variants.greedy' depends on axioms: [propext, Classical.choice, Quot.sound]`

Imports: Mathlib.Combinatorics.Colex, Mathlib.Data.Nat.BitIndices, Mathlib.Tactic.Ring, Mathlib.Tactic.Linarith, Mathlib.Analysis.SpecialFunctions.Log.Base.
