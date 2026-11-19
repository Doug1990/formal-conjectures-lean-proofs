# Erdos1063.erdos_1063.variants.exists_exception

- Statement: for `2 ≤ k` and `2k ≤ n`, some `n - i` with `i < k` does not divide `C(n, k)` (Erdős–Selfridge). Category research solved.
- Source: `FormalConjectures/ErdosProblems/1063.lean:93` in the checkout
- Proof idea: the partial-fraction identity `∑_{j≤m} (-1)^j C(m,j)/(y+j) = m!/∏_{j≤m}(y+j)` (lemma `pf`), proved by induction on `m` via Pascal's rule. On the left this gives `F(m+1,y) = F(m,y) − F(m,y+1)`, and the right side satisfies the same recurrence. Take `m = k−1` and `y = a = n−k+1`. The product is `n.descFactorial k = k!·C(n,k)`, so `C(n,k)·∑ = 1/k`. If every `a+j = n−(m−j)` divided `C(n,k)`, then `C(n,k)·∑ = ∑ (-1)^j C(m,j)·q_j` would be an integer `z` with `z·k = 1`, which is impossible for `k ≥ 2`. The proof only uses `k ≤ n`, not `2k ≤ n`.
- Axioms: `propext, Classical.choice, Quot.sound`
- Compiles: 3 (1: `Finset.prod_range_reflect` needs import Mathlib.Algebra.BigOperators.Intervals; 2: a no-op `simp only at r`; 3: clean + axioms)
- Reusable: `pf` (alternating binomial partial fractions over ℚ)
- Date: 2026-11-03
