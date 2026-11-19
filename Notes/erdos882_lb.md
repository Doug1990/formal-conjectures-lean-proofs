# erdos882_lb

- Statements: `Erdos882.erdos_882.variants.lower_bound` (line 113) and `Erdos882.erdos_882.variants.lower_bound_explicit` (line 131)
- Source: `FormalConjectures/ErdosProblems/882.lean` (both tagged research solved, ELRSS99)
- Date: 2026-11-12

Proof idea: A subset I ⊆ [0,m) of indices has the sum k·2^m − s, where k = |I| and s = Σ_{i∈I} 2^i < 2^m has binary digit sum ν(s) = k. Suppose x₂ = q·x₁. For q = 0 we get x₂ = 0, which is impossible. For q = 1 we get k₁ = k₂ and s₁ = s₂, so I₁ = I₂. For q ≥ 2, write q·s₁ = r + 2^m·t with r < 2^m. Comparing quotient and remainder mod 2^m gives r = s₂ and k₂ + t = q·k₁. Then ν(q s₁) = k₂ + ν(t) (binary concatenation) and ν(q s₁) ≤ ν(q)·k₁. So (q − ν q)·k₁ ≤ t − ν t, with t < q. The function n − ν(n) is monotone and q − ν(q) ≥ 1, which gives a contradiction when k₁ ≥ 2. When k₁ = 1, s₁ = 2^i ≤ 2^(m−1) forces 2t ≤ q, and monotonicity at 2t gives the contradiction. For the explicit bound, m = ⌊log₂ n⌋: A_m ⊆ [1, 2^m − 1] ⊆ [1, n] has m elements and log₂ n < m + 1.

Axioms (both theorems): propext, Classical.choice, Quot.sound
