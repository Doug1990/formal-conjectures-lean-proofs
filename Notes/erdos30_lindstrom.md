# erdos30_lindstrom

- Statement: `Erdos30.erdos_30.variants.lindstrom` (research solved), `FormalConjectures/ErdosProblems/30.lean:88` in the checkout:
  `(h N : ℝ) ≤ √N + N^(1/4) + 1` for every `N`.
- Proof idea: For a Sidon set S ⊆ [1, N] with |S| = k and the interval [0, m], the additive energy E(S, [0,m]) is at most k(m+1) (diagonal a₁ = a₂) plus (m+1)m (off-diagonal: the pair (b₁, b₂) determines the tuple by the Sidon property, and b₁ ≠ b₂). Cauchy–Schwarz (`Finset.le_card_add_mul_addEnergy`) with |S + [0,m]| ≤ N + m gives k²(m+1) ≤ (N+m)(k+m). Take q = N^{1/4}, m + 1 = ⌈q³⌉. The quadratic f(x) = x²(m+1) − (q⁴+m)(x+m) is positive at x₀ = q²+q+1 (explicit expansion q⁵+q⁴+2q³+q²+q+δ(2q²+q+2)−δ² with δ = m+1−q³ ∈ [0,1)) and increasing beyond x₀, so k ≤ x₀ = √N + N^{1/4} + 1. N = 0 is handled separately.
- Axioms: `[propext, Classical.choice, Quot.sound]`
- Date: 2026-10-29
- Compiles: 3 (1: `simp made no progress`; 2: omega on non-reduced projections; 3: clean).
