# VCDimConvex.exists_convex_rn_add_two_vc_n_forall_not_hasAddVCNDimAtMost

- Source: `FormalConjectures/Other/VCDimConvex.lean:54` (category research solved)
- Statement: `∀ n, ∃ C : Set (Fin (n + 2) → ℝ), Convex ℝ C ∧ ∀ d, ¬ HasAddVCNDimAtMost C n d`
- Lean file: `results/vcn_shatter.lean`. The statement is unchanged. `HasAddVCNDimAtMost` is restated locally, as the additive form of `HasMulVCNDimAtMost` in `FormalConjecturesForMathlib/Combinatorics/Additive/VCDim.lean`.

## Proof idea
This generalises the paraboloid construction from `vc3_shatter`. The proof works in W = ℝ × ℝ^(n+1), with P(e) = (|e|², e). Fix an injection q : Set (ℕⁿ) → ℝ, which exists by cardinality, and let C = conv{P(V(a, q T)) : a ∈ T}. Here V(a, r) ∈ ℝ^(n+1) has coordinates a₀, …, a_{n−1}, r.

For each d, take x_k(j) = (j², j·e_k) and y_s = (q(T_s)², q(T_s)·e_n), where T_s is the image of s in ℕⁿ. Cross terms vanish because the supports are disjoint, so y_s + Σ_k x_k(i_k) = P(V(i, q T_s)).

If i ∉ s, the point P(V(i, q T_s)) differs from every generator, because V and q are injective. The open half-space {w₁ − 2⟨p, w₂⟩ > −|p|²} contains every other paraboloid point, is convex, and has P(p) on its boundary. So P(V(i, q T_s)) is not in C. The set C is the same for every d.

Finally, the linear equivalence `Fin.consLinearEquiv` moves C to `Fin (n+2) → ℝ`. Convexity and the membership pattern are preserved under the linear equivalence.

## Axioms
`'VCDimConvex.exists_convex_rn_add_two_vc_n_forall_not_hasAddVCNDimAtMost' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date
2026-11-04 (2 compiles)
