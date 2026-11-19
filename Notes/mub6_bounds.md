# OpenQuantumProblem13.mutuallyUnbiasedBases_dim6_bounds

- Source: `FormalConjectures/OpenQuantumProblems/13.lean:533` (category research solved)
- Statement: `HasMUBs 6 3 ∧ ∀ m : ℕ, HasMUBs 6 m → m ≤ 7` (3 ≤ μ(6) ≤ 7)
- Definitions (UMat, relativeUnitary, IsUnbiased, IsMUBFamily, HasMUBs) are restated verbatim with targeted Mathlib imports. The statement is unchanged. The qubit family (ZU, XU, YU) and its proofs are copied from the source file.

## Proof idea
Lower bound: tensor products. Qubit MUBs {Z, X, Y} (from the source file) and qutrit MUBs {I, F, DF}. The qutrit ones are given as c·ω^{f(k,i)} with exponent tables f : Fin 3 → Fin 3 → Fin 3 and c = √3/3. Entries of U*V are c² times a sum of three cube roots of unity. That sum is 3 (all exponents equal), 0 (all distinct) or has |·|² = 3 (exactly two equal), and the exponent patterns are checked by `decide`. W(U,V) = (U ⊗ₖ V) reindexed by finProdFinEquiv. Its relative unitary is the reindexed Kronecker product of the relative unitaries, so the norms² multiply to (1/2)(1/3) = 1/6. Upper bound, for general d: the projector entries P_{r,i} = e_i^{(r)} e_i^{(r)*} give a linear map L : ℝ^{m×d} → ℝ^{d×d}. It sends c ↦ the real coordinates (Re above the diagonal, Im below) of the Hermitian matrix Σ c P, and those coordinates are injective on Hermitian matrices. Pairing with P_{s,j} gives Σ_x c_x |⟨e,f⟩|² = 0. Unbiasedness makes these coefficients independent of j except at x = (s,j), so a kernel vector c is constant along each basis and dim ker ≤ m. Rank–nullity gives md ≤ d² + m. For d = 6 that is 5m ≤ 36, so m ≤ 7.

## Axioms
`'OpenQuantumProblem13.mutuallyUnbiasedBases_dim6_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date
2026-11-05. Verified file: work/mub6_lower.lean (clean compile). This results copy was written by hand from that file and was not compiled separately.
