# erdos1121

- Statements: `Erdos1121.erdos_1121` and `Erdos1121.erdos_1121.variants.higher_dimension`
- Source: FormalConjectures/ErdosProblems/1121.lean:49 and :63 (research solved, Goodman–Goodman GoGo45)
- Date: 2026-11-17

Proof idea: the centre is the weighted mean z = (Σ rᵢcᵢ)/Σ rᵢ, and the argument works in any real inner product space (`GG.cover`). Fix p in ball i and put v = p − z. Project onto v: xⱼ = ⟪v,cⱼ⟫ and ρⱼ = ‖v‖rⱼ. Cauchy–Schwarz shows that a value t outside every interval [xⱼ−ρⱼ, xⱼ+ρⱼ] gives a hyperplane missing every ball, so the hypothesis says no such t separates the centres. The 1D lemma `GG.oned` gives S(xᵢ+ρᵢ) ≤ Σρⱼxⱼ + S². To prove it, let R be the maximal right endpoint. The gap R − eⱼ is covered by the intervals whose right ends are larger (`GG.gap`, via Lebesgue measure of Ioc ⊆ ⋃ Icc). Then Σρⱼ(R−xⱼ) ≤ Σρⱼ² + 2Σ_{eⱼ<eₗ}ρⱼρₗ ≤ S² (`GG.pair`). Dividing by ‖v‖S gives ⟪v,cᵢ⟫ − ⟪v,z⟫ + ‖v‖rᵢ ≤ ‖v‖S, and ‖v‖² = ⟪v,p−cᵢ⟫ + ⟪v,cᵢ−z⟫ ≤ ‖v‖S, so ‖p − z‖ ≤ Σrᵢ.

Axioms (both): [propext, Classical.choice, Quot.sound]
