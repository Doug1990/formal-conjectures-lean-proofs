# erdos_1048.variants.pommerenke_ncard_components

- Statement: `Erdos1048.erdos_1048.variants.pommerenke_ncard_components`, source `FormalConjectures/ErdosProblems/1048.lean:67` (category research solved, Pommerenke 1961).
- Proof idea: for f = zⁿ − rⁿ with r > 1, the level set {|f| ≤ 1} is {z : zⁿ ∈ K}, where K is the closed disk of radius 1 around rⁿ. K lies in the half-plane Re > 0, so the principal n-th root ρ(w) = w^(1/n) is continuous on K. With ω a primitive n-th root of unity, the level set is the union of the n pieces Pₖ = ωᵏ·ρ(K), k < n. Every z with zⁿ ∈ K satisfies (z/ρ(zⁿ))ⁿ = 1, so z/ρ(zⁿ) is a power of ω. The pieces are compact (hence closed), connected (continuous images of a convex set) and pairwise disjoint (raise to the n-th power, then use injectivity of k ↦ ωᵏ for k < n). A preconnected set covered by the closed, disjoint sets Pₖ and ⋃_{j≠k} Pⱼ lies in one of them, so every component equals some Pₖ. The set of components is therefore the range of the injective map k ↦ Pₖ on Fin n, which has n elements. `levelSet` from Erdos1043 is restated verbatim locally.
- Axioms: `propext, Classical.choice, Quot.sound`
- Verified file: work/erdos1048_pom.lean (2 compiles). This results copy was written by hand from the verified file and not compiled separately.
- Reusable: Pom.ρ, Pom.P, slit, pow_P, mem_union, disj, comp_eq (components of a finite disjoint union of closed preconnected sets), comps_eq, card.
- Date: 2026-11-05
