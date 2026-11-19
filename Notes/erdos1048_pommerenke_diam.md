# Erdos1048.erdos_1048.variants.pommerenke_diam_tendsto_zero

- Source: `FormalConjectures/ErdosProblems/1048.lean:78` (category research solved, Pommerenke 1961)
- Verified file: `work/erdos1048_diam.lean`. This results copy was written by hand from that file and not compiled separately.
- Date: 2026-11-05

**Proof idea.** For f = Xⁿ − rⁿ, the level set {|f| ≤ 1} is the union of the n pieces ωᵏ·ρ(B), where B is the closed ball of radius 1 around R = rⁿ and ρ(w) = w^(1/n) is the principal root. Earlier work (pommerenke_ncard_components) shows these pieces are exactly the connected components. Rotation by ωᵏ is an isometry, so the diameter of a component is at most the diameter of ρ(B). On B we have |w| ≥ rⁿ − 1 and |ρ(w)|ⁿ = |w| ≤ rⁿ + 1 ≤ (2r)ⁿ, so ρ'(w) = (1/n)·ρ(w)/w has norm at most 2r/(n(rⁿ − 1)). The mean value theorem on the convex ball B (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) then bounds the diameter by 4r/(n(rⁿ − 1)) ≤ 4r/(n(r − 1)), which is < ε once n > 4r/((r − 1)ε).

Axioms: `[propext, Classical.choice, Quot.sound]`
