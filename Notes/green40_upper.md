# Green40.green_40.upper_bound

- Source: `FormalConjectures/GreensOpenProblems/40.lean:74` (category research solved; f(r) ≤ rʳ/r!)
- Statement: `f r ≤ (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞)`, where f r = liminf over n of the minimal covering density of linear codes V ≤ 𝔽₂ⁿ with V + H(r) = 𝔽₂ⁿ.

## Proof idea
Generic step: let σ : Fin n → W be such that every w ∈ W is a sum of at most r values σ(i) over distinct i. Then the kernel V of the syndrome map x ↦ Σ xᵢσ(i) is a covering code of radius r (subtract the indicator vector of the representing set). The map (v, w) ↦ v + t(w), with t a section of the syndrome map, is injective, so |V|·|W| ≤ 2ⁿ. The Hamming ball bound is |H_n(r)| ≤ C(n+r, r): inject x ↦ supp(x) ∪ [n, n+r−|supp x|) into the r-subsets of [0, n+r). Then use C(N,r)·r! = descFactorial ≤ Nʳ.
Construction ("block Hamming code"): n = r(2ᵐ−1) and W = (𝔽₂ᵐ)ʳ. The coordinates are in bijection with Fin r × (𝔽₂ᵐ∖0), and σ(j, u) = u placed in block j. Every w is represented with at most r terms, one per nonzero block. Now n + r = r·2ᵐ, so density ≤ C(n+r,r)/2^{rm} ≤ (r·2ᵐ)ʳ/(r!·2^{rm}) = rʳ/r! exactly, for every m. So the bound holds frequently, and `liminf_le_of_frequently_le'` finishes. For r = 0 the same generic step with W = 𝔽₂⁰ gives density ≤ 1 for every n.

Axioms: `'Green40.green_40.upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-31. Compiles: 4 (1: Nat.card rewrite on the wrong subtype, a beta-unreduced injOn hypothesis, Prod.ext direction; 2: `show` before Subtype.ext; 3: clean; 4: + axioms). Defs restated locally, targeted imports.
