# Green40.green_40.sanity_f_one

- Source: `FormalConjectures/GreensOpenProblems/40.lean:69` (category research solved; f(1) = 1 via Hamming codes)
- Statement: `f 1 = 1`, where `f r = liminf_n minDensity n r` and `minDensity` is the infimum over covering subspaces V ≤ 𝔽₂ⁿ (V + H(r) = 𝔽₂ⁿ) of |V|·|H(r)|/2ⁿ.

## Proof idea
Lower bound: for every covering subspace the map V × H(1) → 𝔽₂ⁿ, (v,h) ↦ v+h, is surjective, so 2ⁿ ≤ |V|·|H(1)| and every density is ≥ 1. Then `le_liminf_of_le` gives 1 ≤ f 1.
Upper bound: for n = 2ᵏ − 1, fix a bijection σ from Fin n onto the nonzero vectors of 𝔽₂ᵏ. Let the Hamming code V be the kernel of the syndrome map x ↦ Σ xᵢσ(i). V covers: if the syndrome of x is σ(i), subtract eᵢ. Vectors of weight ≤ 1 are 0 or some eᵢ, so they have pairwise distinct syndromes. That makes (v,h) ↦ v+h injective, so |V|·|H(1)| ≤ 2ⁿ. Since 2ᵏ − 1 ≥ k, this holds frequently, and `liminf_le_of_frequently_le'` gives f 1 ≤ 1. The size of the Hamming ball is never computed.

Reusable: `syn`, `syn_single`, `small` (weight ≤ 1 vectors over ZMod 2), `cover`, `inj`, `one_le` (minDensity n 1 ≥ 1).

Axioms: `'Green40.green_40.sanity_f_one' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-31. Compiles: 2 (1st clean, 2nd with #print axioms). Defs restated locally (𝔽 / 𝔽₂ abbrevs from FormalConjecturesForMathlib/Data/ZMod/Fp.lean), targeted imports.
