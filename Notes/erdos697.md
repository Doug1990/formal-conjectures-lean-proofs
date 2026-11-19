# Erdős 697: density_exists and variants.delta_lt

- Statements: `Erdos697.density_exists` and `Erdos697.erdos_697.variants.delta_lt`
- Source: `FormalConjectures/ErdosProblems/697.lean` (lines 39 and 52), both `category research solved`
- Verified file: `work/erdos697_dens.lean`; `results/erdos697.lean` is an identical copy. The statements are unchanged. `δ` is defined exactly as in the source (`(density_exists m α).choose`). `HasDensity`/`partialDensity` are restated locally from FormalConjecturesForMathlib/Data/Set/Density.lean.

**Proof idea.** Every admissible d satisfies 1 < d < X = exp(m^α), so d divides L = ⌈X⌉₊!. This makes the set periodic with period L. Shifting the counting window by L adds the per-period count c, so count(N) = ⌊N/L⌋·c + O(L). The square of the error is ≤ L²·N, so the generic `dens_of_sq` lemma gives density c/L. For `delta_lt`: δ = c/L by uniqueness of limits. A union bound over the multiples of each d ∈ D gives c/L ≤ Σ_{d∈D} 1/d. When D ≠ ∅ this is strictly less than Σ 1/(d−1). Reindexing d = mk + 1 (injectively into 1 ≤ k ≤ ⌊X/m⌋) bounds it by H_K/m. Then H_K ≤ 1 + log K ≤ 1 + m^α − log m ≤ 1 + m^α. When D = ∅ the density is 0 < (m^α+1)/m.

Axioms (both): `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-11
