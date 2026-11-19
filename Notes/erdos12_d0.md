# erdos12_d0

- Statement: `Erdos12.erdos_12.variants.erdos_sarkozy_density_0` (good sets have natural density 0; Erdős–Sárközy [ErSa70])
- Source: `FormalConjectures/ErdosProblems/12.lean:95` (category research solved)
- The definitions `Set.partialDensity`, `Set.HasDensity` (from FormalConjecturesForMathlib/Data/Set/Density.lean) and `Erdos12.IsGood` are restated verbatim. The statement itself is unchanged.

## Proof idea
This is a density-increment argument. I derived it myself and did not consult the paper. Suppose `|A ∩ [0,N)| > εN` for infinitely many N. Then keep a subset S ⊆ A \ {0} whose elements all lie in one residue class mod m, with `ε(3/2)^k N ≤ m·|S ∩ [0,N)|` for infinitely many N. For a step, pick a ∈ S and let g = gcd(m,a). Every element of S above a is ≡ 0 mod g, so it lies in one of the a/g classes t mod a with g | t. For each such t, the classes t and −t mod a cannot both contain elements of S above a, because a | b+c would contradict goodness. A self-paired class contains at most one element. Summing over the involution t ↦ (a−t) % a gives 2·Σ_t c_t ≤ (a/g)(B+1). So if every class satisfied lcm(m,a)·c_t < (3/2)·ε(3/2)^k N from some N on, the count of S would be too small. Hence some class S_t, which lies in one class mod lcm(m,a) = m·(a/g), gains the factor 3/2 infinitely often (pigeonhole via `Filter.eventually_all_finset`). A set inside one class mod m has at most N/m + 1 elements below N, which bounds the relative density by 1 + o(1). This contradicts (3/2)^k ε/2 ≥ 2 for large k.

## Axioms
`'Erdos12.erdos_12.variants.erdos_sarkozy_density_0' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date
2026-11-14 (4 compiles)
