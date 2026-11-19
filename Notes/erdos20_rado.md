# erdos20_rado

- Statement: `Erdos20.erdos_20.variants.erdos_rado_bound` (category research solved, Erdős–Rado 1960)
- Source: `FormalConjectures/ErdosProblems/20.lean:66` in the checkout
- Statement: `∀ n k, n > 0 → 2 ≤ k → f n k ≤ (k - 1) ^ n * n.factorial + 1`

## Proof idea
Classical Erdős–Rado sunflower lemma, by induction on `n` for finite families of `Finset`s
(`core`). Take a maximum-size pairwise disjoint subfamily `D` (`disj_or_cover`). If `|D| ≥ k`,
any `k` members of `D` form a sunflower with empty kernel. Otherwise `U = ⋃ D` has at most
`(k-1)n` elements and meets every member, so by pigeonhole some `x ∈ U` lies in more than
`(k-1)^(n-1)(n-1)!` members. Erasing `x` from these gives an `(n-1)`-uniform family of the
same size (erase is injective on sets containing `x`). The induction hypothesis gives a
sunflower there, and re-inserting `x` gives a sunflower with kernel `insert x K`. The
`Set (Set α)` statement is reduced to the Finset version: `F` is finite (positive `ncard`),
its members are finite, and `F' = coe⁻¹' F` has the same cardinality
(`Set.ncard_preimage_of_injective_subset_range`). The sunflower is mapped back by `coe`.
`f`, `IsSunflower` and `IsSunflowerWithKernel` are restated locally (targeted imports,
no FormalConjecturesUtil).

## Axioms
`'Erdos20.erdos_20.variants.erdos_rado_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date
2026-11-02 (4 compiles: 2 with small errors, 1 clean, 1 clean + axioms)
