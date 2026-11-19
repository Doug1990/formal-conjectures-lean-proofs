# erdos494_product

- Statement: `Erdos494.erdos_494.variants.product`
- Source: `FormalConjectures/ErdosProblems/494.lean:150` (category research solved)
- Date: 2026-11-11

Proof idea: the statement is purely existential, so any counterexample works (the one used is simpler than Steinerberger's ζ₆ example). Take A = {0,1,2,3} and B = {0,−1,−2,3}, embedded from ℤ into ℂ. Three of the four 3-subsets contain 0, so their product is 0; the remaining 3-subset has product 6 in both cases. So both product multisets are {0,0,0,6}. The helper `PM.prod_cast` moves the multiset computation to ℤ (`Finset.powersetCard_map`, `Finset.prod_map`, `Int.cast_prod`), where it is decidable and closes by `rfl` during `congr 1`. A ≠ B follows from injectivity of `Finset.map` and `decide` on Finset ℤ.

Axioms: `'Erdos494.erdos_494.variants.product' depends on axioms: [propext, Classical.choice, Quot.sound]`

Verified with `.\tools\check.ps1` (3 compiles). The `@[category]` attribute and `FormalConjecturesUtil` import were replaced by targeted Mathlib imports; `prodMultiset` was restated verbatim.
