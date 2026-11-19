# Erdos675.minTranslation_squarefree_three

- Source: `FormalConjectures/ErdosProblems/675.lean` (category test)
- Statement unchanged; `import Mathlib` is used, and `IsTranslation` and `minTranslation` are restated verbatim.

**Proof idea.** First check that t = 4 is a valid translation. 1, 2, 3, 5, 6, 7 are all squarefree: 2, 3, 5, 7 are prime, 6 = 2·3 with coprime factors, and 1 is a unit. So `sInf ≤ 4`. For the other direction, `le_csInf` reduces to showing that no t ∈ {1, 2, 3} works. In each case some a ∈ {3, 2, 1} has a + t = 4, which is not squarefree (2·2 ∣ 4 and 2 is not a unit), while a is squarefree. No `decide` is used on `Squarefree`.

Axioms: `'Erdos675.minTranslation_squarefree_three' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-27
