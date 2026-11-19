# Erdos554.multicolourGraphRamsey_one_cycleGraph_five

- Source: `FormalConjectures/ErdosProblems/554.lean` (category test)
- Statement unchanged. `import Mathlib` is used, and `SimpleGraph.multicolourGraphRamsey` is restated verbatim from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean`.

**Proof idea.** With one colour (`Fin 1` is a subsingleton), every colour class `C.labelGraph i` is the complete graph ⊤ (helper `labelGraph_fin_one`). By `isContained_top_iff`, C₅ ⊑ K_n holds exactly when there is an embedding `Fin 5 ↪ Fin n`. For n ≥ 5, `Fin.castLE` gives such an embedding, so 5 is in the set and `sInf ≤ 5`. Conversely, any n in the set yields an embedding from the constant colouring, and `Fintype.card_le_of_embedding` gives 5 ≤ n. Then `le_csInf` finishes.

Axioms: `'Erdos554.multicolourGraphRamsey_one_cycleGraph_five' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-27
