# SimpleGraph.lemma4

- Source: FormalConjectures/Paper/DegreeSequencesTriangleFree.lean:274 (category API)
- Statement unchanged; `degreeSequence` / `degreeSequenceMultiplicity` restated locally, verbatim from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Degrees.lean.

Proof idea: take K, the bipartite graph on 8·(2n) vertices from lemma3 (n = |G|), with m = 2n. It has minimum degree 2n+1 and degree-sequence multiplicity 3, and it is triangle-free because it is 2-colourable. H is the disjoint union of G (on ULift (Fin n)) and K (on ULift (Fin 16n)), plus one extra edge between v and a fixed vertex u of K. H is triangle-free: a triangle would have to use the bridge edge, and that forces a loop. The degree of v goes up by 1 and the other degrees in G do not change (`deg_inl`). The induced subgraph J on the vertices outside G is isomorphic to K (`jIso`). Multiplicity and minimum degree are isomorphism invariants (`mult_iso`, `min_ge`), so f(J) = 3 and δ(J) = 2n+1 ≥ 2n. A universe-polymorphic helper `DfsL4.main` handles the `Type*` in the existential.

Axioms: `'SimpleGraph.lemma4' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-02 (the file also contains lemma3, proved earlier the same day).
