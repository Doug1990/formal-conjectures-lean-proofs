# Erdos1098.erdos_1098.variants.upper_bound

- Source: FormalConjectures/ErdosProblems/1098.lean:76 (category research solved)
- Statement: if the centre Z(G) has finite index, the non-commuting graph of G is CliqueFree (index Z(G) + 1).

Proof idea: send a clique t to G ⧸ Z(G). The map is injective on t. If two distinct clique elements x, y had the same coset, then x⁻¹y would be central. So x·(x⁻¹y) = (x⁻¹y)·x, which gives xy = yx and contradicts adjacency. Hence |t| ≤ |G ⧸ Z(G)| = index, which rules out a clique of size index + 1. `nonCommutingGraph` is restated locally with targeted imports.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-09 (2 compiles: the first was correct but had a letI lint, the second was clean)
