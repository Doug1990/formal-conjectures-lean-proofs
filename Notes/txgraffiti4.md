# txgraffiti4

- Statement: `Arxiv.«2507.17780».tx_graffiti_conjecture_4` (category research solved; TxGraffiti Conjecture 4 is false)
- Source: `FormalConjectures/Arxiv/2507.17780/4.lean:95`
- Date: 2026-11-02
- Compiles: 1 (clean, including `#print axioms`)

## Proof idea
Counterexample: the friendship graph F₄ (hub 0, rims {1,2},{3,4},{5,6},{7,8}). The upstream proof uses `native_decide`; this one is kernel-checked. The definitions (IsEdgeMatching, IsMaximalEdgeMatching, saturationNumber, harmonicIndex) are restated locally and unchanged, and the statement is unchanged.

Lower bound μ*(F₄) ≥ 4, by hand rather than by enumerating all 4096 edge subsets:
- If a maximal matching contains neither the rim edge of a triangle nor a spoke to that rim, the rim edge could be added (lemma `tri`; the disjointness check is a small `decide +kernel` over the 12 edges).
- Two spokes share the hub, so a matching contains at most one spoke (`spoke_uniq`).
- So M contains either all 4 rims, or one spoke plus the 3 rims of the other triangles.

The four rims form a maximal matching, so the sInf set is nonempty. H(F₄) = 18/5 is checked by `decide +kernel`, connectivity holds because every vertex is adjacent to the hub, and 4 > 18/5.

## Axioms
'Arxiv.«2507.17780».tx_graffiti_conjecture_4' depends on axioms: [propext, Classical.choice, Quot.sound]
