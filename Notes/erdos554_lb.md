# Erdos554.erdos_554.variants.lower_bound

- Source: `FormalConjectures/ErdosProblems/554.lean:105` (category research solved, Bondy–Erdős / Erdős–Graham)
- Statement: for all n ≥ 1 and k ≥ 1, `n * 2 ^ k + 1 ≤ multicolourGraphRamsey k (cycleGraph (2 * n + 1))`.
- `multicolourGraphRamsey` is restated locally, word for word as in
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean`. The file uses targeted Mathlib imports.

## Proof idea
`multicolourGraphRamsey` is an `sInf` over ℕ, so the defining set first has to be shown nonempty (otherwise sInf = 0).
`LB.seq` is a greedy multicolour Ramsey argument. From (k+1)^j vertices it extracts j vertices whose edge colour
{f i, f i'} (i < i') depends only on i. Pigeonhole on these colours then gives a monochromatic K_{2n+1},
which contains C_{2n+1} (`LB.ramsey_cycle`). For the lower bound, write k = k'+1 and colour K_{n·2^k}, with
vertices x < 2n·2^{k'}, as follows. The colour of {x,y} is the least t with ⌊x/(2n·2^t)⌋ = ⌊y/(2n·2^t)⌋.
Colour 0 is a disjoint union of cliques on 2n vertices, and a copy of C_{2n+1} there stays in one block,
which contradicts injectivity. Colour s+1 is bipartite via the parity of ⌊x/(2n·2^s)⌋, and an odd cycle
has no proper 2-colouring (`LB.no_parity`). Smaller complete graphs inherit the colouring by pullback
along `Fin.castLEEmb`.

Reusable: `LB.seq` (generic greedy Ramsey sequence), `LB.ramsey_cycle` (finiteness of R_k(C_{2n+1})), `LB.adj_succ`/`LB.adj_wrap`/`LB.no_parity` (odd cycles are not bipartite), `LB.pull_copy`.

## Axioms
'Erdos554.erdos_554.variants.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-10
