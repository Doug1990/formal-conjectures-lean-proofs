# SimpleGraph.theorem1 (Erdős–Fajtlowicz–Staton, Theorem 1)

- Statement: `SimpleGraph.theorem1`, FormalConjectures/Paper/DegreeSequencesTriangleFree.lean:254, category research solved.
  A connected triangle-free graph whose degree sequence has maximal multiplicity f = 2 is bipartite, has minimum degree 1,
  and has a compact degree sequence.
- Verified file: `work/dfs_main.lean` (compiled clean, only lint warnings). `results/dfs_theorem1.lean` is NOT yet written:
  I ran low on budget and did not want to retype 520 lines without being able to compile the copy. Next run: copy
  work/dfs_main.lean byte for byte to results/dfs_theorem1.lean with the Write tool.
- Definitions `degreeSequence`, `degreeSequenceMultiplicity`, `IsCompactSequenceOn`, `HasCompactdegreeSequence` are restated
  verbatim (targeted imports, no FormalConjecturesUtil).

## Proof idea
Sort the vertices by degree (`Tuple.sort`) to get a bijection `ord : Fin N ≃ α` with `degreeSequence G = ofFn (deg ∘ ord)`.
f = 2 gives N ≥ 2 and no three equal degrees, so D(k+2) ≥ D(k)+1. Let B be the ⌊N/2⌋ lowest-degree vertices and T the rest
(t = |T|). Pairing B with shifted indices in T (four cases, N mod 4) gives
Σ_T deg ≥ Σ_B deg + 2⌊t²/4⌋, with a +1 if N ≡ 1 mod 4 or some step D(k+2) − D(k) ≥ 2.
On the graph side, Σ_T deg = 2e(G[T]) + e(T,B) ≤ 2e(G[T]) + Σ_B deg, with a −1 if B has an edge. Mantel/Turán in Mathlib
(`exists_isTuranMaximal`, `mul_card_edgeFinset_turanGraph_le`) gives e(G[T]) ≤ #E(turanGraph t 2) ≤ t²/4.
So everything is tight: the degree sequence is compact, B is independent, and G[T] is Turán-maximal, hence
G[T] ≅ turanGraph t 2 (`IsTuranMaximal.nonempty_iso_turanGraph`). Colour T by parity of the Turán index and each B vertex
by the opposite parity of its neighbours (which are pairwise non-adjacent, so they have the same parity). For δ = 1:
the top vertex of B has all its neighbours in one parity class, so D(⌊N/2⌋−1) ≤ ⌈t/2⌉, while compactness gives
D(⌊N/2⌋−1) ≥ D(0) + (⌊N/2⌋−1)/2. This forces D(0) ≤ 1.

## Axioms
'SimpleGraph.theorem1' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-01
