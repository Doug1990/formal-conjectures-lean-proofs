# Erdos934.erdos_934.variants.h_one

- Source: `FormalConjectures/ErdosProblems/934.lean:101` (category research solved; "easy" per the docstring)
- Statement: `∀ d : ℕ, d ≠ 2 → h 1 d = d + 1`
- Verified file: `work/erdos934_h1.lean` (this results copy was written by hand from it and not compiled separately)

**Proof idea.** For t = 1, `HasFarEdges G 1` means G has two vertex-disjoint edges (`1 ≤ edist a b ↔ a ≠ b`).
Lower bound: the star K_{1,d} on `Fin (d+1)` (`fromRel (i = 0)`) has max degree ≤ d and d edges, and any two of its edges share the centre. So no m ≤ d lies in the defining set.
Upper bound: assume G has max degree ≤ d, at least d+1 edges, and no two disjoint edges. Take an edge uv. If every edge contains u (or every edge contains v), then |E| ≤ deg u ≤ d. Otherwise there are edges vw (w ≠ u) and ux (x ≠ v). These two must meet, so w = x and uvw is a triangle. Every edge then meets all three triangle edges, so E ⊆ {uv, uw, vw}. That gives d+1 ≤ 3, while deg u ≥ 2 gives d ≥ 2, so d = 2, which is excluded. Finally `le_antisymm (Nat.sInf_le _) (le_csInf _ _)`.

Axioms: `'Erdos934.erdos_934.variants.h_one' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-05
