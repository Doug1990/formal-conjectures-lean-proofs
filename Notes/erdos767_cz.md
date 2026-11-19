# erdos767_cz

- Statement: `Erdos767.erdos_767.variants.czipszer` (g_k(n) ≤ (k+1)n), checkout file `FormalConjectures/ErdosProblems/767.lean:69`, category research solved (Czipszer).
- Proof idea: The proof first shows that a graph with no cycle carrying k chords at one of its vertices has, in every nonempty vertex set S, a vertex with at most k+1 neighbours in S (`CZ.low_deg`). To see this, take a longest path inside S. All S-neighbours of its start a lie on the path, since otherwise the path could be extended. If a had at least k+2 of them, pick the neighbour y farthest along the path. The prefix up to y, closed by the edge ya, is a cycle (`CZ.cyc`). Its edges at a are only ay and a–(second vertex). The farthest choice puts all other neighbours on the cycle, so they give ≥ k chords at a. Induction on |S| then removes a low-degree vertex each time, which gives at most (k+1)|S| edges inside S (`CZ.edges_le`). The sSup bound follows from `csSup_le'`. Defs are restated locally with targeted imports.
- Axioms: `propext, Classical.choice, Quot.sound`
- Date: 2026-11-14
