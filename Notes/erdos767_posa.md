# erdos767_posa

- Statement: `Erdos767.erdos_767.variants.posa` (g_1(n) = 2n − 4 for n ≥ 4), checkout file `FormalConjectures/ErdosProblems/767.lean:74` (category research solved, Pósa).
- Proof idea: Upper bound: a graph with no cycle that has a chord at one of its vertices is 2-degenerate (the longest-path lemma CZ.low_deg, reused from erdos767_cz with k = 1). So deleting a vertex of degree ≤ 2 inside S gives E(S) ≤ E(S∖v) + 2. The base case |S| = 4 works as follows. If E(S) ≥ 5, the low-degree vertex v has exactly 2 neighbours p, q in the triangle S∖v. The third triangle vertex r then gives the 4-cycle p v q r with chord pq (lemma PO.k4, built with CZ.cyc). By induction E(S) ≤ 2|S| − 4 for |S| ≥ 4. Lower bound: K_{2,n−2} with small side {0,1}. Every big vertex y on a cycle has exactly 2 cycle neighbours (`IsCycle.ncard_neighborSet_toSubgraph_eq_two`), and these must be 0 and 1, so every graph edge between cycle vertices is a cycle edge and there are no chords. The edge count 2n − 4 comes from the degree sum.
- Axioms: `'Erdos767.erdos_767.variants.posa' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Date: 2026-11-14
