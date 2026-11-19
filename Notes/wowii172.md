# wowii172

- Statement: `WrittenOnTheWallII.GraphConjecture172.conjecture172` (DISPROOF of `Ls G ≥ -1 + Δ(B(G)) + dist_min(G, M(G²))`), source `FormalConjectures/WrittenOnTheWallII/GraphConjecture172.lean:62` (research solved).
- Proof idea: D₉ on `Fin 14`: the path 0–1–…–9 plus triangles {0,10,11} and {9,12,13}, with arithmetic adjacency. (1) Ls ≤ 4: by a cut argument (`cut_edge`: a connected spanning subgraph crosses every cut), every path edge lies in any spanning tree T, and 0 / 9 also get a T-edge into their triangle. So every vertex 0..9 has two T-neighbours, and the leaves are among {10,11,12,13}. (2) peripheryMaxDegree ≥ 2: some vertex attains the diameter (`exists_eccent_eq_ediam_of_finite`), and every vertex has degree ≥ 2. (3) `computable_dist` is related to `dist` by restating the checkout's `dist_eq_computable`. dist ≤ 2 ⇔ adjacent or a common neighbour, so the square degrees are computed by `decide`, and the maximisers are exactly {1, 8}. (4) dist(1,8) ≥ 7 via a 1-Lipschitz potential. Then 4 ≥ -1 + 2 + 7 is false.
- Axioms: propext, Classical.choice, Quot.sound
- Date: 2026-11-19
- The checkout definitions (Ls, maxEccentricityVertices, distMin, bfsStep, bfs_dist_aux, computable_dist, and the lemma dist_eq_computable with its helpers) are restated verbatim.
