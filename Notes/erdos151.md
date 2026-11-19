# erdos151 (sqrt_bound + cliqueFree_three)

- Statements: `Erdos151.erdos_151.variants.sqrt_bound` (τ(G) ≤ n − ⌊√n⌋) and
  `Erdos151.erdos_151.variants.cliqueFree_three` (triangle-free ⇒ τ(G) ≤ n − H(n)).
- Source: `FormalConjectures/ErdosProblems/151.lean` (lines 94 and 85), both `research solved`.
  The definitions IsBigMaximalClique / IsCliqueTransversal / cliqueTransversalNumber / H are
  restated verbatim. The file uses targeted Mathlib imports instead of FormalConjecturesUtil.

Proof idea: if a vertex set I contains no maximal clique with ≥ 2 vertices, then V \ I is a
clique transversal, so τ ≤ n − |I| (CT.tau_le). Two kinds of I qualify: an independent set
(a big clique has two adjacent vertices), and the open neighbourhood N(v) of any vertex
(every clique inside N(v) extends by v, so it is not maximal). For the triangle-free case,
`Nat.sSup_mem` gives an independent set of size H(n). For the √n bound, let S be a
maximum independent set and s = ⌊√n⌋. If |S| ≥ s we are done. Otherwise S is dominating, so
n ≤ Σ_{v∈S} (deg v + 1). If every v ∈ S had deg v < s, this would give n ≤ |S|·s ≤ s² − s < n.
So some v has |N(v)| ≥ s.

Axioms (both): propext, Classical.choice, Quot.sound

Date: 2026-11-14
