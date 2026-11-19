# Erdos712.erdos_712.variants.limit_exists

- Source: `FormalConjectures/ErdosProblems/712.lean:56` (category textbook)
- Definitions `Finset.ContainsCompleteHypergraph`, `Hypergraph.extremalNumber`, `Hypergraph.cliqueExtremalNumber` restated verbatim from `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean` (targeted Mathlib imports, since FormalConjecturesUtil is not built).

**Proof idea.** This is the Katona–Nemetz–Simonovits averaging argument. Take an extremal K_k^r-free family H on n+1 vertices. Each edge avoids exactly n+1−r vertices, so Σ_v |H − v| = |H|·(n+1−r). Some vertex v therefore has (n+1)|H − v| ≥ |H|(n+1−r). The family H − v, relabelled to Fin n via `Fin.succAboveEmb v`, is still r-uniform and K_k^r-free, so ex(n+1)(n+1−r) ≤ (n+1)·ex(n). Combined with C(n,r)(n+1) = C(n+1,r)(n+1−r), this shows that ex(n)/C(n,r) is antitone for n ≥ r. It lies in [0,1] (ex ≤ C(n,r)), so it converges to its infimum (`tendsto_atTop_ciInf` on the shifted sequence, then `tendsto_add_atTop_iff_nat`), and the limit lies in [0,1].

Axioms: `'Erdos712.erdos_712.variants.limit_exists' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-29
