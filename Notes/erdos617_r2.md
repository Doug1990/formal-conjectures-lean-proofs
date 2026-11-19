# Erdos617.erdos_617.variants.r2

- Source: FormalConjectures/ErdosProblems/617.lean:76 (category research solved)
- Date: 2026-11-10
- Axioms: `'Erdos617.erdos_617.variants.r2' depends on axioms: [propext, Classical.choice, Quot.sound]`

Proof idea: for every prime q, take V = 𝔽_q² (q² vertices) and colour the edge {u, v} by the
slope (v−u).2/(v−u).1 ∈ 𝔽_q (vertical differences get colour 0), read as an element of Fin q.
This is symmetric because (−b)/(−a) = b/a. Given q+1 points S and a colour k = s, the map
x ↦ x.2 − s·x.1 into 𝔽_q (q values) is not injective on S (pigeonhole), so there are u ≠ v with
v−u on the line of slope s; u ≠ v forces (v−u).1 ≠ 0, so the edge has colour s. So the set
contains all primes, which is infinite. (Affine plane construction; the vertical class is merged
into colour 0 so that q colours suffice.)
