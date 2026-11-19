# erdos856_upper

- Statement: `Erdos856.erdos_856.variants.erdos_upper` (research solved, Erdős Er70), source `FormalConjectures/ErdosProblems/856.lean:98`.
  For k ≥ 3: ∃ C > 0, eventually f_k(N) ≤ C · log N / log log N.
- The definitions `HasEqualLcmTuple` and `f` are restated verbatim. The file imports Mathlib only.

**Proof idea.** For distinct primes q, r with a·q = b·r = L, lcm(a, b) = L. So for a fixed L, the pairs (a, q) ∈ A × {primes < N} with aq = L have pairwise distinct a's that share the pairwise lcm L. In a set A without an equal-lcm k-tuple there are therefore at most k − 1 such pairs. Grouping Σ_{a∈A} Σ_{q<N} 1/(aq) by L = aq ≤ N² gives (Σ_A 1/a)(Σ_{p<N} 1/p) ≤ (k−1)·H(N²) ≤ 3(k−1) log N for N ≥ 3. The Mertens-type bound log log N ≤ 2 Σ_{p<N} 1/p (Euler product over smooth numbers, reused from erdos878_quad's QL.loglog_le) then gives f_k(N) ≤ 6(k−1) log N / log log N. The bound passes to the sSup by csSup_le, since A = ∅ makes the set nonempty.

Axioms: `'Erdos856.erdos_856.variants.erdos_upper' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-14. Compiles: 4 (the first one timed out).
