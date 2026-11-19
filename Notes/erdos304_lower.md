# erdos304_lower

- Statement: `Erdos304.erdos_304.variants.lower_1950` (log log b ≪ N(b)), category research solved (Er50c).
- Source: `FormalConjectures/ErdosProblems/304.lean:160` in the checkout.
- Date: 2026-11-14.

Proof idea: take a = b − 1. By Fibonacci–Sylvester (the `egypt` lemma, copied from
results/erdos295_k.lean), (b−1)/b is a sum of distinct unit fractions, so the set behind the sInf
is nonempty and k = N(b−1, b) is attained by some s. Gap lemma (`LW.gap`): if j ≤ K unit
fractions sum to less than u/v, the gap is at least 1/(2Kv)^(2^j). The induction either finds a term
1/n with n < 2Kv and recurses with target u/v − 1/n (denominator vn ≤ 2Kv²), or all terms are
≤ 1/(2Kv), so the sum is ≤ 1/(2v) ≤ u/v − 1/(2v). For target 1 the gap is exactly 1/b, so
b ≤ (2k)^(2^k). That gives log log b ≤ k log 2 + log log 2k ≤ 3k. Finally k ≤ N(b) by `le_csSup`
(the set is bounded by the Finset.sup). The definitions from 304.lean are restated locally, with
targeted imports instead of the checkout import.

Axioms: `'Erdos304.erdos_304.variants.lower_1950' depends on axioms: [propext, Classical.choice, Quot.sound]`
