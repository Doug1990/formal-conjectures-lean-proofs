# green2_erdos

- Statement: `Green2.green_2_upper_bound_erdos` (category research solved, Erdős 1965)
- Source: `FormalConjectures/GreensOpenProblems/2.lean:76`
- Date: 2026-10-31

## Proof idea
Erdős's construction. For n ≥ 1 write n = 3k + 1 + r with r ≤ 2 and take A = [−k, 2k + r] ⊂ ℤ
(|A| = n). Let S ⊆ A with S∔S disjoint from A and let a = min S. Every other y ∈ S satisfies
a < y and a + y ∉ A. If a < 0, then a + y ≤ 2k + r − 1, so a + y < −k, i.e. y ∈ (a, −k − a),
an interval with at most k − 1 integers. If a ≥ 0, then a + y > 2k + r, so y lies in
(max(a, 2k+r−a), 2k+r], which has at most k + 1 integers. Hence |S| ≤ k + 2 ≤ n/3 + 2, so C = 2.
`Finset.restrictedSumset` and `maxRestrictedSumAvoidingSubsetSize` are restated verbatim from
the checkout; targeted imports instead of FormalConjecturesUtil.

## Axioms
`'Green2.green_2_upper_bound_erdos' depends on axioms: [propext, Classical.choice, Quot.sound]`
