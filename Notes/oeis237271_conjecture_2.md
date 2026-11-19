# OeisA237271.conjecture_2 (and conjecture_3)

- Source: FormalConjectures/OEIS/237271.lean:115 (conjecture_2, research solved); conjecture_3 (:155) is `conjecture_2 n` in the source and is re-checked here.
- Proof idea: the two counts are over the same list of consecutive divisor pairs (d, d'), so it suffices that the predicates agree pointwise (`List.countP_congr`). If d' is odd and d' ≥ 2d then d' ≠ 2d (parity), so d' > 2d. Conversely, if d' > 2d and d' = 2c were even, c would be a divisor of n with d < c < d', which contradicts consecutiveness in the strictly sorted divisor list (index comparison via `List.pairwise_iff_getElem`).
- Axioms: `'OeisA237271.conjecture_2' depends on axioms: [propext, Classical.choice, Quot.sound]` (the same for conjecture_3)
- Date: 2026-11-06. 1 compile. results/oeis237271_conjecture_2.lean is an identical copy of work/oeis237271_c2.lean.
