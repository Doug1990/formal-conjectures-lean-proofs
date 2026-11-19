# Erdos36.minimum_overlap.variants.lower.erdos_1955

- Source: `FormalConjectures/ErdosProblems/36.lean:269` (category textbook)
- Statement: `(1 : ℝ) / 4 ≤ atTop.liminf MinOverlapQuotient`
- The work file restates `Overlap`, `MaxOverlap`, `M` and `MinOverlapQuotient` verbatim with targeted imports, and copies three small API lemmas from the source file (`overlap_le_card_left`, `bddAbove_range_overlap`, `maxOverlap_le_card_left`).

**Proof idea.** `M n` is attained (`Nat.sInf_mem`; the set is nonempty via A = [1,n], B = [n+1,2n]) by some balanced partition (A, B) of {1..2n}, so |A| = |B| = n. Every difference a − b lies in [1−2n, 2n−1], which has 4n−1 values. Splitting A×B into fibres by difference gives n² = Σₖ Overlap(k) ≤ (4n−1)·MaxOverlap (`Finset.card_eq_sum_card_fiberwise`), and this forces 4·M(n) ≥ n for n ≥ 1. So M(n)/n ≥ 1/4 eventually. M(n) ≤ |A| = n bounds the sequence above by 1, which gives the cobounded side condition (`isCoboundedUnder_ge_of_le`) for `le_liminf_of_le`.

**Axioms:** `propext, Classical.choice, Quot.sound`

**Date:** 2026-10-29 (3 compiles)
