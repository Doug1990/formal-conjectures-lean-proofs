# BugeaudNormalAndRich.isNormalInBase_iff_isEquidistributedModuloOne

- Source: `FormalConjectures/Books/BugeaudDistributionModuloOne/NormalAndRich.lean:54` (category research solved; Wall 1949, Bugeaud Thm 4.14)
- Proof file: `results/bugeaud_normal_equi.lean` (targeted imports; `IsNormalInBase`, `digitSeq`, `IsEquidistributed(ModuloOne)` restated verbatim from FormalConjecturesForMathlib)

**Proof idea.** Write y_i = {b^i ξ}. Reusing the digit dictionary from `isRichInBase_iff_dense` (`pre`, `pre_iff`, `digit_eq`), the word w occurs at position i iff ⌊b^k y_i⌋ = W, where W = pre(w) < b^k. That is the same as y_i lying in the b-adic interval [W/b^k, (W+1)/b^k) (`event_iff`, `floor_mem`). (⇒) Normality gives frequency 1/b^k for every level-k b-adic interval (`limA`; the frequency is 0 when W ≥ b^k). A closed interval [c,d] contains the union of the level-k intervals with indices ⌈b^k c⌉ ≤ W < ⌊b^k d⌋, and is covered by those with indices ⌊b^k c⌋ ≤ W ≤ ⌊b^k d⌋. Counting by fibres (`card_fiber`) and `tendsto_finsetSum` give liminf ≥ d−c−2/b^k and limsup ≤ d−c+2/b^k, and `tendsto_order` closes the proof. (⇐) The frequency for a half-open interval [c,d) is squeezed between the frequencies for the closed intervals [c,e] with e < d (from below) and [c,d] (from above) (`ico_lim`). Apply this to the b-adic interval of w.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-30
