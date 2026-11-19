# BugeaudNormalAndRich.isRichInBase_iff_dense

- Source: `FormalConjectures/Books/BugeaudDistributionModuloOne/NormalAndRich.lean:62` (category textbook, AMS 11)
- Statement: for b ≥ 2, ξ is rich in base b iff {b^n ξ mod 1} is dense in `AddCircle 1`.
- `digitSeq` and `IsRichInBase` are restated verbatim from `FormalConjecturesForMathlib/NumberTheory/NormalNumber.lean` (the FormalConjecturesUtil import is not built here), with targeted Mathlib imports.

Proof idea: write y_i = fract(b^i ξ). Digit i+j of ξ equals ⌊b^{j+1} y_i⌋ mod b (`digit_eq`). For y ∈ [0,1), the first k digits ⌊b^{j+1} y⌋ mod b equal w_0..w_{k-1} exactly when ⌊b^k y⌋ = pre(w,k) = Σ w_j b^{k-1-j} (`pre_iff`, proved by induction using ⌊b^{m+1}y⌋ / b = ⌊b^m y⌋). Rich ⇒ dense: for an open U ∋ ↑t, take s = fract t and a ball of radius ε around s, pick k with b^{-k} < ε, and use the first k digits of s as the block. Richness gives i with ⌊b^k y_i⌋ = ⌊b^k s⌋, so |y_i − s| < b^{-k} and ↑(b^i ξ) = ↑y_i ∈ U. Dense ⇒ rich: the image of the open b-adic interval (W/b^k, (W+1)/b^k) with W = pre(w,k) < b^k is open and nonempty in the circle (the quotient map is open). Density gives i with y_i in that interval, so ⌊b^k y_i⌋ = W, and `pre_iff` gives the digits.

Axioms: `'BugeaudNormalAndRich.isRichInBase_iff_dense' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-30
