# OeisA211417.forty_two_mul_a_dvd_product

- Source: FormalConjectures/OEIS/211417.lean:127 (category research solved)
- Statement: (2n+1)(3n+1)(5n+1) ∣ 42·a(n), where a(n) = (30n)! n! / ((15n)! (10n)! (6n)!).

Proof idea: a generic `frame` lemma turns X·D ∣ c·N into a per-prime count, via Legendre's formula and the Landau function Δ ≥ 0 at each layer q = p^i: v_p(X) ≤ v_p(c) + #{good layers with Δ = 1}. Three card lemmas bound the number of good layers below by v_p(2n+1) (minus one when p = 7), v_p(3n+1) and v_p(5n+1). Each uses the single-factor layer analysis: the bad layers are q ∈ {3,5,7}, {2,5,8} and {2,3,4}, and they are swapped for top layers q ≤ 30n < 6q. The factors are pairwise coprime except for 3 between 2n+1 and 5n+1, and 2 between 3n+1 and 5n+1 (from 3A−2B = 1, 5A−2C = 3, 5B−3C = 2). In those two cases the smaller valuation is ≤ 1, because 4 ∤ 2 and 9 ∤ 3. That leftover 1, and the bad 7-layer, are absorbed by v_p(42) = 1 for p ∈ {2,3,7}.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-05. Verified file: work/oeis211417_42.lean (clean on the first compile). results/oeis211417_forty_two.lean is an identical copy and was not compiled separately.
