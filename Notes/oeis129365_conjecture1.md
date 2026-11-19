# OeisA129365.conjecture1

- Source: FormalConjectures/OEIS/129365.lean:87 (category research solved)
- Statement: for n > 0, ∏_{k=1}^n (⌊n/k⌋!)^k divides ∏_{j,k=1}^n gcd(j,k).
- Proof idea: let f(d) = minFac d if d is a prime power, else 1 (so log f = Λ). By `vonMangoldt_sum`
  and injectivity of log, ∏_{d | i} f(d) = i for i ≥ 1. Writing every gcd(j,k) and every factor of m!
  as such a product over d ∈ [1,n] and swapping products gives
  numerator = ∏_d f(d)^{M_d²} and denominator = ∏_d f(d)^{Σ_k k·⌊M_d/k⌋} with M_d = ⌊n/d⌋
  (counts of multiples via `Nat.Ioc_filter_dvd_card_eq_div`). Since k·⌊M/k⌋ ≤ M and the terms with k > M
  vanish, the denominator exponent is ≤ M², so each factor divides. No p-adic valuations needed.
- Axioms: propext, Classical.choice, Quot.sound
- Date: 2026-11-05
- Compiles: 2 (only remaining warning: the statement's unused hypothesis `hn`)
- File: results/oeis129365_conjecture1.lean (identical copy of work/oeis129365_c1.lean)
