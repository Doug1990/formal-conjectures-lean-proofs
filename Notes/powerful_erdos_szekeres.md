# PowerfulNumbersDensity.asymptotic_erdos_szekeres

- Statement: `PowerfulNumbersDensity.asymptotic_erdos_szekeres`, source file
  `FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean:60` (category research solved, Erdős–Szekeres 1935):
  `Q(x) − ζ(3/2)/ζ(3) · x^{1/2} = O(x^{1/3})`.
- `Nat.Full` / `Nat.Powerful` are restated locally from FormalConjecturesForMathlib/Data/Nat/Full.lean
  (same definitions); `Q` and `A` are copied verbatim. Targeted Mathlib imports.

## Proof idea
Every powerful n ≥ 1 is uniquely a²b³ with b squarefree. Existence: write n = c²b with b squarefree
(`Nat.sq_mul_squarefree_of_pos`); powerfulness forces every prime of b to divide c, so b ∣ c.
Uniqueness: b's p-adic valuation is v_p(n) mod 2. So Q(x) = Σ_{b ≤ N, b squarefree} ⌊√(N/b³)⌋ with
N = ⌊x⌋ (exact, via an injective image of a Finset of pairs). Each term lies in
(√x·b^{-3/2} − 1, √x·b^{-3/2}]. This gives Q ≤ √x·S with S = Σ_{b sqfree} b^{-3/2}. It also gives
Q ≥ √x·Σ_{b ≤ K} − K with K = ⌊x^{1/3}⌋, and the tail is ≤ 2/√K by the telescoping
inequality (t+1)^{-3/2} ≤ 2/√t − 2/√(t+1). With x = y³ the error is ≤ 4·x^{1/3} for x ≥ 1.
Finally S·ζ(3) = ζ(3/2): reindex the product series by (b, c) ↦ c²b (`tsum_mul_tsum_of_summable_norm`
+ `tsum_eq_tsum_of_ne_zero_bij`), with ζ(r).re = Σ 1/n^r taken from `zeta_eq_tsum_one_div_nat_cpow`.

Reusable: sqf_unique, powerful_decomp, powerful_mk, Q_eq (exact count formula), term_bounds,
step_ineq / tail_bound (Σ_{b>K} b^{-3/2} ≤ 2/√K), zeta_re (real zeta values for r > 1),
prod_identity.

## Axioms
`'PowerfulNumbersDensity.asymptotic_erdos_szekeres' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date
2026-11-04, 4 compiles (1: unknown `Nat.Ico_succ_right`; 2–3: "no goals" after `congr 1` had already
closed the Ico/Icc goal; 4: clean + axioms).
