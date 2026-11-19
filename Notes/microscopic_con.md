# microscopic_con

- Statement: `Arxiv.«2607.05349».hasFiniteConcentration_of_hasMicroscopicWeighting` (category research solved; Roff–Willerton Theorem 3.1(3))
- Source: `FormalConjectures/Arxiv/2607.05349/MicroscopicWeighting.lean:155`
- Date: 2026-10-31
- Compiles: 3 (clean on the 3rd, including `#print axioms`)

## Proof idea
`det Z(t)` is an exponential polynomial (Leibniz formula), so it is real-analytic in `t`, and it tends to `det 1 = 1` as `t → ∞`, because `Z(t) → I` entrywise. By the identity theorem it does not vanish identically near 0, so by isolated zeros it is nonzero on a punctured neighbourhood of 0. That means `Z(t) w(t) = 1` for all small `t > 0`, which matters because `Matrix.inv` is junk on singular matrices. Write `Z(t) = J + t·E(t)` with `E(t)_{ij} = (e^{-t d_ij} - 1)/t → -d_ij` (the derivative at 0). Then `(1 - Σ_j w_j(t))/t = (E(t) w(t))_i` for every `i`. The right side tends to `-(D w)_i`. The left side does not depend on `i`, so `D w` is constant (uniqueness of limits). Multiplying by `t → 0` gives `Σ w(t) → 1`, so `Σ w = 1`. Hence `w` is a gauging of `D`.

The definitions are restated locally, copied verbatim, with `@[category]` attributes dropped. Imports are targeted Mathlib modules.

## Axioms
`'Arxiv.«2607.05349».hasFiniteConcentration_of_hasMicroscopicWeighting' depends on axioms: [propext, Classical.choice, Quot.sound]`
