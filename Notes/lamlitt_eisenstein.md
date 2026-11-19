# lamlitt_eisenstein

- Statement: `LamLitt.lam_litt.variants.eisenstein` (Eisenstein 1852: an algebraic power series over ℚ[z] has all its coefficients in ℤ[1/N] for some N).
- Source: `FormalConjectures/LittProblems/1.lean:105` (category research solved).
- The definitions `ℤAdjoinInvNat` and `IsCoeffIntegralAdjointInvNat` are copied verbatim. The file uses plain Mathlib imports instead of FormalConjecturesUtil.

## Proof idea
Take a nonzero annihilating polynomial p ∈ ℚ[z][y] of minimal degree. Because the characteristic is 0, p′(f) ≠ 0. Let k be the order of D = p′(f) and write f = A + z^{k+1} g, where A is the truncation of f below degree k+1. The Taylor expansion of p at A (`Polynomial.taylor`) gives Σ_j t_j (z^{k+1} g)^j = 0. Here t_1 = p′(A) = z^k w with w(0) = c ≠ 0, because p′(f) − p′(A) is divisible by f − A. Dividing by z^{2k+1} gives z^{2k+1}(c·g + z·H(g)) = −t_0, where H only involves g through its lower coefficients. Comparing the coefficients of z^{n+2k+1} gives c·g_n = −[t_0]_{n+2k+1} − [zH]_n. By strong induction every g_n lies in ℤ[1/N], provided N clears the denominators of c⁻¹, of f_0..f_k and of all the coefficients of p (`EI.fin_mem` takes N = product of the denominators). The coefficients of the t_j are in ℤ[1/N] via hasseDeriv/eval. Reusable: EI.fin_mem (finite set ⊆ ℤ[1/N]) and EI.Gd_* (truncated "coefficients in a subring" calculus for ℚ⟦X⟧: mul, pow, sum, eval).

## Axioms
'LamLitt.lam_litt.variants.eisenstein' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-18
