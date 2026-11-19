# Erdos942.erdos_942.variants.limsup

- Source: `FormalConjectures/ErdosProblems/942.lean:51` (category textbook)
- Statement: `atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h)) = ⊤`, where h(n) counts powerful numbers in [n², (n+1)²).
- `Nat.Full` / `Nat.Powerful` (from FormalConjecturesForMathlib/Data/Nat/Full.lean) and `erdos_942.h` are restated verbatim; targeted Mathlib imports.

Proof idea: for L and N₀, take the first 2L primes p_i and γ_i = p_i·√p_i. Simultaneous Dirichlet approximation (own pigeonhole lemma `dirichlet` on fractional parts) applied to x_i = (N₀+1)/γ_i with Q = 3·p_{2L}² gives q = q'(N₀+1) ≥ N₀+1 and integers a_i with |q − a_i γ_i| < 1/3, so a_i ≥ 1. The numbers a_i²p_i³ are powerful (`powerful_mk`), pairwise distinct (the p_i-adic valuation is odd for exactly one of them, `key_ne`), and their square roots a_iγ_i lie in [q−1, q+1). So [q², (q+1)²) or [(q−1)², q²) contains at least L of them (`count_le`). Hence for every L, h(n) ≥ L for arbitrarily large n, and the limsup in ℕ∞ is ⊤ (`limsup_eq_iInf_iSup_of_nat` + `ENat.recTopCoe`).

Axioms: `'Erdos942.erdos_942.variants.limsup' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-31
