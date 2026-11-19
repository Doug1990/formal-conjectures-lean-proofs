# Erdos481.erdos_481

- Source: `FormalConjectures/ErdosProblems/481.lean:57` (category research solved, Klarner 1982). No upstream formal proof link.
- Statement unchanged; `T` copied verbatim; FormalConjecturesUtil replaced by targeted Mathlib imports.

**Proof idea.** Track (value, multiplier) pairs: level k holds the r^k pairs (f_w(1), a_w) for words w of length k. Invariants: 1 ≤ a_w ≤ A^k (A = 1 + Σa_i), and 1 ≤ f_w(1) ≤ (1+B)(k+1)·a_w (B = Σb_i). The weight Σ_w 1/a_w equals S^k (S = Σ1/a_i > 1). If level k has no repeated values, then S^k ≤ (1+B)(k+1)·Σ_w 1/f_w(1) ≤ (1+B)(k+1)·H(M_k) ≤ (1+B)(k+1)(1 + log M_k), with M_k = (1+B)(k+1)A^k. That is O(k²), and it contradicts exponential growth (`tendsto_pow_const_div_const_pow_of_one_lt`).

Axioms: `'Erdos481.erdos_481' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-12. 2 compiles.
