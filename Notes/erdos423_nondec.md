# Erdos423.erdos_423.variants.nondecreasing

- Source: FormalConjectures/ErdosProblems/423.lean:119 (category research solved, attributed to Bolan and Tang)
- Statement: `∀ a, IsHofstadterSeq a → ∀ n m, 1 ≤ n → n ≤ m → a n - n ≤ a m - m`

Proof idea: the definition requires a(k−1) < a(k) for k ≥ 3, and a 1 = 1 < 2 = a 2, so
a(k+1) ≥ a(k) + 1 for k ≥ 1. Then a(n+d) − (n+d) is nondecreasing in d by induction (omega,
including truncated subtraction).

REVIEW NOTE: as formalised, this statement follows directly from strict monotonicity of an
integer sequence. The research result it is attributed to is presumably stronger (or the
formalisation is weaker than intended). The proof is valid for the statement as written.

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-11 (2 compiles). Verified file: work/erdos423_nondec.lean (identical copy).
