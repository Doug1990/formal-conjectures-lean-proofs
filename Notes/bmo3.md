# BeaverMathOlympiad.beaver_math_olympiad_problem_3

Source: FormalConjectures/Other/BeaverMathOlympiad.lean:143 (category research solved).

Proof idea: let T(t) = Σ_{i=1}^{t} 2^{v₂(i)}, so T(2t) = 2T(t) + t and T(2t+1) = T(2t) + 1.
The sequence runs in blocks of four: a(4t+2) = B(t) := 12(t+1) + 16T(t), and B(t) = 2^{v₂(t+1)+2}·odd
(Vval, induction on k for t+1 = 2^k·m). So the next terms are B + 2^{v₂(t+1)+4} − 1 (odd),
+2 (≡ 2 mod 4), +9 (odd), and a(4t+6) = B(t+1). Odd terms > 1 and terms ≡ 2 mod 4 are not
powers of 4. B(t) = 4^k would give H₆(t) = 8T(t) + 6t + 6 = 2^{2k−1}. For p ≡ 2 mod 4, p ≥ 6,
H_p(t) = 8T(t) + pt + p is never a power of 2 (strong induction on t): H_p(2s) ≡ 2 mod 4, and
H_p(2s+1) = 2·H_{p+4}(s).

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-09 (3 compiles)
