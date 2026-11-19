# Erdos436.erdos_436.variants.even_three

- Source: `FormalConjectures/ErdosProblems/436.lean:127` (category research solved, Lehmer–Lehmer 1962): `∀ k ≥ 2, Even k → Λ k 3 = ⊤`.
- Proof idea: For even k, every k-th power residue is a quadratic residue. Given M, let R be the product of the odd numbers below M+3 that are coprime to 3. Dirichlet gives arbitrarily large primes p ≡ −3 (mod 8R), and −3 is a unit mod 8R. For such p the Jacobi symbol satisfies J(m|p) = J(m|3) for all 0 < m < M+3 with 3 ∤ m. The proof is by strong induction on m: J(2|p) = χ₈(p) = −1 = J(2|3), and for odd m, reciprocity gives J(m|p) = J(p|m) = J(−3|m) = χ₄(m)·J(3|m) = J(m|3), since p ≡ 1 mod 4. In any window n, n+1, n+2 with n ≤ M, one element is ≡ 2 mod 3, so it is a non-residue. Hence r(k,3,p) ≥ M frequently, and the limsup is ⊤. No CRT over many moduli and no prime factorisation are needed, because the Jacobi symbol handles composite odd m directly.
- Axioms: `propext, Classical.choice, Quot.sound`
- Verified file: work/erdos436_even3.lean (results copy is identical). 2 compiles.
- Date: 2026-11-11
