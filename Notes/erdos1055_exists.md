# Erdos1055.exists_p

- Source: `FormalConjectures/ErdosProblems/1055.lean:54` (category textbook)
- Statement: for every `r : ℕ+` there is a prime `p` with `IsOfClass r p`.
- Date: 2026-10-30

Proof idea: First unfold the `PNat.caseStrongInductionOn` definition into equations for class 1 and class n+1 (`C_one`, `C_succ`, via `PNat.strongInductionOn.eq_1`). The classes are unique, because the first conjunct of class n+1 rules out every lower class. Every prime has a class. The proof is strong induction on p: for p ≥ 3 all prime factors of p+1 are < p, and p gets either a lower class or class (max of the factor classes)+1. If p has class n+1, then some prime factor of p+1 has class exactly n (descent). Classes are unbounded: if p ≥ 5 has class s, Dirichlet (`Nat.forall_exists_prime_gt_and_modEq`) gives a prime q ≡ −1 mod p. Then p | q+1, so q cannot have class 1 (p ∉ {2,3}), and q's class is > s. Start from 5 (class 1), climb to a class ≥ r, then descend to exactly r.

Axioms: `'Erdos1055.exists_p' depends on axioms: [propext, Classical.choice, Quot.sound]`

The definition `IsOfClass` is copied verbatim from the source. The imports are targeted Mathlib imports instead of FormalConjecturesUtil.
