# Erdos999.erdos_999.variants.easy_direction

- Source: `FormalConjectures/ErdosProblems/999.lean:63` (category textbook)
- Date: 2026-10-30
- Compiles: 2 (1st: `zero_le _` → `zero_le`; 2nd: clean)

Proof idea. Suppose g(q) = φ(q)f(q)/q is summable. Then g(q) → 0, so for q ≥ Q₁ we have f(q)/q ≤ g(q) < 1/2 (as φ(q) ≥ 1). For x ∈ [1,2) and |x − p/q| < f(q)/q, this forces 0 < p < 3q, so x lies in S_q = ⋃ over p < 3q with gcd(q,p)=1 of ball(p/q, f(q)/q). There are at most 3φ(q) such p (three blocks of length q, `Nat.filter_coprime_Ico_eq_totient`), so vol(S_q) ≤ 6g(q) and Σ vol(S_q) < ∞. By Borel–Cantelli (`ae_eventually_notMem`), a.e. x lies in only finitely many S_q. But an approximable x ∈ [1,2) lies in S_q for infinitely many q. So, a.e., x ∉ [1,2), i.e. vol([1,2)) = 0, which is a contradiction.

Axioms: `'Erdos999.erdos_999.variants.easy_direction' depends on axioms: [propext, Classical.choice, Quot.sound]`

Note: `IsApproximable` is restated locally with targeted imports (no FormalConjecturesUtil); the `category` attribute is omitted.
