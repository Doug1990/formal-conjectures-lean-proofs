# Erdos539.erdos_539.variants.sq_isBigO

- Source: FormalConjectures/ErdosProblems/539.lean:82 (category research solved, AMS 5 11; Erdős–Szemerédi lower bound √n ≪ h(n))
- Statement (unchanged): `(fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (cofactorThreshold n : ℝ)`. The definitions `IsCofactorLowerBound` and `cofactorThreshold` are copied locally (targeted imports, no FormalConjecturesUtil).
- Proof idea: for |A| = n ≥ 2 pick m ∈ A with m ≠ 0. The map a ↦ (a/(a,m), m/(m,a)) sends A into B×B, where B is the set of cofactors, and it is injective because a = (a/g)·(m/(m/g)) with g = gcd(a,m). So n ≤ |B|², hence ⌊√n⌋ is a cofactor lower bound. The set of lower bounds is bounded by n² (use A = range n), so ⌊√n⌋ ≤ h(n) by `le_csSup`, and √n < ⌊√n⌋ + 1 ≤ 2h(n). IsBigO constant 2. Note: this is the short textbook argument, and the formalisation matches the intended statement (it is not suspicious: the statement is research solved, not open).
- Axioms: `'Erdos539.erdos_539.variants.sq_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Compiles: 2 (1: compiled, only a `push_neg` deprecation warning; 2: clean + axioms)
- Date: 2026-11-12
