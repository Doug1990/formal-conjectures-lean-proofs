# Erdos507.erdos_507.variants.lower_erdos

- Source: FormalConjectures/ErdosProblems/507.lean:110 (category research solved, AMS 51)
- Statement: `α ≫ (fun n ↦ 1 / (n : ℝ) ^ 2)`, i.e. `(fun n ↦ 1/n²) =O[atTop] α` (the `≫` notation from FormalConjecturesForMathlib/Analysis/Asymptotics/Basic.lean is spelled out as `Asymptotics.IsBigO`; definitions of `triangle_area`, `minTriangleArea`, `α` are copied locally, as in results/erdos507_ut.lean, since the project's Util module cannot be imported).
- Proof idea (Erdős): for n ≥ 7 pick a prime p with n < p ≤ 2n (Bertrand). Take the n points (k, k² mod p)/(2p), k < n; they lie in [0,1/2]², hence in the unit disk, and are distinct. For three distinct k, twice the area times 4p² is an integer D, and mod p, D ≡ (a−c)(b−c)(b−a) ≠ 0, so |area| ≥ 1/(8p²) ≥ 1/(32n²). This also rules out collinearity (collinear points have zero area). Boundedness of the sSup comes from the upper_trivial lemma `UT.mta_le` (≤ 56/n), so α n ≥ 1/(32n²) and the IsBigO constant is 32.
- Axioms: `'Erdos507.erdos_507.variants.lower_erdos' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Compiles: 3 (1: timeout, fixed by replacing a simp_all over fin_cases and an nlinarith with explicit steps; 2: missing import Mathlib.Algebra.Field.ZMod; 3: clean + axioms)
- Date: 2026-11-12
