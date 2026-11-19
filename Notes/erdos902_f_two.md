# Erdos902.erdos_902.variants.f_two

- Source: `FormalConjectures/ErdosProblems/902.lean:130` (category research solved), `f 2 = 7`.
- Verified file: `work/erdos902_f2.lean` (3 compiles + 1 axiom check, clean). This results file is an identical copy.

**Proof idea.** The upper bound uses Erdős's 7-vertex quadratic-residue tournament, the same witness as the file's `f_two_le`. For the lower bound, `F2.main` proves Erdős's general bound: every tournament on V with property S_n and |V| ≥ n has at least 2^(n+1) − 1 vertices. The proof is by induction on n. Fix a vertex v and let A be its in-neighbourhood. Then |A| ≥ n−1, since otherwise some n-set containing v ∪ A has no dominator. The subtournament on A has S_{n−1}, because a dominator of E ∪ {v} must lie in A. So |A| ≥ 2^n − 1. The in-degrees sum to m(m−1)/2 (`F2.sum_in`), which gives m − 1 ≥ 2(2^n − 1). Every m in the defining set of `f 2` is therefore ≥ 7.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-05
