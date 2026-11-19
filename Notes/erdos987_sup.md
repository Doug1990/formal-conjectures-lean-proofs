# erdos987_sup

- Statement: `Erdos987.erdos_987.variants.sup_limsup_infty` (category research solved, Erdős [Er64b] "easy to see")
- Source: `FormalConjectures/ErdosProblems/987.lean` (line 83) in google-deepmind/formal-conjectures
- Proof file: `results/erdos987_sup.lean` (identical copy of `work/erdos987_sup.lean`). `additiveChar`/`e` are restated locally and targeted imports are used.

## Proof idea
Suppose the limsup is not ⊤. Then there are B and K with |S_n(k)| = |Σ_{j<n} e(k x_j)| ≤ B for all k ≥ K and all n. Put t_j = (K+1)x_j and T(d) = Σ_{j<n} e(d t_j), so |T(d)| ≤ B for every integer d ≠ 0 (use conjugation for d < 0). Fejér-type double counting (lemma `SL.ident`): Σ_{m,m'<N} |T(m−m')|² = Σ_{j,l<n} |Σ_{m<N} e(m(t_j−t_l))|². The right side is ≥ nN² (diagonal terms only). The left side is ≤ Nn² + N²B² (the m = m' terms are ≤ n²). With N = n² this gives n ≤ 1 + B², which is false for n = ⌈B²⌉ + 2. The hypothesis x_j ∈ (0,1) is not needed. The only compiler warning is an unused-variable lint for `hx`, and it comes from the statement itself. The checkout's external formal proof was not used.

## Axioms
'Erdos987.erdos_987.variants.sup_limsup_infty' depends on axioms: [propext, Classical.choice, Quot.sound]

## Date
2026-11-13
