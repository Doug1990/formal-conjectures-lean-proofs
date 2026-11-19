# Erdos1028.erdos_1028.variants.lower_bound

- Source: FormalConjectures/ErdosProblems/1028.lean:69 (category research solved, Erdős Er63d)
- Statement: `∀ᶠ n : ℕ in atTop, (n : ℝ) / 4 ≤ (H n : ℝ)`
- Proof file: results/erdos1028_lb.lean (identical to work/erdos1028_lb.lean). The defs `imbalance` and `H` are restated verbatim and the file uses targeted imports.

## Proof idea
We prove 20·m ≥ 6n − 120 for every admissible bound m, so 4·H(n) ≥ n for n ≥ 120. The simple one-vertex argument only gives (n−1)/4, which fails for n ≡ 1 mod 4 (the Paley-type colourings are locally balanced, and H(5) = 1). We average instead. For each b ∈ [6,n] and each of the 10 triples T ⊂ {1,…,5}, set c_T(b) = Σ_{x∈T} f(x,b). By pigeonhole some triple is unanimous at b, so Σ_T |c_T(b)| ≥ 12 (checked over all 32 sign cases). Hence some triple T has Σ_b |c_T(b)| ≥ 6(n−5)/5. Split B = [6,n] into the parts B⁺ and B⁻ where c_T > 0 and c_T ≤ 0. Since T < B', we have S(T ∪ B') = S(T) + S(B') + Σ_{b∈B'} c_T(b) and |S(T)| ≤ 9, so each |Σ_{B'} c_T| ≤ 2m + 9. Adding the two parts gives 6(n−5)/5 ≤ 4m + 18. H(n) itself is attained because the defining set is nonempty (m = n² with f ≡ 1), via `Nat.sInf_mem`.

Reusable: LB.S_union (imbalance of an ordered disjoint union), LB.abs_S_le (|S(X)| ≤ |X|²).

## Axioms
'Erdos1028.erdos_1028.variants.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-13
