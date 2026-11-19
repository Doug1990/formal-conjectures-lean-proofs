# Erdos477.erdos_477.variants.degree_two_dvd_condition_b_ne_zero

- Source: `FormalConjectures/ErdosProblems/477.lean:72` (category research solved, AMS 12)
- Lean file: `results/erdos477_quad.lean` (identical copy of `work/erdos477_quad.lean`)
- Date: 2026-11-08, 4 compiles

**Proof idea.** Write b = a·m. Then f(k₁) − f(k₂) = a(k₁−k₂)(k₁+k₂+m), so every multiple 4a·s is a
difference of two values of f. For m = 2j+1, take k₁ = 2s−j and k₂ = −2s−j. For m = 2j, take
k₁ = 1+s−j and k₂ = s−1−j. If x ≠ y in A had x − y = 4a·s, then x + f(k₂) = y + f(k₁) would be two
different representations. So distinct elements of A lie in distinct classes mod 4|a|. On the other
hand, 4a·f(k) ≥ 4ac − b² (complete the square), so covering z + c − a·b² forces an element x ∈ A with
a·x ≤ a·z. Iterating gives 4|a|+1 distinct elements of A, and pigeonhole on residues mod 4|a|
(`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`) gives a contradiction. The hypothesis `b ≠ 0` is not
needed. The argument also covers b = 0, i.e. aX² + c, which generalises S_sq. The only compiler
warning is the unused `hb`. The statement is unchanged.

Axioms: `[propext, Classical.choice, Quot.sound]`
