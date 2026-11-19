# Erdos669.erdos_669.variants.k_two

- Source: `FormalConjectures/ErdosProblems/669.lean:191` (category research solved)
- Statement: `maxLinesExactly 2 n = n.choose 2 ∧ maxLinesAtLeast 2 n = n.choose 2`
- Date: 2026-11-10

**Proof idea.** Upper bound: every determined line is `affineSpan {p, q}` for some 2-subset `{p, q}` of S. So both line sets lie inside the image of `S.powersetCard 2`, which has at most C(n,2) elements. Lower bound: take the parabola points (i, i²) for i < n. If (c, c²) lies on the line through (a, a²) and (b, b²) with a ≠ b, write it as (1−r)p + rq. Then r(r−1)(b−a)² = 0 (one `linear_combination`), so c = a or c = b. This means every determined line meets S in exactly its two spanning points. So the pair ↦ line map is injective, and every line has exactly 2 (hence ≥ 2) points. Both line sets therefore have exactly C(n,2) elements, and both sSups equal C(n,2).

Definitions (`linesWithPointsFor`, `linesWithAtLeastPointsFor`, `lineCounts*`, `maxLines*`) are restated locally, with targeted Mathlib imports.

Axioms: `[propext, Classical.choice, Quot.sound]`
