# Erdos150.erdos_150.variants.seymour

- Source: `FormalConjectures/ErdosProblems/150.lean:93` (category research solved, Seymour's observation c(3m+2) ≥ 3^m)
- Verified file: `work/erdos150_seymour.lean`. `results/erdos150_seymour.lean` is an identical copy.

## Proof idea
The graph on Fin (3m+2) has vertex 0 = u and vertex 1 = v, and vertex 2+3j+t is position t ∈ {0,1,2} on path j. The m paths u–(2+3j)–(3+3j)–(4+3j)–v are internally disjoint and have length 4. For each choice function f : Fin m → Fin 3, T_f is the set of the vertices at position f(j) on path j. These sets are pairwise distinct, so there are 3^m of them. T_f disconnects u from v: the "side" predicate (v, or position > f(j)) is preserved along edges of G − T_f, which is shown by walk induction. T_f is minimal: if S ⊊ T_f, some path j₀ is intact in G − S, so u reaches v, and every other surviving vertex walks along its own path to u or to v. Then ncard (range T) = 3^m ≤ ncard(cuts) ≤ sSup, where BddAbove holds because ncard ≤ |Set (Set (Fin n))|. The defs IsMinimalCut and maxMinimalCuts are copied verbatim.

## Axioms
'Erdos150.erdos_150.variants.seymour' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-10
