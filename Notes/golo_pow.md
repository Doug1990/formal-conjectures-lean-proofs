# golo_pow

- Statements: `Arxiv.«1609.08688».maximalLength_pow` (line 279) and `Arxiv.«1609.08688».maximalLength_pow_eventually` (line 286), both category research solved
- Source: `FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean`

Proof idea: the key fact is that F is supermultiplicative, F(a)·F(b) ≤ F(ab). Both sups are attained
(`Nat.sSup_mem`, with the bound (n+2)² taken from the file's pigeonhole lemma). Given optimal sequences s over
[1,a] and t over [1,b], the product sequence lists, in lexicographic order over (u ∈ s, v ∈ t), the triples
i ↦ (u i − 1)·b + v i ∈ [1, ab]. This is the source's `⊗₂` construction, encoded into ℕ instead of `ℕ ×ₗ ℕ`.
It is still 2-increasing: if u <₂ u', the two coordinates where u increases also increase in the product, and
when u = u' the product inherits v <₂ v'. By induction, F(n)^j ≤ F(n^j), and F(n)^j = (n^e)^j = (n^j)^e.
That gives the "frequently" statement along m = n^N. For the "eventually" statement, F is monotone. For m ≥ n^J,
take j = log_n m, so that n^j ≤ m < n^{j+1}. Choose J > b/(e−b), so that (j+1)·b ≤ e·j. When b ≥ 0 this gives
m^b ≤ n^{(j+1)b} ≤ n^{ej} ≤ F(n^j) ≤ F(m). When b < 0, m^b ≤ 1 ≤ F(1) ≤ F(m).

Axioms (both): `propext, Classical.choice, Quot.sound`

Date: 2026-10-31
