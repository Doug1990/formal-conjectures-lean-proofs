# dfs_lemma3

- Statement: `SimpleGraph.lemma3` (Lemma 3 of Erdős–Fajtlowicz–Staton, category API), source `FormalConjectures/Paper/DegreeSequencesTriangleFree.lean:262`.
- Claim: for every n > 0 there is a bipartite graph on `Fin (8 * n)` with minimum degree n + 1 and `degreeSequenceMultiplicity = 3`.

## Proof idea
The construction is my own; it is not taken from the paper. The vertex set is Fin 8 × Fin n, transported to Fin (8n) via `finProdFinEquiv`. Rows R1..R4 form one side and columns C1..C4 the other. Each row/column block pair is a half graph H (i + j ≥ n − 1), a shifted half graph H' (i + j ≥ n), complete (J), or empty. The pattern is:

| | C1 | C2 | C3 | C4 |
|---|---|---|---|---|
| R1 | H' | H' | J | H |
| R2 | J | H' | H | H |
| R3 | H | H | H | J |
| R4 | H' | J | H | H |

Vertex index k in a block then has degree 3k + n + 1 + off, where off = 0 for R1, C1, C2, off = 1 for R2, R4, and off = 2 for R3, C3, C4. The degree therefore determines k and the class of off. Each class has at most 3 blocks, so every degree occurs at most 3 times, which is proved by an injection into Fin 3. The degree n + 1 occurs exactly 3 times (k = 0 in R1, C1, C2). The minimum degree is n + 1, and the 2-colouring is row vs. column.

The degree count works in steps:
1. Split the neighbour count with `Fintype.sum_prod_type`.
2. Count each block as a Finset.Ico in `range n`.
3. Run `fin_cases` over the 8 blocks.
4. Transfer the degrees with `Iso.comap … |>.degree_eq`.

## Axioms
`'SimpleGraph.lemma3' depends on axioms: [propext, Classical.choice, Quot.sound]`

Note: the compile output contains many `PANIC at Lean.Expr.appArg!` lines. These are internal elaborator messages, probably from `decide`/`fin_cases`/`simp` on the `![…]` tables. They are not errors, and the file compiles with no errors or warnings.

Date: 2026-11-02
