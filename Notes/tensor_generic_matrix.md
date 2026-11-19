# isGenericRank_matrix

- Statement: `Arxiv.«0805.3777».isGenericRank_matrix (m n : ℕ) : IsGenericRank [m, n] (min m n)` (category textbook)
- Source: `FormalConjectures/Arxiv/0805.3777/TensorRank.lean:183`
- Date: 2026-10-31

**Proof idea.** U is the set of 2-holors T whose leading `min m n` square block `Sm T` has nonzero determinant. U is open because `T ↦ det (Sm T)` is continuous. U is dense because `det (Sm (T + c·E)) = charpoly(−Sm T)(c)`, where E is the holor with the leading identity block. That polynomial is monic, so it has finitely many roots, and `T + c·E ∈ U` for all c ≠ 0 close enough to 0 (`mem_closure_of_tendsto` along `𝓝[≠] 0`). Upper bound: every T is a sum of m row tensors `unitVec i ⊗ row_i` and also a sum of n column tensors `col_j ⊗ unitVec j`. Every 1-holor y is `CPRankMax1`, since `y = y ⊗ 1`. So cprank T ≤ min m n. Lower bound: by induction with `cases` on `CPRankMax`/`CPRankMax1`, a holor of CP rank ≤ r has entries `Σ_{l<r} u_l(i) v_l(j)`. So `Sm T = B * C` with B of width r, and an invertible block gives min m n = rank(Sm T) ≤ rank B ≤ r. Reusable 2-holor API: `idx`, `ext_idx`, `holor_sum_apply`, `mul_idx`, `vec_rank1`, `row_decomp`, `col_decomp`, `decomp`.

Axioms: `'Arxiv.«0805.3777».isGenericRank_matrix' depends on axioms: [propext, Classical.choice, Quot.sound]`

Compiles: 2. The first was clean apart from two deprecation warnings (`finite_setOf_isRoot`, `Set.diff_subset`); the second, with `#print axioms`, was clean.
