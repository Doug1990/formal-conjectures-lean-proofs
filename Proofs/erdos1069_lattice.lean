import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace EuclideanGeometry

/-- A line in the plane: an affine subspace of `ℝ²` whose direction is one-dimensional. -/
def IsLine (L : AffineSubspace ℝ ℝ²) : Prop :=
  Module.finrank ℝ L.direction = 1

end EuclideanGeometry

open EuclideanGeometry

namespace Erdos1069

def richLines (s : Finset ℝ²) (k : ℕ) : Set (AffineSubspace ℝ ℝ²) :=
  {L | IsLine L ∧ k ≤ ((s : Set ℝ²) ∩ (L : Set ℝ²)).ncard}

/-! Helpers (the first two are copied from `Erdos211`). -/

theorem isLine_pair {a b : ℝ²} (hab : a ≠ b) : IsLine (line[ℝ, a, b]) := by
  unfold IsLine
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr hab)

theorem line_pair_eq {a b : ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    line[ℝ, a, b] = L := by
  apply (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ a b) ha).mpr
  apply Submodule.eq_of_le_of_finrank_eq
  · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem ha hb)
  · exact (isLine_pair hab).trans hL.symm

theorem richLines_finite' (s : Finset ℝ²) {k : ℕ} (hk : 2 ≤ k) : (richLines s k).Finite := by
  classical
  refine ((s.offDiag : Set (ℝ² × ℝ²)).toFinite.image (fun p => line[ℝ, p.1, p.2])).subset ?_
  rintro L ⟨hL, hcard⟩
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (Set.one_lt_ncard_iff (s := (s : Set ℝ²) ∩ (L : Set ℝ²)) (Set.toFinite _)).mp (by omega)
  exact ⟨(a, b), Finset.mem_coe.mpr (Finset.mem_offDiag.mpr ⟨ha.1, hb.1, hab⟩),
    line_pair_eq hL ha.2 hb.2 hab⟩

noncomputable def e0 : ℝ² := EuclideanSpace.single 0 1
noncomputable def e1 : ℝ² := EuclideanSpace.single 1 1

/-- The grid point `(i, j)`. -/
noncomputable def P (i j : ℕ) : ℝ² := (i : ℝ) • e0 + (j : ℝ) • e1

lemma P0 (i j : ℕ) : P i j 0 = i := by simp [P, e0, e1]
lemma P1 (i j : ℕ) : P i j 1 = j := by simp [P, e0, e1]

lemma P_inj {a b c d : ℕ} (h : P a b = P c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun v : ℝ² => v 0) h
  have h1 := congrArg (fun v : ℝ² => v 1) h
  simp only [P0, P1, Nat.cast_inj] at h0 h1
  exact ⟨h0, h1⟩

lemma e0_ne : e0 ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ² => v 0) h
  simp [e0] at this

lemma e1_ne : e1 ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ² => v 1) h
  simp [e1] at this

noncomputable def row (j : ℕ) : AffineSubspace ℝ ℝ² := AffineSubspace.mk' (P 0 j) (ℝ ∙ e0)
noncomputable def col (i : ℕ) : AffineSubspace ℝ ℝ² := AffineSubspace.mk' (P i 0) (ℝ ∙ e1)

lemma P_mem_row (i j : ℕ) : P i j ∈ row j := by
  rw [row, AffineSubspace.mem_mk', vsub_eq_sub]
  refine Submodule.mem_span_singleton.mpr ⟨i, ?_⟩
  simp [P]

lemma P_mem_col (i j : ℕ) : P i j ∈ col i := by
  rw [col, AffineSubspace.mem_mk', vsub_eq_sub]
  refine Submodule.mem_span_singleton.mpr ⟨j, ?_⟩
  simp [P]

lemma coord_of_mem_row {x : ℝ²} {j : ℕ} (h : x ∈ row j) : x 1 = j := by
  rw [row, AffineSubspace.mem_mk', vsub_eq_sub] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have := congrArg (fun v : ℝ² => v 1) hc
  simp [e0, P1] at this
  linarith

lemma coord_of_mem_col {x : ℝ²} {i : ℕ} (h : x ∈ col i) : x 0 = i := by
  rw [col, AffineSubspace.mem_mk', vsub_eq_sub] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have := congrArg (fun v : ℝ² => v 0) hc
  simp [e1, P0] at this
  linarith

/-- The `m × m` grid. -/
noncomputable def grid (m : ℕ) : Finset ℝ² :=
  ((Finset.range m) ×ˢ (Finset.range m)).image (fun p => P p.1 p.2)

lemma grid_card (m : ℕ) : (grid m).card = m ^ 2 := by
  rw [grid, Finset.card_image_of_injective, Finset.card_product, Finset.card_range, sq]
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  obtain ⟨h1, h2⟩ := P_inj h
  simp only at h1 h2
  rw [h1, h2]

lemma P_mem_grid {m i j : ℕ} (hi : i < m) (hj : j < m) : P i j ∈ grid m :=
  Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩, rfl⟩

lemma row_rich (m j : ℕ) (hj : j < m) : row j ∈ richLines (grid m) m := by
  refine ⟨?_, ?_⟩
  · unfold IsLine
    rw [row, AffineSubspace.direction_mk']
    exact finrank_span_singleton e0_ne
  · have hsub : (((Finset.range m).image (fun i => P i j) : Finset ℝ²) : Set ℝ²) ⊆
        (grid m : Set ℝ²) ∩ (row j : Set ℝ²) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨P_mem_grid (Finset.mem_range.mp hi) hj, P_mem_row i j⟩
    calc m = ((Finset.range m).image (fun i => P i j)).card := by
          rw [Finset.card_image_of_injective _ (fun a b h => (P_inj h).1), Finset.card_range]
      _ = _ := (Set.ncard_coe_finset _).symm
      _ ≤ _ := Set.ncard_le_ncard hsub

lemma col_rich (m i : ℕ) (hi : i < m) : col i ∈ richLines (grid m) m := by
  refine ⟨?_, ?_⟩
  · unfold IsLine
    rw [col, AffineSubspace.direction_mk']
    exact finrank_span_singleton e1_ne
  · have hsub : (((Finset.range m).image (fun j => P i j) : Finset ℝ²) : Set ℝ²) ⊆
        (grid m : Set ℝ²) ∩ (col i : Set ℝ²) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨P_mem_grid hi (Finset.mem_range.mp hj), P_mem_col i j⟩
    calc m = ((Finset.range m).image (fun j => P i j)).card := by
          rw [Finset.card_image_of_injective _ (fun a b h => (P_inj h).2), Finset.card_range]
      _ = _ := (Set.ncard_coe_finset _).symm
      _ ≤ _ := Set.ncard_le_ncard hsub

lemma row_inj {j j' : ℕ} (h : row j = row j') : j = j' := by
  have := coord_of_mem_row (h ▸ P_mem_row 0 j)
  rw [P1, Nat.cast_inj] at this
  exact this

lemma col_inj {i i' : ℕ} (h : col i = col i') : i = i' := by
  have := coord_of_mem_col (h ▸ P_mem_col i 0)
  rw [P0, Nat.cast_inj] at this
  exact this

lemma row_ne_col (i j : ℕ) : row j ≠ col i := by
  intro h
  have h0 := coord_of_mem_col (h ▸ P_mem_row 0 j)
  have h1 := coord_of_mem_col (h ▸ P_mem_row 1 j)
  rw [P0] at h0 h1
  have : ((0 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) := h0.trans h1.symm
  exact absurd (Nat.cast_inj.mp this) (by decide)

theorem erdos_1069.variants.lattice (m : ℕ) (hm : 2 ≤ m) :
    ∃ s : Finset ℝ², s.card = m ^ 2 ∧ 2 * m ≤ (richLines s m).ncard := by
  classical
  refine ⟨grid m, grid_card m, ?_⟩
  set T : Finset (AffineSubspace ℝ ℝ²) :=
    (Finset.range m).image row ∪ (Finset.range m).image col with hT
  have hdisj : Disjoint ((Finset.range m).image row) ((Finset.range m).image col) := by
    rw [Finset.disjoint_left]
    intro L hL1 hL2
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hL1
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hL2
    exact row_ne_col i j hi.symm
  have hTcard : T.card = 2 * m := by
    rw [hT, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b h => row_inj h),
      Finset.card_image_of_injective _ (fun a b h => col_inj h), Finset.card_range]
    ring
  have hsub : (T : Set (AffineSubspace ℝ ℝ²)) ⊆ richLines (grid m) m := by
    intro L hL
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hL) with h | h
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      exact row_rich m j (Finset.mem_range.mp hj)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact col_rich m i (Finset.mem_range.mp hi)
  rw [← hTcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (richLines_finite' _ hm)

end Erdos1069

#print axioms Erdos1069.erdos_1069.variants.lattice
