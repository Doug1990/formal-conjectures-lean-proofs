import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- We say a subset `S` of points is non-collinear for $n$ points
if it contains no $n$ points that lie on the same line. -/
def NonCollinearFor (n : ℕ) (S : Set P) : Prop :=
  ∀ (A : Set P), A ⊆ S → A.Finite → A.ncard = n → ¬ Collinear ℝ A

/-- A line in the plane: an affine subspace of `ℝ²` whose direction is one-dimensional. -/
def IsLine (L : AffineSubspace ℝ ℝ²) : Prop :=
  Module.finrank ℝ L.direction = 1

/--
The set of lines in $\mathbb{R}^2$ containing exactly $k$ points from a given set $S$.
-/
noncomputable def linesWithPointsFor (k : ℕ) (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  let determined_lines := { affineSpan ℝ {p, q} | (p ∈ S) (q ∈ S) (_ : p ≠ q) }
  { L ∈ determined_lines | (↑L ∩ S).ncard = k }

end EuclideanGeometry

open EuclideanGeometry

namespace Erdos588

noncomputable def numLinesWithPointsMax (k n : ℕ) : ℕ :=
  sSup {((linesWithPointsFor k S).ncard) | (S : Set ℝ²)
    (_ : S.ncard = n) (_ : S.Finite) (_ : NonCollinearFor (k + 1) S)}

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

theorem mem_lines {k : ℕ} {S : Set ℝ²} {L : AffineSubspace ℝ ℝ²}
    (h : L ∈ linesWithPointsFor k S) : IsLine L ∧ ((L : Set ℝ²) ∩ S).ncard = k := by
  have h' : (∃ p ∈ S, ∃ q ∈ S, ∃ (_ : p ≠ q), affineSpan ℝ {p, q} = L) ∧
      ((L : Set ℝ²) ∩ S).ncard = k := h
  obtain ⟨⟨p, -, q, -, hpq, rfl⟩, hc⟩ := h'
  exact ⟨isLine_pair hpq, hc⟩

theorem lines_finite (k : ℕ) (T : Finset ℝ²) : (linesWithPointsFor k ↑T).Finite := by
  classical
  refine ((T.offDiag : Set (ℝ² × ℝ²)).toFinite.image (fun p => line[ℝ, p.1, p.2])).subset ?_
  intro L hL
  have h' : (∃ p ∈ (T : Set ℝ²), ∃ q ∈ (T : Set ℝ²), ∃ (_ : p ≠ q), affineSpan ℝ {p, q} = L) ∧
      ((L : Set ℝ²) ∩ ↑T).ncard = k := hL
  obtain ⟨⟨p, hp, q, hq, hpq, rfl⟩, -⟩ := h'
  exact ⟨(p, q), Finset.mem_coe.2 (Finset.mem_offDiag.2 ⟨hp, hq, hpq⟩), rfl⟩

/-- Counting ordered pairs of distinct points: every line with exactly `k` points of `T`
contains `k(k-1)` of them, and distinct lines share none. -/
theorem count (k : ℕ) (T : Finset ℝ²) :
    (linesWithPointsFor k ↑T).ncard * (k * (k - 1)) ≤ T.card * (T.card - 1) := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : Finset (AffineSubspace ℝ ℝ²), (G : Set _) = linesWithPointsFor k ↑T :=
    ⟨(lines_finite k T).toFinset, (lines_finite k T).coe_toFinset⟩
  have hmem : ∀ L, L ∈ G ↔ L ∈ linesWithPointsFor k ↑T := fun L => by
    rw [← hG, Finset.mem_coe]
  let U : AffineSubspace ℝ ℝ² → Finset ℝ² := fun L => T.filter (· ∈ L)
  have hU : ∀ L ∈ G, (U L).card = k := by
    intro L hL
    have h1 := (mem_lines ((hmem L).1 hL)).2
    have h2 : ((U L : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ ↑T := by
      ext x
      simp [U, and_comm]
    rw [← Set.ncard_coe_finset, h2, h1]
  have hoff : ∀ L ∈ G, (U L).offDiag.card = k * (k - 1) := by
    intro L hL
    rw [Finset.offDiag_card, hU L hL, Nat.mul_sub_one]
  have hdisj : ∀ L ∈ G, ∀ L' ∈ G, L ≠ L' → Disjoint (U L).offDiag (U L').offDiag := by
    intro L hL L' hL' hne
    rw [Finset.disjoint_left]
    rintro ⟨p, q⟩ h1 h2
    simp only [Finset.mem_offDiag, U, Finset.mem_filter] at h1 h2
    exact hne ((line_pair_eq (mem_lines ((hmem L).1 hL)).1 h1.1.2 h1.2.1.2 h1.2.2).symm.trans
      (line_pair_eq (mem_lines ((hmem L').1 hL')).1 h2.1.2 h2.2.1.2 h2.2.2))
  have hsub : G.biUnion (fun L => (U L).offDiag) ⊆ T.offDiag := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_offDiag, U, Finset.mem_filter] at hx
    obtain ⟨L, -, h1, h2, h3⟩ := hx
    exact Finset.mem_offDiag.2 ⟨h1.1, h2.1, h3⟩
  calc (linesWithPointsFor k ↑T).ncard * (k * (k - 1)) = ∑ L ∈ G, (U L).offDiag.card := by
        rw [Finset.sum_congr rfl hoff, Finset.sum_const, smul_eq_mul, ← hG,
          Set.ncard_coe_finset]
    _ = (G.biUnion fun L => (U L).offDiag).card := by
        rw [Finset.card_biUnion (by intro L hL L' hL' hne; exact hdisj L hL L' hL' hne)]
    _ ≤ T.offDiag.card := Finset.card_le_card hsub
    _ = T.card * (T.card - 1) := by rw [Finset.offDiag_card, Nat.mul_sub_one]

theorem erdos_588.variants.trivial_upper (k n : ℕ) (hk : 2 ≤ k) :
    numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1) := by
  have hk1 : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
  have key : numLinesWithPointsMax k n ≤ n * (n - 1) / (k * (k - 1)) := by
    unfold numLinesWithPointsMax
    apply csSup_le'
    rintro m ⟨S, hn, hS, -, rfl⟩
    obtain ⟨T, rfl⟩ : ∃ T : Finset ℝ², (T : Set ℝ²) = S := ⟨hS.toFinset, hS.coe_toFinset⟩
    rw [Set.ncard_coe_finset] at hn
    subst hn
    exact (Nat.le_div_iff_mul_le hk1).2 (count k T)
  calc _ ≤ n * (n - 1) / (k * (k - 1)) * (k * (k - 1)) := Nat.mul_le_mul_right _ key
    _ ≤ n * (n - 1) := Nat.div_mul_le_self _ _

end Erdos588

#print axioms Erdos588.erdos_588.variants.trivial_upper
