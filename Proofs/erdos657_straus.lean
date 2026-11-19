import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fintype.Powerset

/-! Local restatements of the checkout definitions (FormalConjecturesForMathlib:
`Geometry/Metric.lean`, `Geometry/2d.lean`, `Data/Set/Triplewise.lean`, `Geometry/Euclidean.lean`). -/

open scoped Finset

local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

section Defs

variable {X : Type*} [MetricSpace X]

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

noncomputable def distinctDistances (points : Finset X) : ℕ :=
  #(distanceSet points)

end Defs

protected def Set.Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q

def Set.IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z ↦ ¬ _root_.IsIsosceles x y z

namespace Erdos657

namespace ST

/-- Vertex of the box with side lengths `√(2^i)` indexed by the subset `s`. -/
noncomputable def phi (k : ℕ) (s : Finset (Fin k)) : ℝ^k :=
  WithLp.toLp 2 (fun i => if i ∈ s then Real.sqrt (2 ^ (i : ℕ)) else 0)

noncomputable def D {k : ℕ} (u : Finset (Fin k)) : ℝ := ∑ i ∈ u, (2 : ℝ) ^ (i : ℕ)

lemma D_nonneg {k : ℕ} (u : Finset (Fin k)) : 0 ≤ D u :=
  Finset.sum_nonneg (fun _ _ => by positivity)

lemma D_inj {k : ℕ} {u v : Finset (Fin k)} (h : D u = D v) : u = v := by
  have hc : ∀ w : Finset (Fin k),
      D w = ((∑ i ∈ w.map Fin.valEmbedding, 2 ^ i : ℕ) : ℝ) := by
    intro w
    simp [D, Finset.sum_map]
  rw [hc, hc, Nat.cast_inj] at h
  exact (Finset.map_inj).mp (Finset.geomSum_injective le_rfl h)

lemma dist_phi {k : ℕ} (s t : Finset (Fin k)) :
    dist (phi k s) (phi k t) = Real.sqrt (D (symmDiff s t)) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have hterm : ∀ i, dist (phi k s i) (phi k t i) ^ 2 =
      if i ∈ symmDiff s t then (2 : ℝ) ^ (i : ℕ) else 0 := by
    intro i
    have hc : (Real.sqrt (2 ^ (i : ℕ))) ^ 2 = (2 : ℝ) ^ (i : ℕ) := Real.sq_sqrt (by positivity)
    simp only [phi, PiLp.toLp_apply, Real.dist_eq, sq_abs, Finset.mem_symmDiff]
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs, ht, hc]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_mem, Finset.univ_inter, D]

lemma key {k : ℕ} {a b a' b' : Finset (Fin k)}
    (h : dist (phi k a) (phi k b) = dist (phi k a') (phi k b')) :
    symmDiff a b = symmDiff a' b' := by
  rw [dist_phi, dist_phi, Real.sqrt_inj (D_nonneg _) (D_nonneg _)] at h
  exact D_inj h

lemma phi_inj (k : ℕ) : Function.Injective (phi k) := by
  intro a b h
  have h1 : dist (phi k a) (phi k b) = dist (phi k a) (phi k a) := by rw [h]
  have h2 := key h1
  rw [symmDiff_self] at h2
  exact symmDiff_eq_bot.mp h2

end ST

/--
Straus observed that for every $k$ there is a set of $2^k$ points in $\mathbb{R}^k$ with no
isosceles triangles which determines at most $2^k - 1$ distinct distances.
-/
theorem erdos_657.variants.straus (k : ℕ) :
    ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
      distinctDistances A ≤ 2 ^ k - 1 := by
  classical
  refine ⟨Finset.univ.image (ST.phi k), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (ST.phi_inj k), Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin]
  · intro x hx y hy z hz hxy hyz hxz
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy hz
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := hz
    have hab : a ≠ b := fun h => hxy (h ▸ rfl)
    have hbc : b ≠ c := fun h => hyz (h ▸ rfl)
    have hac : a ≠ c := fun h => hxz (h ▸ rfl)
    rintro (h | h | h)
    · have h' := ST.key h
      rw [symmDiff_comm b c] at h'
      exact hac (symmDiff_left_inj.mp h')
    · have h' := ST.key h
      rw [symmDiff_comm c a] at h'
      exact hab (symmDiff_left_inj.mp h').symm
    · have h' := ST.key h
      rw [symmDiff_comm a b] at h'
      exact hbc (symmDiff_left_inj.mp h').symm
  · unfold distinctDistances
    calc #(distanceSet (Finset.univ.image (ST.phi k)))
        ≤ ((Finset.univ.erase (∅ : Finset (Fin k))).image
            (fun u => Real.sqrt (ST.D u))).card := Finset.card_le_card ?_
      _ ≤ (Finset.univ.erase (∅ : Finset (Fin k))).card := Finset.card_image_le
      _ = 2 ^ k - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_finset, Fintype.card_fin]
    intro d hd
    simp only [distanceSet, Finset.mem_image, Finset.mem_offDiag] at hd
    obtain ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, rfl⟩ := hd
    simp only [Finset.mem_univ, true_and] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    refine Finset.mem_image.mpr ⟨symmDiff a b, ?_, (ST.dist_phi a b).symm⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    apply hxy
    rw [← Finset.bot_eq_empty, symmDiff_eq_bot] at h
    rw [h]

end Erdos657

#print axioms Erdos657.erdos_657.variants.straus
