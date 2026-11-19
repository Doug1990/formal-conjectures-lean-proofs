import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

open scoped Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Classical in
noncomputable def distinctDistancesFrom {X : Type*} [MetricSpace X] (points : Finset X)
    (pt : X) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

namespace Erdos652

namespace First

lemma dDF_eq (points : Finset ℝ²) (p : ℝ²) :
    distinctDistancesFrom points p = #((points.erase p).image fun x => dist x p) := by
  unfold distinctDistancesFrom
  congr 2
  ext x
  simp only [Finset.mem_erase]

lemma unit (a b c d : ℝ) (h : (a - c) ^ 2 + (b - d) ^ 2 = 1) :
    dist (!₂[a, b]) (!₂[c, d]) = 1 := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  simp [h]

noncomputable def P (m : ℕ) (k : ℕ) : ℝ² :=
  !₂[(k : ℝ) / m, Real.sqrt (1 - ((k : ℝ) / m) ^ 2)]

lemma P_dist (m k : ℕ) (hk : k < m) : dist (P m k) (!₂[0, 0]) = 1 := by
  unfold P
  apply unit
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have h0 : (0 : ℝ) ≤ (k : ℝ) / m := div_nonneg (Nat.cast_nonneg k) hm.le
  have h1 : (k : ℝ) / m ≤ 1 := by
    rw [div_le_one hm]
    exact_mod_cast hk.le
  have h2 : 0 ≤ 1 - ((k : ℝ) / m) ^ 2 := by nlinarith
  rw [sub_zero, sub_zero, Real.sq_sqrt h2]
  ring

lemma P_inj (m : ℕ) (hm : 0 < m) : Function.Injective (P m) := by
  intro a b h
  have h' := congrArg (fun v : ℝ² => v 0) h
  simp only [P] at h'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (a : ℝ) / m = (b : ℝ) / m := by simpa using h'
  rw [div_left_inj' hm'] at this
  exact_mod_cast this

end First

theorem erdos_652.variants.first (n : ℕ) (hn : 2 ≤ n) :
    ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1 := by
  set m := n - 1 with hmdef
  have hm : 0 < m := by omega
  set S : Finset ℝ² := (Finset.range m).image (First.P m) with hS
  have hd : ∀ x ∈ S, dist x (!₂[0, 0]) = 1 := by
    intro x hx
    rw [hS, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact First.P_dist m k (Finset.mem_range.mp hk)
  have hnot : (!₂[(0:ℝ), 0]) ∉ S := by
    intro h
    have := hd _ h
    rw [dist_self] at this
    norm_num at this
  have hcardS : S.card = m := by
    rw [hS, Finset.card_image_of_injective _ (First.P_inj m hm), Finset.card_range]
  have hne : S.Nonempty := by
    rw [← Finset.card_pos, hcardS]
    exact hm
  refine ⟨insert (!₂[0, 0]) S, ?_, !₂[0, 0], Finset.mem_insert_self _ _, ?_⟩
  · rw [Finset.card_insert_of_notMem hnot, hcardS]
    omega
  · rw [First.dDF_eq, Finset.erase_insert hnot]
    have : (S.image fun x => dist x (!₂[(0:ℝ), 0])) = {1} := by
      ext d
      simp only [Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hd x hx
      · rintro rfl
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, hx, hd x hx⟩
    rw [this, Finset.card_singleton]

end Erdos652

#print axioms Erdos652.erdos_652.variants.first
