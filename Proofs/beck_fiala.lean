import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace BeckFiala

namespace BF

variable {n m : ℕ}

/-- The floating coordinates of `x`. -/
noncomputable def Fl (x : Fin n → ℝ) : Finset (Fin n) := Finset.univ.filter (fun j => |x j| < 1)

lemma mem_Fl {x : Fin n → ℝ} {j : Fin n} : j ∈ Fl x ↔ |x j| < 1 := by
  simp [Fl]

/-- More unknowns than equations: a nonzero kernel vector supported on `F`. -/
lemma kernel (F : Finset (Fin n)) (A : Finset (Fin m)) (S : Fin m → Finset (Fin n))
    (h : A.card < F.card) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ (∀ j ∉ F, v j = 0) ∧ ∀ i ∈ A, ∑ j ∈ S i, v j = 0 := by
  let f : (Fin n → ℝ) →ₗ[ℝ] ((↥A ⊕ ↥Fᶜ) → ℝ) :=
    { toFun := fun v k => Sum.elim (fun i => ∑ j ∈ S i.1, v j) (fun j => v j.1) k
      map_add' := by
        intro v w; funext k; cases k <;> simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c v; funext k; cases k <;> simp [Finset.mul_sum] }
  have hdim : Module.finrank ℝ ((↥A ⊕ ↥Fᶜ) → ℝ) < Module.finrank ℝ (Fin n → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    have := F.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hk
  rw [LinearMap.mem_ker] at hv
  refine ⟨v, hv0, fun j hj => ?_, fun i hi => ?_⟩
  · have := congrFun hv (Sum.inr ⟨j, Finset.mem_compl.2 hj⟩)
    simpa [f] using this
  · have := congrFun hv (Sum.inl ⟨i, hi⟩)
    simpa [f] using this

/-- Move along `v` until one more coordinate is fixed. -/
lemma move (x v : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1) (hv : v ≠ 0)
    (hvF : ∀ j ∉ Fl x, v j = 0) :
    ∃ c : ℝ, (∀ j, |x j + c * v j| ≤ 1) ∧
      (Fl (fun j => x j + c * v j)).card < (Fl x).card := by
  classical
  let J := Finset.univ.filter (fun j => v j ≠ 0)
  have hJ : J.Nonempty := by
    by_contra h
    apply hv
    funext j
    by_contra hj
    exact h ⟨j, by simpa [J] using hj⟩
  let μ : Fin n → ℝ := fun j => if 0 < v j then (1 - x j) / v j else (-1 - x j) / v j
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image J μ hJ
  have key : ∀ j, v j ≠ 0 → 0 < μ j ∧ μ j * v j = (if 0 < v j then 1 else -1) - x j := by
    intro j hj
    have hF : |x j| < 1 := by
      by_contra h; exact hj (hvF j (by rw [mem_Fl]; exact h))
    rw [abs_lt] at hF
    rcases lt_or_gt_of_ne hj with h | h
    · simp only [μ, if_neg (not_lt.2 h.le)]
      exact ⟨div_pos_of_neg_of_neg (by linarith) h, by field_simp⟩
    · simp only [μ, if_pos h]
      exact ⟨div_pos (by linarith) h, by field_simp⟩
  have hv0 : v j0 ≠ 0 := by simpa [J] using hj0
  obtain ⟨hpos, he0⟩ := key j0 hv0
  have hbound : ∀ j, |x j + μ j0 * v j| ≤ 1 := by
    intro j
    by_cases hj : v j = 0
    · simp [hj, hx j]
    · have hle : μ j0 ≤ μ j := hmin j (by simp [J, hj])
      obtain ⟨hμ, he⟩ := key j hj
      have hxj := hx j
      rw [abs_le] at hxj ⊢
      rcases lt_or_gt_of_ne hj with h | h
      · rw [if_neg (not_lt.2 h.le)] at he
        have h1 : μ j * v j ≤ μ j0 * v j := mul_le_mul_of_nonpos_right hle h.le
        have h2 : μ j0 * v j < 0 := mul_neg_of_pos_of_neg hpos h
        constructor <;> linarith
      · rw [if_pos h] at he
        have h1 : μ j0 * v j ≤ μ j * v j := mul_le_mul_of_nonneg_right hle h.le
        have h2 : 0 < μ j0 * v j := mul_pos hpos h
        constructor <;> linarith
  refine ⟨μ j0, hbound, Finset.card_lt_card ?_⟩
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j0, ?_, ?_⟩
    · by_contra h
      exact hv0 (hvF j0 h)
    · simp only [mem_Fl]
      have e : x j0 + μ j0 * v j0 = (if 0 < v j0 then 1 else -1) := by rw [he0]; ring
      rw [e]
      split_ifs <;> norm_num
  · intro j hj
    simp only [mem_Fl] at hj ⊢
    by_contra h
    have := hvF j (by rw [mem_Fl]; exact h)
    rw [this, mul_zero, add_zero] at hj
    exact h hj

/-- Double counting: active sets are fewer than floating coordinates. -/
lemma count (t : ℕ) (S : Fin m → Finset (Fin n)) (F : Finset (Fin n)) (A : Finset (Fin m))
    (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t)
    (hA : ∀ i ∈ A, t < ((S i).filter (· ∈ F)).card) :
    A.card * (t + 1) ≤ t * F.card := by
  have h1 : ∀ i, ((S i).filter (· ∈ F)).card = (F.filter (· ∈ S i)).card := by
    intro i
    rw [Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  calc A.card * (t + 1) = ∑ _i ∈ A, (t + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ i ∈ A, ((S i).filter (· ∈ F)).card := Finset.sum_le_sum (fun i hi => hA i hi)
    _ = ∑ i ∈ A, ∑ j ∈ F, if j ∈ S i then 1 else 0 := by
        simp only [h1, Finset.card_filter]
    _ = ∑ j ∈ F, ∑ i ∈ A, if j ∈ S i then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ _j ∈ F, t := by
        apply Finset.sum_le_sum
        intro j _
        rw [← Finset.card_filter]
        exact le_trans (Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.subset_univ A))) (hdeg j)
    _ = t * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Rounding error on a set with at most `t` floating coordinates. -/
lemma bound (t : ℕ) (ht : 1 ≤ t) (x χ : Fin n → ℝ)
    (hχ : ∀ j, χ j = 1 ∨ χ j = -1) (hfix : ∀ j ∉ Fl x, χ j = x j) (T : Finset (Fin n))
    (hT : (T.filter (· ∈ Fl x)).card ≤ t) :
    |∑ j ∈ T, (χ j - x j)| < 2 * t := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have e : ∑ j ∈ T, (χ j - x j) = ∑ j ∈ T.filter (· ∈ Fl x), (χ j - x j) := by
    rw [Finset.sum_filter_of_ne]
    intro j _ h
    by_contra hj
    exact h (by rw [hfix j hj, sub_self])
  rw [e]
  rcases (T.filter (· ∈ Fl x)).eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty, abs_zero]; linarith
  · calc |∑ j ∈ T.filter (· ∈ Fl x), (χ j - x j)|
          ≤ ∑ j ∈ T.filter (· ∈ Fl x), |χ j - x j| := Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _j ∈ T.filter (· ∈ Fl x), (2 : ℝ) := by
          apply Finset.sum_lt_sum_of_nonempty h
          intro j hj
          have hj' : |x j| < 1 := mem_Fl.1 (Finset.mem_filter.1 hj).2
          rw [abs_lt] at hj' ⊢
          rcases hχ j with h' | h' <;> rw [h'] <;> constructor <;> linarith [hj'.1, hj'.2]
      _ = 2 * ((T.filter (· ∈ Fl x)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ 2 * t := by
          have : ((T.filter (· ∈ Fl x)).card : ℝ) ≤ t := by exact_mod_cast hT
          linarith

lemma main (t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n))
    (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    ∀ k, ∀ x : Fin n → ℝ, (Fl x).card = k → (∀ j, |x j| ≤ 1) →
      ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧ (∀ j ∉ Fl x, χ j = x j) ∧
        ∀ i, |∑ j ∈ S i, (χ j - x j)| < 2 * t := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x hk hx
  rcases (Fl x).eq_empty_or_nonempty with hF | hF
  · refine ⟨x, fun j => ?_, fun j _ => rfl, fun i => ?_⟩
    · have h1 : ¬ |x j| < 1 := by rw [← mem_Fl, hF]; simp
      have h2 : |x j| = 1 := le_antisymm (hx j) (not_lt.1 h1)
      rcases (abs_eq (zero_le_one' ℝ)).1 h2 with h | h
      exacts [Or.inl h, Or.inr h]
    · simp only [sub_self, Finset.sum_const_zero, abs_zero]
      have : (1:ℝ) ≤ t := by exact_mod_cast ht
      linarith
  · let A := Finset.univ.filter (fun i => t < ((S i).filter (· ∈ Fl x)).card)
    have hcount := count t S (Fl x) A hdeg (fun i hi => (Finset.mem_filter.1 hi).2)
    have hAF : A.card < (Fl x).card := by
      have := hF.card_pos
      by_contra h
      have h' : (Fl x).card ≤ A.card := not_lt.1 h
      have := Nat.mul_le_mul_right (t + 1) h'
      nlinarith
    obtain ⟨v, hv0, hvF, hvA⟩ := kernel (Fl x) A S hAF
    obtain ⟨c, hc, hlt⟩ := move x v hx hv0 hvF
    obtain ⟨χ, hχ, hfix, hsum⟩ :=
      ih _ (by rw [← hk]; exact hlt) (fun j => x j + c * v j) rfl hc
    have hfix' : ∀ j ∉ Fl x, χ j = x j := by
      intro j hj
      have hv : v j = 0 := hvF j hj
      have hj' : j ∉ Fl (fun j => x j + c * v j) := by
        rw [mem_Fl] at hj ⊢
        rw [hv, mul_zero, add_zero]; exact hj
      rw [hfix j hj', hv, mul_zero, add_zero]
    refine ⟨χ, hχ, hfix', fun i => ?_⟩
    by_cases hi : i ∈ A
    · have e : ∑ j ∈ S i, (χ j - x j) = ∑ j ∈ S i, (χ j - (x j + c * v j)) := by
        have : ∑ j ∈ S i, (χ j - (x j + c * v j))
            = ∑ j ∈ S i, (χ j - x j) - c * ∑ j ∈ S i, v j := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro j _; ring
        rw [this, hvA i hi, mul_zero, sub_zero]
      rw [e]; exact hsum i
    · apply bound t ht x χ hχ hfix' (S i)
      have : ¬ t < ((S i).filter (· ∈ Fl x)).card :=
        fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      omega

end BF

theorem beck_fiala_theorem (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n))
    (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1 := by
  obtain ⟨χ, hχ, -, hsum⟩ :=
    BF.main t ht S hdeg _ (fun _ => (0:ℝ)) rfl (fun j => by simp)
  refine ⟨χ, hχ, fun i => ?_⟩
  have hs : |∑ j ∈ S i, χ j| < 2 * (t:ℝ) := by simpa using hsum i
  let z : Fin n → ℤ := fun j => if χ j = 1 then 1 else -1
  have hz : ∀ j, (z j : ℝ) = χ j := by
    intro j; simp only [z]; split_ifs with h
    · simp [h]
    · rcases hχ j with h' | h'
      · exact absurd h' h
      · simp [h']
  have e : ∑ j ∈ S i, χ j = ((∑ j ∈ S i, z j : ℤ) : ℝ) := by
    push_cast; simp only [hz]
  rw [e] at hs ⊢
  rw [abs_lt] at hs
  have a1 : -(2 * (t:ℤ)) < ∑ j ∈ S i, z j := by exact_mod_cast hs.1
  have a2 : ∑ j ∈ S i, z j < 2 * (t:ℤ) := by exact_mod_cast hs.2
  rw [abs_le]
  have b1 : -(2 * (t:ℤ) - 1) ≤ ∑ j ∈ S i, z j := by omega
  have b2 : ∑ j ∈ S i, z j ≤ 2 * (t:ℤ) - 1 := by omega
  constructor
  · exact_mod_cast b1
  · exact_mod_cast b2

end BeckFiala

#print axioms BeckFiala.beck_fiala_theorem
