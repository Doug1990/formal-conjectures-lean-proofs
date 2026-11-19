import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

abbrev 𝔽 (p n : ℕ) := Fin n → ZMod p
abbrev 𝔽₂ (n : ℕ) := 𝔽 2 n

open Filter Fintype
open scoped ENNReal Pointwise

namespace Green40

def hammingBall (n r : ℕ) : Set (𝔽₂ n) :=
  {x | hammingNorm x ≤ r}

def IsCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) : Prop :=
  (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ

noncomputable def minDensity (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule (ZMod 2) (𝔽₂ n)) (_ : IsCoveringSubspace n r V),
    (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

noncomputable def f (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensity n r) atTop

/-- syndrome map -/
def syn {n : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : Fin n → W) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] W where
  toFun x := ∑ i, x i • σ i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

def ind {n : ℕ} (S : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ S then 1 else 0

lemma syn_ind {n : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : Fin n → W)
    (S : Finset (Fin n)) : syn σ (ind S) = ∑ i ∈ S, σ i := by
  simp [syn, ind, ite_smul, Finset.sum_ite_mem]

lemma ind_mem {n r : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ r) : ind S ∈ hammingBall n r := by
  show hammingNorm (ind S) ≤ r
  unfold hammingNorm
  refine le_trans (Finset.card_le_card ?_) hS
  intro i hi
  by_contra hc
  simp [ind, hc] at hi

lemma cover_r {n r : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : Fin n → W)
    (hrep : ∀ w, ∃ S : Finset (Fin n), S.card ≤ r ∧ ∑ i ∈ S, σ i = w) :
    IsCoveringSubspace n r (LinearMap.ker (syn σ)) := by
  unfold IsCoveringSubspace
  ext x
  simp only [Set.mem_univ, iff_true]
  obtain ⟨S, hS, hsum⟩ := hrep (syn σ x)
  refine ⟨x - ind S, ?_, ind S, ind_mem S hS, sub_add_cancel _ _⟩
  show x - ind S ∈ LinearMap.ker (syn σ)
  rw [LinearMap.mem_ker, map_sub, syn_ind, hsum, sub_self]

lemma card_space (n : ℕ) : Nat.card (𝔽₂ n) = 2 ^ n := by
  simp [Nat.card_eq_fintype_card, ZMod.card]

lemma ker_card {n : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : Fin n → W)
    (hsurj : ∀ w, ∃ x, syn σ x = w) :
    Nat.card (LinearMap.ker (syn σ)) * Nat.card W ≤ 2 ^ n := by
  choose t ht using hsurj
  have hinj : Function.Injective
      (fun p : LinearMap.ker (syn σ) × W => (p.1 : Fin n → ZMod 2) + t p.2) := by
    rintro ⟨⟨v, hv⟩, w⟩ ⟨⟨v', hv'⟩, w'⟩ h
    simp only at h
    have hw : w = w' := by
      have := congrArg (syn σ) h
      rwa [map_add, map_add, LinearMap.mem_ker.1 hv, LinearMap.mem_ker.1 hv', zero_add,
        zero_add, ht, ht] at this
    subst hw
    have : v = v' := add_right_cancel h
    subst this
    rfl
  have h1 := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, card_space] at h1

/-! Size of the Hamming ball. -/

def supp {n : ℕ} (x : Fin n → ZMod 2) : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)

def T (n r : ℕ) (x : Fin n → ZMod 2) : Finset ℕ :=
  (supp x).map Fin.valEmbedding ∪ Finset.Ico n (n + r - (supp x).card)

lemma T_mem {n r : ℕ} (x : Fin n → ZMod 2) (i : Fin n) : (i : ℕ) ∈ T n r x ↔ i ∈ supp x := by
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨a, ha, hai⟩ := Finset.mem_map.1 h
      have : a = i := Fin.ext hai
      rwa [← this]
    · have := (Finset.mem_Ico.1 h).1
      exact absurd i.2 (by omega)
  · intro h
    exact Finset.mem_union_left _ (Finset.mem_map_of_mem _ h)

lemma T_mem_powersetCard {n r : ℕ} (x : Fin n → ZMod 2) (hx : (supp x).card ≤ r) :
    T n r x ∈ Finset.powersetCard r (Finset.range (n + r)) := by
  rw [Finset.mem_powersetCard]
  constructor
  · intro a ha
    rw [Finset.mem_range]
    rcases Finset.mem_union.1 ha with h | h
    · obtain ⟨b, _, rfl⟩ := Finset.mem_map.1 h
      have := b.2
      simp only [Fin.valEmbedding_apply]
      omega
    · have := (Finset.mem_Ico.1 h).2
      omega
  · unfold T
    rw [Finset.card_union_of_disjoint, Finset.card_map, Nat.card_Ico]
    · omega
    · rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨b, _, rfl⟩ := Finset.mem_map.1 ha
      have := b.2
      have := (Finset.mem_Ico.1 hb).1
      simp only [Fin.valEmbedding_apply] at this
      omega

lemma ball_card (n r : ℕ) : Nat.card (hammingBall n r) ≤ (n + r).choose r := by
  have hinj : Function.Injective (fun x : hammingBall n r =>
      (⟨T n r x.1, T_mem_powersetCard x.1 x.2⟩ :
        {s // s ∈ Finset.powersetCard r (Finset.range (n + r))})) := by
    intro x y h
    have h' : T n r x.1 = T n r y.1 := congrArg Subtype.val h
    apply Subtype.ext
    funext i
    have hi : i ∈ supp x.1 ↔ i ∈ supp y.1 := by
      rw [← T_mem (r := r), ← T_mem (r := r), h']
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have key2 : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b := by decide
    exact key2 _ _ hi
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card {s // s ∈ Finset.powersetCard r (Finset.range (n + r))} =
      (n + r).choose r := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard, Finset.card_range]
  rwa [h2] at h1

lemma key {n r : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : Fin n → W)
    (hrep : ∀ w, ∃ S : Finset (Fin n), S.card ≤ r ∧ ∑ i ∈ S, σ i = w) :
    ∃ V, IsCoveringSubspace n r V ∧
      Nat.card V * Nat.card (hammingBall n r) * Nat.card W ≤ 2 ^ n * (n + r).choose r := by
  refine ⟨_, cover_r σ hrep, ?_⟩
  have hVW := ker_card σ (fun w => by
    obtain ⟨S, _, hS⟩ := hrep w
    exact ⟨ind S, by rw [syn_ind, hS]⟩)
  have hH := ball_card n r
  rw [Nat.mul_right_comm]
  exact Nat.mul_le_mul hVW hH

lemma md_le (n r C D : ℕ) (hD : D ≠ 0) (h : ∃ V, IsCoveringSubspace n r V ∧
    Nat.card V * Nat.card (hammingBall n r) * D ≤ 2 ^ n * C) :
    minDensity n r ≤ (C : ℝ≥0∞) / D := by
  obtain ⟨V, hV, hle⟩ := h
  refine le_trans (iInf₂_le V hV) ?_
  apply ENNReal.div_le_of_le_mul
  rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hD))
    (Or.inl (ENNReal.natCast_ne_top D))]
  have hle' : Nat.card V * Nat.card (hammingBall n r) * D ≤ C * 2 ^ n := by
    rw [Nat.mul_comm C]; exact hle
  exact_mod_cast hle'

lemma card_nonzero (k : ℕ) :
    Fintype.card {w : Fin k → ZMod 2 // w ≠ 0} = 2 ^ k - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

lemma exists_block (r k : ℕ) : ∃ σ : Fin (r * (2 ^ k - 1)) → (Fin r → Fin k → ZMod 2),
    ∀ w, ∃ S : Finset (Fin (r * (2 ^ k - 1))), S.card ≤ r ∧ ∑ i ∈ S, σ i = w := by
  classical
  have hc : Fintype.card (Fin r × {w : Fin k → ZMod 2 // w ≠ 0}) = r * (2 ^ k - 1) := by
    rw [Fintype.card_prod, Fintype.card_fin, card_nonzero]
  let e := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun i => Pi.single (e i).1 (e i).2.1, fun w => ?_⟩
  refine ⟨Finset.univ.filter (fun i => (e i).2.1 = w (e i).1), ?_, ?_⟩
  · calc _ ≤ (Finset.univ : Finset (Fin r)).card := by
          apply Finset.card_le_card_of_injOn (fun i => (e i).1)
          · intro a _; simp
          · intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
            simp only at hab
            apply e.injective
            apply Prod.ext hab
            apply Subtype.ext
            rw [ha, hb]
            exact congrArg w hab
      _ = r := by simp
  · funext j
    rw [Finset.sum_apply]
    by_cases hw : w j = 0
    · rw [hw]
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Pi.single_apply]
      split_ifs with h
      · rw [hi, ← h, hw]
      · rfl
    · let i0 := e.symm (j, ⟨w j, hw⟩)
      have he : e i0 = (j, ⟨w j, hw⟩) := by simp [i0]
      rw [Finset.sum_eq_single_of_mem i0]
      · rw [he]; simp
      · simp [he]
      · intro i hi hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [Pi.single_apply]
        split_ifs with h
        · exfalso
          apply hne
          apply e.injective
          rw [he]
          apply Prod.ext h.symm
          apply Subtype.ext
          show (e i).2.1 = w j
          rw [hi, h]
        · rfl

lemma pos_case (r m : ℕ) :
    minDensity (r * (2 ^ m - 1)) r ≤ (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞) := by
  obtain ⟨σ, hσ⟩ := exists_block r m
  obtain ⟨V, hV, hle⟩ := key σ hσ
  have hW : Nat.card (Fin r → Fin m → ZMod 2) = (2 ^ m) ^ r := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, Fintype.card_fin]
  have hn : r * (2 ^ m - 1) + r = r * 2 ^ m := by
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel h1]
  have hC : (r * (2 ^ m - 1) + r).choose r * r.factorial ≤ (r * (2 ^ m - 1) + r) ^ r := by
    rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ _
  rw [hW, hn] at hle
  rw [hn, Nat.mul_pow] at hC
  have hP : 0 < (2 ^ m) ^ r := by positivity
  have hfin : Nat.card V * Nat.card (hammingBall (r * (2 ^ m - 1)) r) * r.factorial ≤
      2 ^ (r * (2 ^ m - 1)) * r ^ r := by
    apply Nat.le_of_mul_le_mul_right _ hP
    calc _ = Nat.card V * Nat.card (hammingBall (r * (2 ^ m - 1)) r) * (2 ^ m) ^ r *
          r.factorial := by rw [Nat.mul_right_comm]
      _ ≤ 2 ^ (r * (2 ^ m - 1)) * (r * 2 ^ m).choose r * r.factorial :=
          Nat.mul_le_mul_right _ hle
      _ = 2 ^ (r * (2 ^ m - 1)) * ((r * 2 ^ m).choose r * r.factorial) := Nat.mul_assoc _ _ _
      _ ≤ 2 ^ (r * (2 ^ m - 1)) * (r ^ r * (2 ^ m) ^ r) := Nat.mul_le_mul_left _ hC
      _ = 2 ^ (r * (2 ^ m - 1)) * r ^ r * (2 ^ m) ^ r := (Nat.mul_assoc _ _ _).symm
  have := md_le _ r (r ^ r) r.factorial (Nat.factorial_ne_zero r) ⟨V, hV, hfin⟩
  simpa [Nat.cast_pow] using this

lemma zero_case (m : ℕ) : minDensity m 0 ≤ 1 := by
  have hrep : ∀ w : Fin 0 → ZMod 2, ∃ S : Finset (Fin m), S.card ≤ 0 ∧
      ∑ i ∈ S, (0 : Fin m → Fin 0 → ZMod 2) i = w :=
    fun w => ⟨∅, by simp, Subsingleton.elim _ _⟩
  obtain ⟨V, hV, hle⟩ := key _ hrep
  have h1 : Nat.card (Fin 0 → ZMod 2) = 1 := by simp
  rw [h1, Nat.add_zero, Nat.choose_zero_right] at hle
  have := md_le m 0 1 1 one_ne_zero ⟨V, hV, hle⟩
  simpa using this

theorem green_40.upper_bound (r : ℕ) : f r ≤ (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞) := by
  show liminf (fun n ↦ minDensity n r) atTop ≤ _
  apply Filter.liminf_le_of_frequently_le'
  rw [Filter.frequently_atTop]
  intro m
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨m, le_rfl, ?_⟩
    simpa using zero_case m
  · refine ⟨r * (2 ^ m - 1), ?_, pos_case r m⟩
    have := Nat.lt_two_pow_self (n := m)
    calc m ≤ 2 ^ m - 1 := by omega
      _ ≤ r * (2 ^ m - 1) := Nat.le_mul_of_pos_left _ hr

end Green40

#print axioms Green40.green_40.upper_bound
