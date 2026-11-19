import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Density
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Common

open Filter Real
open scoped Pointwise

noncomputable def maxCosetDim (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : Set V) : ℕ :=
  sSup { Module.finrank K S.direction | (S : AffineSubspace K V) (_h : (S : Set V) ⊆ A) }

abbrev 𝔽 (p n : ℕ) := Fin n → ZMod p
abbrev 𝔽₂ (n : ℕ) := 𝔽 2 n

namespace Green51

noncomputable def guaranteedMaxCosetDim (n : ℕ) (α : ℝ) : ℕ :=
  sInf { maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A + A) | (A : Finset (𝔽₂ n)) (_h : A.dens ≥ α) }

open Module

lemma pivot {K : Type*} [Field K] [DecidableEq K] {n : ℕ} : ∀ (d : ℕ) (V : Submodule K (Fin n → K))
    (C : Finset (Fin n)) (p : Fin n → K), (∀ v ∈ V, ∀ i ∉ C, v i = 0) →
    d ≤ finrank K V → ∃ v ∈ V, d ≤ (C.filter fun i => v i + p i ≠ 0).card := by
  intro d
  induction d with
  | zero => intro V C p _ _; exact ⟨0, V.zero_mem, Nat.zero_le _⟩
  | succ d ih =>
    intro V C p hC hd
    have hne : V ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hd; omega
    obtain ⟨u, huV, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra h
      push Not at h
      exact hu0 (funext h)
    have hjC : j ∈ C := by
      by_contra h; exact hj (hC u huV j h)
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (LinearMap.proj j : (Fin n → K) →ₗ[K] K)
    have h2 := Submodule.finrank_le (LinearMap.range
      (LinearMap.proj j : (Fin n → K) →ₗ[K] K))
    rw [Module.finrank_fin_fun] at h1
    rw [Module.finrank_self] at h2
    set W := LinearMap.ker (LinearMap.proj j : (Fin n → K) →ₗ[K] K) with hW0
    have hW : n ≤ finrank K W + 1 := by omega
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq V W
    have hsup := Submodule.finrank_le (V ⊔ W)
    rw [Module.finrank_fin_fun] at hsup
    have hd' : d ≤ finrank K (V ⊓ W : Submodule K (Fin n → K)) := by omega
    have hC' : ∀ v ∈ V ⊓ W, ∀ i ∉ C.erase j, v i = 0 := by
      intro v hv i hi
      by_cases hij : i = j
      · subst hij
        have := hv.2
        simpa [W] using this
      · exact hC v hv.1 i (fun h => hi (Finset.mem_erase.2 ⟨hij, h⟩))
    set c := (1 - p j) / u j with hc
    obtain ⟨w, hwVW, hw⟩ := ih (V ⊓ W) (C.erase j) (c • u + p) hC' hd'
    have hwj : w j = 0 := by
      have := hwVW.2
      simpa [W] using this
    refine ⟨c • u + w, V.add_mem (V.smul_mem c huV) hwVW.1, ?_⟩
    have e : ∀ i, (c • u + w) i + p i = w i + (c • u + p) i := fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hjval : (c • u + w) j + p j ≠ 0 := by
      have : (c • u + w) j + p j = 1 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwj, add_zero, hc]
        field_simp
        ring
      rw [this]; exact one_ne_zero
    have hsub : insert j ((C.erase j).filter fun i => w i + (c • u + p) i ≠ 0) ⊆
        C.filter fun i => (c • u + w) i + p i ≠ 0 := by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Finset.mem_filter.2 ⟨hjC, hjval⟩
      · obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
        exact Finset.mem_filter.2 ⟨Finset.mem_of_mem_erase hi1, by rw [e]; exact hi2⟩
    have hnot : j ∉ (C.erase j).filter fun i => w i + (c • u + p) i ≠ 0 := by
      intro h
      exact (Finset.notMem_erase j C) (Finset.mem_of_mem_filter _ h)
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at this
    omega

lemma coset_le {K : Type*} [Field K] [DecidableEq K] {n : ℕ} (S : AffineSubspace K (Fin n → K)) (w : ℕ)
    (hS : ∀ y ∈ S, (Finset.univ.filter fun i => y i ≠ 0).card ≤ w) :
    finrank K S.direction ≤ w := by
  by_cases h : (S : Set (Fin n → K)).Nonempty
  · obtain ⟨p, hp⟩ := h
    obtain ⟨v, hv, hcard⟩ := pivot (finrank K S.direction) S.direction Finset.univ p
      (by simp) le_rfl
    have hm := hS _ (AffineSubspace.vadd_mem_of_mem_direction hv hp)
    exact hcard.trans hm
  · have h' : (S : Set (Fin n → K)) = ∅ := Set.not_nonempty_iff_eq_empty.1 h
    rw [(AffineSubspace.coe_eq_bot_iff S).1 h', AffineSubspace.direction_bot, finrank_bot]
    exact Nat.zero_le _

lemma maxCoset_le {K : Type*} [Field K] [DecidableEq K] {n : ℕ} (A : Set (Fin n → K)) (w : ℕ)
    (hA : ∀ y ∈ A, (Finset.univ.filter fun i => y i ≠ 0).card ≤ w) :
    maxCosetDim K (Fin n → K) A ≤ w := by
  unfold maxCosetDim
  apply csSup_le
  · exact ⟨0, ⊥, by simp, by simp⟩
  · rintro _ ⟨S, hS, rfl⟩
    exact coset_le S w fun y hy => hA y (hS hy)

lemma cb_bound (m : ℕ) : (Nat.centralBinom m) ^ 2 * (3 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hr := Nat.succ_mul_centralBinom_succ m
    have hpoly : (2 * (2 * m + 1)) ^ 2 * (3 * (m + 1) + 1) ≤ 16 * (m + 1) ^ 2 * (3 * m + 1) := by
      nlinarith
    have key : (m + 1) ^ 2 * ((Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1)) ≤
        (m + 1) ^ 2 * 16 ^ (m + 1) := by
      calc (m + 1) ^ 2 * ((Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1))
          = ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1) := by ring
        _ = (2 * (2 * m + 1)) ^ 2 * (3 * (m + 1) + 1) * (Nat.centralBinom m) ^ 2 := by
            rw [hr]; ring
        _ ≤ 16 * (m + 1) ^ 2 * (3 * m + 1) * (Nat.centralBinom m) ^ 2 :=
            Nat.mul_le_mul_right _ hpoly
        _ = 16 * (m + 1) ^ 2 * ((Nat.centralBinom m) ^ 2 * (3 * m + 1)) := by ring
        _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

lemma mid_bound (n : ℕ) : (n.choose (n / 2)) ^ 2 * (3 * (n / 2) + 1) ≤ (2 ^ n) ^ 2 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h2 : 2 * m / 2 = m := by omega
    rw [h2, ← Nat.centralBinom_eq_two_mul_choose]
    calc _ ≤ 16 ^ m := cb_bound m
      _ = (2 ^ (2 * m)) ^ 2 := by
          rw [← pow_mul, show 2 * m * 2 = 4 * m by ring, pow_mul]; norm_num
  · have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h2]
    have hB : (2 * m + 1).choose m ≤ 2 * Nat.centralBinom m := by
      rw [← Nat.choose_symm_half, Nat.choose_succ_succ', Nat.centralBinom_eq_two_mul_choose]
      have h1 := Nat.choose_le_middle (m + 1) (2 * m)
      have h3 : 2 * m / 2 = m := by omega
      rw [h3] at h1
      omega
    calc _ ≤ (2 * Nat.centralBinom m) ^ 2 * (3 * m + 1) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hB 2)
      _ = 4 * ((Nat.centralBinom m) ^ 2 * (3 * m + 1)) := by ring
      _ ≤ 4 * 16 ^ m := Nat.mul_le_mul_left _ (cb_bound m)
      _ = (2 ^ (2 * m + 1)) ^ 2 := by
          rw [← pow_mul]; rw [show (2 * m + 1) * 2 = 2 + 4 * m by ring, pow_add, pow_mul]
          norm_num

def ind {n : ℕ} (s : Finset (Fin n)) : 𝔽₂ n := fun j => if j ∈ s then 1 else 0

lemma ind_inj {n : ℕ} : Function.Injective (ind (n := n)) := by
  intro s t h
  ext j
  have := congrFun h j
  by_cases h1 : j ∈ s <;> by_cases h2 : j ∈ t <;> simp [ind, h1, h2] at this ⊢

def low (n k : ℕ) : Finset (Finset (Fin n)) := Finset.univ.filter fun s => s.card ≤ k

def AA (n k : ℕ) : Finset (𝔽₂ n) := (low n k).image ind

lemma sum_wt (n k : ℕ) : ∀ y ∈ (↑(AA n k + AA n k) : Set (𝔽₂ n)),
    (Finset.univ.filter fun i => y i ≠ 0).card ≤ 2 * k := by
  intro y hy
  rw [Finset.mem_coe, Finset.mem_add] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hb
  have hs' := (Finset.mem_filter.1 hs).2
  have ht' := (Finset.mem_filter.1 ht).2
  have hsub : (Finset.univ.filter fun i => (ind s + ind t) i ≠ 0) ⊆ s ∪ t := by
    intro i hi
    have hi' := (Finset.mem_filter.1 hi).2
    rw [Finset.mem_union]
    by_contra hc
    push Not at hc
    apply hi'
    simp [ind, hc.1, hc.2]
  calc _ ≤ (s ∪ t).card := Finset.card_le_card hsub
    _ ≤ s.card + t.card := Finset.card_union_le s t
    _ ≤ 2 * k := by omega

lemma count (n k : ℕ) (hk : 2 * k < n) :
    2 ^ n ≤ 2 * (low n k).card + (n - k - k - 1) * n.choose (n / 2) := by
  let high : Finset (Finset (Fin n)) := Finset.univ.filter fun s => n - k ≤ s.card
  let mid : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun s => k < s.card ∧ s.card < n - k
  have hhigh : high.card = (low n k).card := by
    refine Finset.card_nbij' compl compl ?_ ?_ ?_ ?_
    · intro s hs
      have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).2
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
      rw [Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_univ s
      rw [Fintype.card_fin] at this
      omega
    · intro s hs
      have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).2
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    · intro s _; exact compl_compl s
    · intro s _; exact compl_compl s
  have hmid : mid.card ≤ (n - k - k - 1) * n.choose (n / 2) := by
    have hsub : mid ⊆ (Finset.Ioo k (n - k)).biUnion
        (fun i => Finset.powersetCard i (Finset.univ : Finset (Fin n))) := by
      intro s hs
      have h1 := (Finset.mem_filter.1 hs).2
      rw [Finset.mem_biUnion]
      exact ⟨s.card, Finset.mem_Ioo.2 h1,
        Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩⟩
    calc mid.card ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ Finset.Ioo k (n - k),
          (Finset.powersetCard i (Finset.univ : Finset (Fin n))).card :=
          Finset.card_biUnion_le
      _ = ∑ i ∈ Finset.Ioo k (n - k), n.choose i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      _ ≤ (Finset.Ioo k (n - k)).card • n.choose (n / 2) :=
          Finset.sum_le_card_nsmul _ _ _ fun i _ => Nat.choose_le_middle i n
      _ = (n - k - k - 1) * n.choose (n / 2) := by
          rw [Nat.card_Ioo, smul_eq_mul]
  have hcov : (Finset.univ : Finset (Finset (Fin n))) ⊆ low n k ∪ mid ∪ high := by
    intro s _
    simp only [Finset.mem_union, low, mid, high, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_union_le (low n k ∪ mid) high
  have h3 := Finset.card_union_le (low n k) mid
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at h1
  omega

lemma arith (n r k : ℕ) (hn : 100 ≤ n) (hr : r * r ≤ n) (hk : k = (n - r - 1) / 2) :
    2500 * (n - k - k - 1) * (n - k - k - 1) ≤ 2401 * (3 * (n / 2) + 1) := by
  have h10 : 10 * r ≤ n := by
    by_cases h : 10 ≤ r
    · exact le_trans (Nat.mul_le_mul_right r h) hr
    · omega
  have hM : n - k - k - 1 ≤ r + 1 := by omega
  have hM2 : (n - k - k - 1) * (n - k - k - 1) ≤ (r + 1) * (r + 1) := Nat.mul_self_le_mul_self hM
  have e : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by ring
  rw [e] at hM2
  rw [mul_assoc]
  generalize (n - k - k - 1) * (n - k - k - 1) = q at hM2 ⊢
  generalize r * r = s at hr hM2
  omega

lemma dens_ok (n : ℕ) (hn : 100 ≤ n) :
    ((AA n ((n - Nat.sqrt n - 1) / 2)).dens : ℝ) ≥ 1 / 100 := by
  set r := Nat.sqrt n with hr0
  set k := (n - r - 1) / 2 with hk0
  have hr : r * r ≤ n := Nat.sqrt_le n
  have hrn : r ≤ n := Nat.sqrt_le_self n
  have hk : 2 * k < n := by omega
  have hc := count n k hk
  have ha := arith n r k hn hr hk0
  have hb := mid_bound n
  set B := n.choose (n / 2)
  set M := n - k - k - 1
  set L := (low n k).card
  have hsq : (50 * (M * B)) * (50 * (M * B)) ≤ (49 * 2 ^ n) * (49 * 2 ^ n) := by
    calc (50 * (M * B)) * (50 * (M * B)) = (2500 * M * M) * B ^ 2 := by ring
      _ ≤ (2401 * (3 * (n / 2) + 1)) * B ^ 2 := Nat.mul_le_mul_right _ ha
      _ = 2401 * (B ^ 2 * (3 * (n / 2) + 1)) := by ring
      _ ≤ 2401 * (2 ^ n) ^ 2 := Nat.mul_le_mul_left _ hb
      _ = (49 * 2 ^ n) * (49 * 2 ^ n) := by ring
  have hlin := Nat.mul_self_le_mul_self_iff.1 hsq
  have hL : 2 ^ n ≤ 100 * L := by omega
  have hcardA : (AA n k).card = L := Finset.card_image_of_injective _ ind_inj
  have hcardF : Fintype.card (𝔽₂ n) = 2 ^ n := by simp [ZMod.card]
  rw [Finset.dens_eq_card_div_card, hcardA, hcardF]
  push_cast
  have hL' : ((2 ^ n : ℕ) : ℝ) ≤ 100 * (L : ℝ) := by exact_mod_cast hL
  push_cast at hL'
  rw [ge_iff_le, le_div_iff₀ (by positivity)]
  linarith

theorem green_51.upper :
    ∃ α > 0, α ≤ 1 ∧ ∀ᶠ (n : ℕ) in atTop, (guaranteedMaxCosetDim n α : ℝ) < (n : ℝ) - sqrt n := by
  refine ⟨1 / 100, by norm_num, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 100] with n hn
  set r := Nat.sqrt n with hr0
  set k := (n - r - 1) / 2 with hk0
  have hrn : r ≤ n := Nat.sqrt_le_self n
  have hmem : maxCosetDim (ZMod 2) (𝔽₂ n) ↑(AA n k + AA n k) ∈
      { maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A + A) | (A : Finset (𝔽₂ n)) (_h : A.dens ≥ (1 / 100 : ℝ)) } :=
    ⟨AA n k, dens_ok n hn, rfl⟩
  have h1 : guaranteedMaxCosetDim n (1 / 100) ≤ 2 * k :=
    (Nat.sInf_le hmem).trans (maxCoset_le _ _ (sum_wt n k))
  have hrlt : r < n := Nat.sqrt_lt_self (by omega)
  have h2 : 2 * k + r + 1 ≤ n := by omega
  have h3 : ((2 * k : ℕ) : ℝ) + r + 1 ≤ n := by exact_mod_cast h2
  have h4 : ((guaranteedMaxCosetDim n (1 / 100) : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h5 : √(n : ℝ) < r + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  linarith

end Green51

#print axioms Green51.green_51.upper
