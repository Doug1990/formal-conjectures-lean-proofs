import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Topology

/-! Definitions restated from FormalConjecturesForMathlib/Data/Set/Density.lean -/
namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

open Set

namespace Erdos12

/--
A set `A` is "good" if it is infinite and there are no distinct `a,b,c` in `A`
such that `a ∣ (b+c)` and `b > a`, `c > a`.
-/
abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c

namespace DZ

open Classical

noncomputable def cnt (S : Set ℕ) (N : ℕ) : ℕ := ((Finset.range N).filter (· ∈ S)).card

def Sc (S : Set ℕ) (a t : ℕ) : Set ℕ := {x | x ∈ S ∧ a < x ∧ x % a = t}

def Rs (m a : ℕ) : Finset ℕ := (Finset.range a).filter (Nat.gcd m a ∣ ·)

lemma cap {S : Set ℕ} {m : ℕ} (_hm : 0 < m) (hS : ∀ x ∈ S, ∀ y ∈ S, x ≡ y [MOD m]) (N : ℕ) :
    m * cnt S N ≤ N + m := by
  have h1 : cnt S N ≤ N / m + 1 := by
    unfold cnt
    calc ((Finset.range N).filter (· ∈ S)).card ≤ (Finset.range (N / m + 1)).card := by
          apply Finset.card_le_card_of_injOn (fun x => x / m)
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx ⊢
            have := Nat.div_le_div_right (c := m) hx.1.le
            omega
          · intro x hx y hy hxy
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
            have hmod : x % m = y % m := hS x hx.2 y hy.2
            have hxy' : x / m = y / m := hxy
            calc x = x % m + m * (x / m) := (Nat.mod_add_div x m).symm
              _ = y % m + m * (y / m) := by rw [hmod, hxy']
              _ = y := Nat.mod_add_div y m
      _ = N / m + 1 := Finset.card_range _
  calc m * cnt S N ≤ m * (N / m + 1) := Nat.mul_le_mul_left _ h1
    _ = m * (N / m) + m := by ring
    _ ≤ N + m := by have := Nat.mul_div_le N m; omega

lemma cnt_le_insert {S T : Set ℕ} (h : ∀ x ∈ S, x = 0 ∨ x ∈ T) (N : ℕ) :
    cnt S N ≤ cnt T N + 1 := by
  unfold cnt
  calc ((Finset.range N).filter (· ∈ S)).card
      ≤ (insert 0 ((Finset.range N).filter (· ∈ T))).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter, Finset.mem_range] at hx
        rcases h x hx.2 with h0 | hT
        · rw [h0]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_range.2 hx.1, hT⟩)
    _ ≤ ((Finset.range N).filter (· ∈ T)).card + 1 := Finset.card_insert_le _ _

lemma cnt_diff (A : Set ℕ) (N : ℕ) : cnt A N ≤ cnt (A \ {0}) N + 1 :=
  cnt_le_insert (fun x hx => by
    rcases Nat.eq_zero_or_pos x with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hx, fun hx0 => by rw [Set.mem_singleton_iff] at hx0; omega⟩) N

variable {A : Set ℕ}

lemma pair (hA : IsGood A) {S : Set ℕ} (hSA : S ⊆ A) {a t x y : ℕ} (haA : a ∈ A) (ht : t < a)
    (hx : x ∈ S ∧ a < x ∧ x % a = t) (hy : y ∈ S ∧ a < y ∧ y % a = (a - t) % a) : x = y := by
  have hdvd : a ∣ x + y := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, hx.2.2, hy.2.2]
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0; simp
    · rw [Nat.mod_eq_of_lt (by omega : a - t < a), show t + (a - t) = a by omega, Nat.mod_self]
  exact hA.2 a haA x (hSA hx.1) y (hSA hy.1) hdvd hx.2.1 hy.2.1

lemma pair_card (hA : IsGood A) {S : Set ℕ} (hSA : S ⊆ A) {a t : ℕ} (haA : a ∈ A) (ht : t < a)
    (N : ℕ) (B : ℝ)
    (h1 : (cnt (Sc S a t) N : ℝ) ≤ B) (h2 : (cnt (Sc S a ((a - t) % a)) N : ℝ) ≤ B) :
    (cnt (Sc S a t) N : ℝ) + cnt (Sc S a ((a - t) % a)) N ≤ B + 1 := by
  by_cases hY : cnt (Sc S a ((a - t) % a)) N = 0
  · rw [hY]; push_cast; linarith
  · have hX : cnt (Sc S a t) N ≤ 1 := by
      unfold cnt at hY ⊢
      obtain ⟨y, hy⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hY)
      apply Finset.card_le_one.2
      intro x1 hx1 x2 hx2
      have e1 := pair hA hSA haA ht (Finset.mem_filter.1 hx1).2 (Finset.mem_filter.1 hy).2
      have e2 := pair hA hSA haA ht (Finset.mem_filter.1 hx2).2 (Finset.mem_filter.1 hy).2
      rw [e1, e2]
    have : (cnt (Sc S a t) N : ℝ) ≤ 1 := by exact_mod_cast hX
    linarith

lemma cover {S : Set ℕ} {m a : ℕ} (hS : ∀ x ∈ S, ∀ y ∈ S, x ≡ y [MOD m]) (haS : a ∈ S)
    (ha : 0 < a) (N : ℕ) :
    cnt S N ≤ (a + 1) + ∑ t ∈ Rs m a, cnt (Sc S a t) N := by
  unfold cnt
  calc ((Finset.range N).filter (· ∈ S)).card
      ≤ (Finset.range (a+1) ∪ (Rs m a).biUnion
          (fun t => (Finset.range N).filter (· ∈ Sc S a t))).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        rw [Finset.mem_union]
        by_cases hxa : x ≤ a
        · left; simp only [Finset.mem_range]; omega
        · right
          rw [Finset.mem_biUnion]
          refine ⟨x % a, ?_, ?_⟩
          · simp only [Rs, Finset.mem_filter, Finset.mem_range]
            refine ⟨Nat.mod_lt _ ha, ?_⟩
            have hmod : x % Nat.gcd m a = a % Nat.gcd m a :=
              Nat.ModEq.of_dvd (Nat.gcd_dvd_left m a) (hS x hx.2 a haS)
            have hgx : Nat.gcd m a ∣ x := by
              apply Nat.dvd_of_mod_eq_zero
              rw [hmod]
              exact Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right m a)
            exact (Nat.dvd_mod_iff (Nat.gcd_dvd_right m a)).2 hgx
          · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hx.1, ⟨hx.2, by omega, rfl⟩⟩
    _ ≤ (Finset.range (a+1)).card + ((Rs m a).biUnion
          (fun t => (Finset.range N).filter (· ∈ Sc S a t))).card := Finset.card_union_le _ _
    _ ≤ (a + 1) + ∑ t ∈ Rs m a, ((Finset.range N).filter (· ∈ Sc S a t)).card := by
        rw [Finset.card_range]
        exact Nat.add_le_add_left Finset.card_biUnion_le _

lemma Rcard {m a : ℕ} : (Rs m a).card ≤ a / Nat.gcd m a := by
  have hga : Nat.gcd m a ∣ a := Nat.gcd_dvd_right m a
  calc (Rs m a).card ≤ (Finset.range (a / Nat.gcd m a)).card := by
        apply Finset.card_le_card_of_injOn (fun t => t / Nat.gcd m a)
        · intro t ht
          simp only [Rs, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht ⊢
          exact Nat.div_lt_div_of_lt_of_dvd hga ht.1
        · intro t1 ht1 t2 ht2 h
          simp only [Rs, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht1 ht2
          have h' : t1 / Nat.gcd m a = t2 / Nat.gcd m a := h
          rw [← Nat.div_mul_cancel ht1.2, ← Nat.div_mul_cancel ht2.2, h']
    _ = a / Nat.gcd m a := Finset.card_range _

lemma sigma_mem {m a t : ℕ} (ha : 0 < a) (ht : t ∈ Rs m a) : (a - t) % a ∈ Rs m a := by
  have hga : Nat.gcd m a ∣ a := Nat.gcd_dvd_right m a
  simp only [Rs, Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨Nat.mod_lt _ ha, (Nat.dvd_mod_iff hga).2 (Nat.dvd_sub hga ht.2)⟩

lemma sigma_inv {a t : ℕ} (ht : t < a) : (a - (a - t) % a) % a = t := by
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; simp
  · rw [Nat.mod_eq_of_lt (by omega : a - t < a), show a - (a - t) = t by omega,
      Nat.mod_eq_of_lt ht]

lemma Rs_lt {m a t : ℕ} (ht : t ∈ Rs m a) : t < a := by
  simp only [Rs, Finset.mem_filter, Finset.mem_range] at ht
  exact ht.1

lemma step (hA : IsGood A) {ε q : ℝ} (hε : 0 < ε) (hq : 0 < q) {S : Set ℕ} (hSA : S ⊆ A)
    (h0 : (0:ℕ) ∉ S) {m : ℕ} (hm : 0 < m) (hS : ∀ x ∈ S, ∀ y ∈ S, x ≡ y [MOD m])
    (hf : ∃ᶠ N in atTop, ε * q * N ≤ m * cnt S N) :
    ∃ S' ⊆ A, (0:ℕ) ∉ S' ∧ ∃ m' : ℕ, 0 < m' ∧ (∀ x ∈ S', ∀ y ∈ S', x ≡ y [MOD m']) ∧
      ∃ᶠ N in atTop, ε * (q * (3/2)) * N ≤ m' * cnt S' N := by
  obtain ⟨N₁, hN₁, hN₁'⟩ := (hf.and_eventually (eventually_ge_atTop 1)).exists
  have hpos : 0 < cnt S N₁ := by
    rcases Nat.eq_zero_or_pos (cnt S N₁) with h | h
    · exfalso
      rw [h] at hN₁
      have : (1:ℝ) ≤ N₁ := by exact_mod_cast hN₁'
      have : 0 < ε * q * N₁ := by positivity
      push_cast at hN₁
      linarith
    · exact h
  have hpos' : 0 < ((Finset.range N₁).filter (· ∈ S)).card := hpos
  obtain ⟨a, haf⟩ := Finset.card_pos.1 hpos'
  have haS : a ∈ S := (Finset.mem_filter.1 haf).2
  have ha : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ haS))
  have haA : a ∈ A := hSA haS
  have hg : 0 < Nat.gcd m a := Nat.gcd_pos_of_pos_right m ha
  have hga : Nat.gcd m a ∣ a := Nat.gcd_dvd_right m a
  obtain ⟨K, hKdef⟩ : ∃ K, K = a / Nat.gcd m a := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKdef]; exact Nat.div_pos (Nat.le_of_dvd ha hga) hg
  have hL : 0 < m * K := Nat.mul_pos hm hK
  have hlcm : Nat.lcm m a = m * K := by
    rw [hKdef, ← Nat.mul_div_assoc m hga]; rfl
  have hmodL : ∀ t, ∀ x ∈ Sc S a t, ∀ y ∈ Sc S a t, x ≡ y [MOD m * K] := by
    intro t x hx y hy
    have hx' : x ∈ S ∧ a < x ∧ x % a = t := hx
    have hy' : y ∈ S ∧ a < y ∧ y % a = t := hy
    have h1 : x ≡ y [MOD m] := hS x hx'.1 y hy'.1
    have h2 : x ≡ y [MOD a] := hx'.2.2.trans hy'.2.2.symm
    rw [← hlcm]
    rcases le_total x y with hxy | hxy
    · exact (Nat.modEq_iff_dvd' hxy).2
        (Nat.lcm_dvd ((Nat.modEq_iff_dvd' hxy).1 h1) ((Nat.modEq_iff_dvd' hxy).1 h2))
    · exact ((Nat.modEq_iff_dvd' hxy).2
        (Nat.lcm_dvd ((Nat.modEq_iff_dvd' hxy).1 h1.symm) ((Nat.modEq_iff_dvd' hxy).1 h2.symm))).symm
  by_contra hcon
  have hev : ∀ t ∈ Rs m a, ∀ᶠ N in atTop,
      ¬ (ε * (q * (3/2)) * N ≤ ((m * K : ℕ) : ℝ) * cnt (Sc S a t) N) := by
    intro t _
    refine Filter.not_frequently.1 (fun hfr => hcon ⟨Sc S a t, fun x hx => hSA hx.1,
      fun h => h0 h.1, m * K, hL, hmodL t, hfr⟩)
  have hall := (Filter.eventually_all_finset (Rs m a)).2 hev
  have hbig : ∀ᶠ N : ℕ in atTop, 4 * ((m:ℝ) * (a + 1) + m * K) / (ε * q) < N :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  obtain ⟨N, hN, hallN, hbigN⟩ := (hf.and_eventually (hall.and hbig)).exists
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ε * (q * (3/2)) * N / ((m:ℝ) * K) := ⟨_, rfl⟩
  have hmK : (0:ℝ) < (m:ℝ) * K := by
    have : (0:ℝ) < ((m * K : ℕ) : ℝ) := by exact_mod_cast hL
    push_cast at this; exact this
  have hmB : (m:ℝ) * K * B = ε * (q * (3/2)) * N := by
    rw [hBdef]; field_simp
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hB : ∀ t ∈ Rs m a, (cnt (Sc S a t) N : ℝ) ≤ B := by
    intro t ht
    have h := hallN t ht
    rw [not_le] at h
    push_cast at h
    rw [hBdef, le_div_iff₀ hmK]
    linarith
  have hpair : ∀ t ∈ Rs m a,
      (cnt (Sc S a t) N : ℝ) + cnt (Sc S a ((a - t) % a)) N ≤ B + 1 := fun t ht =>
    pair_card hA hSA haA (Rs_lt ht) N B (hB t ht) (hB _ (sigma_mem ha ht))
  have hsum := Finset.sum_le_sum hpair
  rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib] at hsum
  have hre : ∑ t ∈ Rs m a, (cnt (Sc S a ((a - t) % a)) N : ℝ) =
      ∑ t ∈ Rs m a, (cnt (Sc S a t) N : ℝ) := by
    apply Finset.sum_nbij' (fun t => (a - t) % a) (fun t => (a - t) % a)
    · intro t ht; exact sigma_mem ha ht
    · intro t ht; exact sigma_mem ha ht
    · intro t ht; exact sigma_inv (Rs_lt ht)
    · intro t ht; exact sigma_inv (Rs_lt ht)
    · intro t _; rfl
  rw [hre] at hsum
  have hRc : ((Rs m a).card : ℝ) ≤ K := by rw [hKdef]; exact_mod_cast Rcard
  have hcov : (cnt S N : ℝ) ≤ (a + 1 : ℝ) + ∑ t ∈ Rs m a, (cnt (Sc S a t) N : ℝ) := by
    exact_mod_cast cover hS haS ha N
  set T := ∑ t ∈ Rs m a, (cnt (Sc S a t) N : ℝ) with hT
  have h2T : 2 * T ≤ K * (B + 1) := by
    have := mul_le_mul_of_nonneg_right hRc (by linarith : (0:ℝ) ≤ B + 1)
    linarith
  have i1 : (m:ℝ) * (2 * T) ≤ m * (K * (B + 1)) :=
    mul_le_mul_of_nonneg_left h2T (Nat.cast_nonneg _)
  have i2 : (m:ℝ) * cnt S N ≤ m * ((a + 1) + T) :=
    mul_le_mul_of_nonneg_left hcov (Nat.cast_nonneg _)
  have i3 : 4 * ((m:ℝ) * (a + 1) + m * K) < N * (ε * q) :=
    (div_lt_iff₀ (by positivity)).1 hbigN
  nlinarith

lemma iter (hA : IsGood A) {ε : ℝ} (hε : 0 < ε)
    (h0 : ∃ᶠ N in atTop, ε * N ≤ cnt (A \ {0}) N) (k : ℕ) :
    ∃ S ⊆ A, (0:ℕ) ∉ S ∧ ∃ m : ℕ, 0 < m ∧ (∀ x ∈ S, ∀ y ∈ S, x ≡ y [MOD m]) ∧
      ∃ᶠ N in atTop, ε * (3/2) ^ k * N ≤ m * cnt S N := by
  induction k with
  | zero =>
    exact ⟨A \ {0}, Set.sdiff_subset, by simp, 1, one_pos, fun x _ y _ => Nat.modEq_one,
      by simpa using h0⟩
  | succ k ih =>
    obtain ⟨S, hSA, hS0, m, hm, hS, hf⟩ := ih
    obtain ⟨S', h1, h2, m', h3, h4, h5⟩ := step hA hε (by positivity) hSA hS0 hm hS hf
    refine ⟨S', h1, h2, m', h3, h4, ?_⟩
    rw [pow_succ]; exact h5

lemma ncard_Iio' (N : ℕ) : (Set.Iio N).ncard = N := by
  rw [show Set.Iio N = ((Finset.range N : Finset ℕ) : Set ℕ) by ext; simp,
    Set.ncard_coe_finset, Finset.card_range]

lemma ncard_cnt (S : Set ℕ) (N : ℕ) : (S ∩ Set.Iio N).ncard = cnt S N := by
  rw [show S ∩ Set.Iio N = (((Finset.range N).filter (· ∈ S) : Finset ℕ) : Set ℕ) by
    ext x; simp [and_comm], Set.ncard_coe_finset]
  rfl

end DZ

open DZ in
/--
Erdős and Sárközy proved that such an $A$ must have density 0.
-/
theorem erdos_12.variants.erdos_sarkozy_density_0 (A : Set ℕ) (hA : IsGood A) :
    A.HasDensity 0 := by
  have key : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, (cnt A N : ℝ) ≤ ε * N := by
    intro ε hε
    by_contra hne
    have hfr : ∃ᶠ N : ℕ in atTop, ε * N < cnt A N := by
      rw [Filter.not_eventually] at hne
      exact hne.mono fun N h => lt_of_not_ge h
    have hb : ∃ᶠ N : ℕ in atTop, (ε / 2) * N ≤ cnt (A \ {0}) N := by
      have hev : ∀ᶠ N : ℕ in atTop, (2 / ε : ℝ) < N :=
        tendsto_natCast_atTop_atTop.eventually_gt_atTop _
      refine (hfr.and_eventually hev).mono fun N ⟨h1, h2⟩ => ?_
      have h3 : (cnt A N : ℝ) ≤ cnt (A \ {0}) N + 1 := by exact_mod_cast cnt_diff A N
      have h4 : 2 < (N : ℝ) * ε := (div_lt_iff₀ hε).1 h2
      linarith
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 / ε) (by norm_num : (1:ℝ) < 3 / 2)
    obtain ⟨S, _, _, m, hm, hS, hf⟩ := iter hA (half_pos hε) hb k
    have hev : ∀ᶠ N : ℕ in atTop, (m : ℝ) < N :=
      tendsto_natCast_atTop_atTop.eventually_gt_atTop _
    obtain ⟨N, h1, h2⟩ := (hf.and_eventually hev).exists
    have h3 : ((m * cnt S N : ℕ) : ℝ) ≤ ((N + m : ℕ) : ℝ) := by exact_mod_cast cap hm hS N
    push_cast at h3
    have h4 : 2 ≤ ε / 2 * (3 / 2) ^ k := by
      have := (div_lt_iff₀ hε).1 hk
      linarith
    have h5 : 2 * (N : ℝ) ≤ ε / 2 * (3 / 2) ^ k * N :=
      mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _)
    linarith
  have hT : Tendsto (fun N : ℕ => (cnt A N : ℝ) / N) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun b hb => Eventually.of_forall fun N =>
      lt_of_lt_of_le hb (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), fun b hb => ?_⟩
    refine ((key (b / 2) (half_pos hb)).and (eventually_gt_atTop 0)).mono fun N ⟨hN, hN0⟩ => ?_
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [div_lt_iff₀ hN']
    have := mul_pos hb hN'
    linarith
  have hpd : (fun b : ℕ => A.partialDensity Set.univ b) = fun N => (cnt A N : ℝ) / N := by
    funext N
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
    rw [ncard_cnt, ncard_Iio']
  show Tendsto (fun b : ℕ => A.partialDensity Set.univ b) atTop (𝓝 0)
  rw [hpd]
  exact hT

end Erdos12

#print axioms Erdos12.erdos_12.variants.erdos_sarkozy_density_0
