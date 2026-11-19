import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Algebra.IsPrimePow

namespace Erdos292

def A : Set ℕ :=
  {n | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ n ∈ S ∧ ∑ m ∈ S, (1 : ℚ) / m = 1}

lemma one_div_mul_cast (a b : ℕ) : (1 : ℚ) / ((a * b : ℕ) : ℚ) = (1 / a) * (1 / b) := by
  rw [Nat.cast_mul, one_div_mul_one_div]

lemma sum_image_mul (a : ℕ) (ha : 0 < a) (T : Finset ℕ) :
    ∑ x ∈ T.image (a * ·), (1 : ℚ) / x = (1 / a) * ∑ t ∈ T, (1 : ℚ) / t := by
  rw [Finset.sum_image (f := fun x : ℕ => (1 : ℚ) / x)
    (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left ha h), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun t _ => one_div_mul_cast a t)

theorem erdos_292.variants.mul : ∀ m ∈ A, ∀ n ∈ A, m * n ∈ A := by
  rintro m ⟨S, hS, hmS, hsum⟩ n ⟨T, hT, hnT, htsum⟩
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hS hmS)).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (hT hnT)).1
  have hdisj : Disjoint (S.erase m) (T.image (m * ·)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx'
    have h1 := Finset.mem_erase.mp hx
    have h2 := (Finset.mem_Icc.mp (hS h1.2)).2
    have h3 := (Finset.mem_Icc.mp (hT ht)).1
    have : m ≤ m * t := Nat.le_mul_of_pos_right m h3
    exact h1.1 (by omega)
  refine ⟨S.erase m ∪ T.image (m * ·), ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have h := Finset.mem_Icc.mp (hS (Finset.mem_erase.mp hx).2)
      have : m ≤ m * n := Nat.le_mul_of_pos_right m hn1
      exact Finset.mem_Icc.mpr ⟨h.1, by omega⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      have h := Finset.mem_Icc.mp (hT ht)
      refine Finset.mem_Icc.mpr ⟨Nat.mul_pos hm1 h.1, Nat.mul_le_mul_left m h.2⟩
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hnT, rfl⟩)
  · rw [Finset.sum_union hdisj, sum_image_mul m hm1 T, htsum]
    have := Finset.sum_erase_add S (fun x : ℕ => (1 : ℚ) / x) hmS
    rw [hsum] at this
    linarith

theorem erdos_292.variants.two_mul : ∀ n ∈ A, 1 < n → 2 * n ∈ A := by
  rintro n ⟨S, hS, hnS, hsum⟩ hn
  have h1S : 1 ∉ S := by
    intro h1
    have e := Finset.add_sum_erase S (fun x : ℕ => (1 : ℚ) / x) h1
    have hpos : (1 : ℚ) / n ≤ ∑ x ∈ S.erase 1, (1 : ℚ) / x :=
      Finset.single_le_sum (f := fun x : ℕ => (1 : ℚ) / x)
        (fun i _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
        (Finset.mem_erase.mpr ⟨by omega, hnS⟩)
    have : (0 : ℚ) < 1 / n := by
      have : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
      exact one_div_pos.mpr this
    rw [hsum] at e
    simp only [Nat.cast_one, div_one] at e
    linarith
  have h2 : 2 ∉ S.image (2 * ·) := by
    intro h
    obtain ⟨x, hx, hx2⟩ := Finset.mem_image.mp h
    have hx2' : 2 * x = 2 := hx2
    have : x = 1 := by omega
    exact h1S (this ▸ hx)
  refine ⟨insert 2 (S.image (2 * ·)), ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      have h := Finset.mem_Icc.mp (hS ht)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, hnS, rfl⟩)
  · rw [Finset.sum_insert h2, sum_image_mul 2 (by norm_num) S, hsum]
    norm_num

lemma norm_inv_nat (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : a ≠ 0) :
    padicNorm p ((1 : ℚ) / a) = (p : ℚ) ^ (padicValNat p a) := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  rw [padicNorm.div, padicNorm.one, padicNorm.eq_zpow_of_nonzero ha', padicValRat.of_nat,
    zpow_neg, zpow_natCast, one_div, inv_inv]

theorem erdos_292.variants.prime_pow : ∀ n ∈ A, ¬ IsPrimePow n := by
  rintro n ⟨S, hS, hnS, hsum⟩ hpp
  obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff n |>.mp hpp
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have e := Finset.add_sum_erase S (fun x : ℕ => (1 : ℚ) / x) hnS
  rw [hsum] at e
  have e' : (1 : ℚ) / ((p ^ k : ℕ) : ℚ) = 1 - ∑ x ∈ S.erase (p ^ k), (1 : ℚ) / x := by
    linarith
  have hpk : (1 : ℚ) ≤ (p : ℚ) ^ (k - 1) := one_le_pow₀ hp1.le
  have hbound : padicNorm p (∑ x ∈ S.erase (p ^ k), (1 : ℚ) / x) ≤ (p : ℚ) ^ (k - 1) := by
    refine padicNorm.sum_le' (fun a ha => ?_) (by linarith)
    obtain ⟨hne, haS⟩ := Finset.mem_erase.mp ha
    have hI := Finset.mem_Icc.mp (hS haS)
    rw [norm_inv_nat p a (by omega)]
    refine pow_le_pow_right₀ hp1.le ?_
    have hdvd : p ^ padicValNat p a ∣ a := pow_padicValNat_dvd
    have hle : p ^ padicValNat p a ≤ a := Nat.le_of_dvd (by omega) hdvd
    have hlt : p ^ padicValNat p a < p ^ k := lt_of_le_of_lt hle (by omega)
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    omega
  have hleft : padicNorm p ((1 : ℚ) / ((p ^ k : ℕ) : ℚ)) = (p : ℚ) ^ k := by
    rw [norm_inv_nat p (p ^ k) (pow_ne_zero _ hp.ne_zero), padicValNat.prime_pow]
  have hmax := padicNorm.sub (p := p) (q := 1) (r := ∑ x ∈ S.erase (p ^ k), (1 : ℚ) / x)
  rw [← e', hleft, padicNorm.one] at hmax
  have h2 : (p : ℚ) ^ k ≤ (p : ℚ) ^ (k - 1) := le_trans hmax (max_le hpk hbound)
  have h3 : (p : ℚ) ^ (k - 1) < (p : ℚ) ^ k := pow_lt_pow_right₀ hp1 (by omega)
  linarith

end Erdos292

#print axioms Erdos292.erdos_292.variants.mul
#print axioms Erdos292.erdos_292.variants.two_mul
#print axioms Erdos292.erdos_292.variants.prime_pow
