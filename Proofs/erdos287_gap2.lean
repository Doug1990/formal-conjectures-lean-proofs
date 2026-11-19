import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Common

namespace Erdos287

def max_gap (k : ℕ) (s : Fin k → ℕ ) : ℕ  :=
   Finset.sup Finset.univ (fun i : Fin (k - 1) =>
      s  ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

/-- Between two distinct multiples of `2^v` lies a multiple of `2^(v+1)`. -/
lemma between {v x y : ℕ} (hxy : x < y) (hx : 2 ^ v ∣ x) (hy : 2 ^ v ∣ y) :
    ∃ z, x ≤ z ∧ z ≤ y ∧ 2 ^ (v + 1) ∣ z := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := hy
  have hcd : c < d := Nat.lt_of_mul_lt_mul_left hxy
  rcases Nat.even_or_odd c with ⟨e, he⟩ | ⟨e, he⟩
  · refine ⟨2 ^ v * c, le_rfl, Nat.mul_le_mul_left _ hcd.le, ?_⟩
    rw [pow_succ, he]
    exact ⟨e, by ring⟩
  · refine ⟨2 ^ v * (c + 1), Nat.mul_le_mul_left _ (by omega),
      Nat.mul_le_mul_left _ (by omega), ?_⟩
    rw [pow_succ, he]
    exact ⟨e + 1, by ring⟩

/-- A finite nonempty sum of positive rationals, each of 2-adic valuation `> m`,
has 2-adic valuation `> m`. -/
lemma val_sum (m : ℤ) (f : ℕ → ℚ) (T : Finset ℕ) (hT : T.Nonempty)
    (hpos : ∀ j ∈ T, 0 < f j) (hv : ∀ j ∈ T, m < padicValRat 2 (f j)) :
    m < padicValRat 2 (∑ j ∈ T, f j) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hv a (by simp)
  | cons a s ha hs ih =>
    rw [Finset.sum_cons]
    have h1 : 0 < ∑ j ∈ s, f j := Finset.sum_pos (fun j hj => hpos j (by simp [hj])) hs
    have h0 : 0 < f a := hpos a (by simp)
    have h2 := padicValRat.min_le_padicValRat_add (p := 2) (q := f a) (r := ∑ j ∈ s, f j)
      (by linarith)
    have h3 := ih (fun j hj => hpos j (by simp [hj])) (fun j hj => hv j (by simp [hj]))
    have h4 := hv a (by simp)
    exact lt_of_lt_of_le (lt_min h4 h3) h2

/-- Kürschák: a sum of reciprocals of `k ≥ 2` consecutive positive integers is not `1`. -/
lemma core (a k : ℕ) (ha : 1 ≤ a) (hk : 2 ≤ k) :
    ∑ j ∈ Finset.range k, (1 : ℚ) / ((a + j : ℕ) : ℚ) ≠ 1 := by
  intro hsum
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image (Finset.range k)
    (fun j => padicValNat 2 (a + j)) (Finset.nonempty_range_iff.2 (by omega))
  have hlt : ∀ j ∈ Finset.range k, j ≠ j0 →
      padicValNat 2 (a + j) < padicValNat 2 (a + j0) := by
    intro j hj hne
    by_contra hcon
    rw [not_lt] at hcon
    have hdj : 2 ^ padicValNat 2 (a + j0) ∣ a + j := (padicValNat_dvd_iff_le (by omega)).2 hcon
    have hdj0 : 2 ^ padicValNat 2 (a + j0) ∣ a + j0 := pow_padicValNat_dvd
    have key : ∀ x y, x < y → x ∈ Finset.range k → y ∈ Finset.range k →
        2 ^ padicValNat 2 (a + j0) ∣ a + x → 2 ^ padicValNat 2 (a + j0) ∣ a + y → False := by
      intro x y hxy hx hy hdx hdy
      obtain ⟨z, h1, h2, h3⟩ := between (show a + x < a + y by omega) hdx hdy
      have hzr : z - a ∈ Finset.range k := by
        simp only [Finset.mem_range] at hx hy ⊢
        omega
      have h4 := hmax (z - a) hzr
      have hz : a + (z - a) = z := by omega
      simp only [hz] at h4
      have h5 : padicValNat 2 (a + j0) + 1 ≤ padicValNat 2 z :=
        (padicValNat_dvd_iff_le (by omega)).1 h3
      omega
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key j j0 h hj hj0 hdj hdj0
    · exact key j0 j h hj0 hj hdj0 hdj
  have hv1 : 1 ≤ padicValNat 2 (a + j0) := by
    have he := hmax (a % 2) (by simp only [Finset.mem_range]; omega)
    have : 1 ≤ padicValNat 2 (a + a % 2) :=
      one_le_padicValNat_of_dvd (by omega) (by omega)
    omega
  have hval : ∀ j, padicValRat 2 ((1 : ℚ) / ((a + j : ℕ) : ℚ)) =
      -(padicValNat 2 (a + j) : ℤ) := by
    intro j
    rw [one_div, padicValRat.inv, padicValRat.of_nat]
  have hpos : ∀ j, (0 : ℚ) < 1 / ((a + j : ℕ) : ℚ) := by
    intro j
    apply div_pos one_pos
    exact_mod_cast (show 0 < a + j by omega)
  rw [← Finset.add_sum_erase _ _ hj0] at hsum
  have hne : ((Finset.range k).erase j0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hj0, Finset.card_range]
    omega
  have hR := val_sum (-(padicValNat 2 (a + j0) : ℤ)) (fun j => (1 : ℚ) / ((a + j : ℕ) : ℚ)) _
    hne (fun j _ => hpos j)
    (fun j hj => by
      rw [hval]
      have := hlt j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
      omega)
  have hadd := padicValRat.add_eq_of_lt (p := 2) (by rw [hsum]; exact one_ne_zero)
    (hpos j0).ne' (Finset.sum_pos (fun j _ => hpos j) hne).ne' (by rw [hval]; exact hR)
  rw [hsum, padicValRat.one, hval] at hadd
  omega

theorem erdos_287.variants.gap_at_least_two :
    ∀ (k : ℕ) (_ : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s → 1 < s ⟨0, by omega⟩ →
    ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
    2 ≤ max_gap k s := by
  intro k hk s hs h1 hsum
  by_contra hcon
  rw [not_le] at hcon
  have hstep : ∀ j (hj : j + 1 < k), s ⟨j + 1, hj⟩ = s ⟨j, by omega⟩ + 1 := by
    intro j hj
    have hle : s ⟨j + 1, hj⟩ - s ⟨j, by omega⟩ ≤ max_gap k s := by
      unfold max_gap
      exact Finset.le_sup (f := fun i : Fin (k - 1) => s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)
        (Finset.mem_univ ⟨j, by omega⟩)
    have hlt : s ⟨j, by omega⟩ < s ⟨j + 1, hj⟩ :=
      hs (show (⟨j, by omega⟩ : Fin k) < ⟨j + 1, hj⟩ from Fin.mk_lt_mk.2 (by omega))
    omega
  have hform : ∀ j (hj : j < k), s ⟨j, hj⟩ = s ⟨0, by omega⟩ + j := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      rw [hstep j hj, ih (by omega)]
      omega
  have hsum' : ∑ i : Fin k, (1 : ℝ) / ((s ⟨0, by omega⟩ + (i : ℕ) : ℕ) : ℝ) = 1 := by
    refine Eq.trans ?_ hsum
    apply Finset.sum_congr rfl
    intro i _
    have := hform i i.isLt
    simp only [Fin.eta] at this
    rw [this]
  have h2 : ∑ j ∈ Finset.range k, (1 : ℝ) / ((s ⟨0, by omega⟩ + j : ℕ) : ℝ) = 1 :=
    (Fin.sum_univ_eq_sum_range (fun j => (1 : ℝ) / ((s ⟨0, by omega⟩ + j : ℕ) : ℝ)) k).symm.trans
      hsum'
  have h3 : ((∑ j ∈ Finset.range k, (1 : ℚ) / ((s ⟨0, by omega⟩ + j : ℕ) : ℚ) : ℚ) : ℝ) =
      ((1 : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    exact h2
  exact core _ k (by omega) hk (Rat.cast_injective h3)

end Erdos287

#print axioms Erdos287.erdos_287.variants.gap_at_least_two
