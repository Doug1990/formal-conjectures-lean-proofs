import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter

namespace Erdos1186

def monoCount (k n : ℕ) (c : ℕ → Bool) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ =>
    p.1 + (k - 1) * p.2 ≤ n ∧ ∀ i < k, c (p.1 + i * p.2) = c p.1).card

noncomputable def minMonoCount (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ c : ℕ → Bool, monoCount k n c = m}

noncomputable def δ (k : ℕ) : ℝ :=
  atTop.liminf (fun n : ℕ ↦ (minMonoCount k n : ℝ) / (n : ℝ) ^ 2)

theorem minMonoCount_le (k n : ℕ) (c : ℕ → Bool) : minMonoCount k n ≤ monoCount k n c :=
  Nat.sInf_le ⟨c, rfl⟩

namespace P

/-- The set of progressions. -/
def A (j n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p => p.1 + j * p.2 ≤ n

lemma A_count (j : ℕ) (hj : 1 ≤ j) : ∀ n, 2 * j * (A j n).card ≤ n ^ 2 := by
  intro n
  induction n with
  | zero => simp [A]
  | succ n ih =>
    have hsub : A j (n + 1) ⊆ A j n ∪
        ((Finset.Icc 1 n).filter (fun d => j * d ≤ n)).image (fun d => (n + 1 - j * d, d)) := by
      intro p hp
      simp only [A, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      rcases p with ⟨a, d⟩
      simp only at hp
      by_cases h : a + j * d ≤ n
      · apply Finset.mem_union_left
        simp only [A, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        refine ⟨⟨⟨hp.1.1.1, ?_⟩, hp.1.2.1, ?_⟩, h⟩
        · nlinarith
        · nlinarith
      · apply Finset.mem_union_right
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨d, ⟨⟨hp.1.2.1, ?_⟩, ?_⟩, ?_⟩
        · nlinarith
        · omega
        · ext <;> (simp; try omega)
    have hfil : (Finset.Icc 1 n).filter (fun d => j * d ≤ n) ⊆ Finset.Icc 1 (n / j) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      simp only [Finset.mem_Icc]
      exact ⟨hd.1.1, (Nat.le_div_iff_mul_le hj).mpr (by rw [mul_comm]; exact hd.2)⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (A j n)
      (((Finset.Icc 1 n).filter (fun d => j * d ≤ n)).image (fun d => (n + 1 - j * d, d)))
    have h3 := Finset.card_image_le (s := (Finset.Icc 1 n).filter (fun d => j * d ≤ n))
      (f := fun d => (n + 1 - j * d, d))
    have h4 := Finset.card_le_card hfil
    rw [Nat.card_Icc] at h4
    have h5 : j * (n / j) ≤ n := Nat.mul_div_le n j
    have h6 : j * ((Finset.Icc 1 n).filter (fun d => j * d ≤ n)).card ≤ n :=
      le_trans (Nat.mul_le_mul_left j (by simpa using h4)) h5
    have : 2 * j * (A j (n+1)).card ≤ 2 * j * (A j n).card + 2 * (j *
        ((Finset.Icc 1 n).filter (fun d => j * d ≤ n)).card) := by
      have := Nat.mul_le_mul_left (2 * j) (le_trans h1 (le_trans h2 (Nat.add_le_add_left h3 _)))
      linarith [this]
    nlinarith

/-- The progression as a set. -/
def Pr (k a d : ℕ) : Finset ℕ := (Finset.range k).image fun i => a + i * d

lemma card_Pr (k a d : ℕ) (hd : 1 ≤ d) : (Pr k a d).card = k := by
  rw [Pr, Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro i i' h
  simp only at h
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (Nat.add_left_cancel h)

lemma Pr_sub (k n a d : ℕ) (hk : 1 ≤ k) (ha : 1 ≤ a) (h : a + (k - 1) * d ≤ n) :
    Pr k a d ⊆ Finset.Icc 1 n := by
  intro x hx
  simp only [Pr, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  simp only [Finset.mem_Icc]
  have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
  omega

lemma mono_iff (k a d : ℕ) (hk : 1 ≤ k) (S : Finset ℕ) :
    (∀ i < k, decide (a + i * d ∈ S) = decide (a ∈ S)) ↔ (Pr k a d ⊆ S ∨ Disjoint (Pr k a d) S) := by
  constructor
  · intro h
    by_cases ha : a ∈ S
    · left
      intro x hx
      simp only [Pr, Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have := h i hi
      simpa [ha] using this
    · right
      rw [Finset.disjoint_left]
      intro x hx
      simp only [Pr, Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have := h i hi
      simpa [ha] using this
  · have h0 : a ∈ Pr k a d := by
      simp only [Pr, Finset.mem_image, Finset.mem_range]
      exact ⟨0, by omega, by simp⟩
    rintro (h | h) i hi
    · have hi' : a + i * d ∈ Pr k a d := by
        simp only [Pr, Finset.mem_image, Finset.mem_range]
        exact ⟨i, hi, rfl⟩
      simp [h hi', h h0]
    · have hi' : a + i * d ∈ Pr k a d := by
        simp only [Pr, Finset.mem_image, Finset.mem_range]
        exact ⟨i, hi, rfl⟩
      have e1 : a + i * d ∉ S := Finset.disjoint_left.mp h hi'
      have e2 : a ∉ S := Finset.disjoint_left.mp h h0
      simp [e1, e2]

/-- Number of subsets of U on which a given progression is monochromatic. -/
lemma count_S (k n a d : ℕ) (hk : 1 ≤ k) (ha : 1 ≤ a) (hd : 1 ≤ d)
    (h : a + (k - 1) * d ≤ n) :
    ((Finset.Icc 1 n).powerset.filter
      (fun S => ∀ i < k, decide (a + i * d ∈ S) = decide (a ∈ S))).card * 2 ^ (k - 1) ≤ 2 ^ n := by
  set U := Finset.Icc 1 n
  set Q := Pr k a d
  have hQU : Q ⊆ U := Pr_sub k n a d hk ha h
  have hcU : U.card = n := by simp [U]
  have hcQ : Q.card = k := card_Pr k a d hd
  have hcard : (U \ Q).card = n - k := by
    rw [Finset.card_sdiff_of_subset hQU, hcU, hcQ]
  have hsub : U.powerset.filter (fun S => ∀ i < k, decide (a + i * d ∈ S) = decide (a ∈ S)) ⊆
      (U \ Q).powerset.image (fun T => T ∪ Q) ∪ (U \ Q).powerset := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset, mono_iff k a d hk] at hS
    rcases hS with ⟨hSU, h1 | h1⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_image]
      refine ⟨S \ Q, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        exact Finset.sdiff_subset_sdiff hSU le_rfl
      · exact Finset.sdiff_union_of_subset h1
    · apply Finset.mem_union_right
      rw [Finset.mem_powerset, Finset.subset_sdiff]
      exact ⟨hSU, h1.symm⟩
  have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hc2 := Finset.card_image_le (s := (U \ Q).powerset) (f := fun T => T ∪ Q)
  rw [Finset.card_powerset, hcard] at hc hc2
  have hnk : k ≤ n := by
    have : 1 * d ≤ (k - 1) * d + d := by omega
    have : (k - 1) * d + 0 ≤ (k - 1) * d := le_refl _
    by_contra hh
    have : k - 1 ≥ n := by omega
    have : (k - 1) * d ≥ n * 1 := Nat.mul_le_mul this hd
    omega
  have e : 2 ^ (n - k) * 2 * 2 ^ (k - 1) = 2 ^ n := by
    rw [mul_assoc, ← pow_succ', ← pow_add]
    congr 1
    omega
  calc _ ≤ (2 ^ (n - k) + 2 ^ (n - k)) * 2 ^ (k - 1) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ n := by rw [← e]; ring

lemma min_bound (k n : ℕ) (hk : 1 ≤ k) :
    minMonoCount k n * 2 ^ (k - 1) ≤ (A (k - 1) n).card := by
  set U := Finset.Icc 1 n
  let c : Finset ℕ → ℕ → Bool := fun S x => decide (x ∈ S)
  have hmc : ∀ S, monoCount k n (c S) = ((A (k - 1) n).filter
      (fun p => ∀ i < k, decide (p.1 + i * p.2 ∈ S) = decide (p.1 ∈ S))).card := by
    intro S
    rw [monoCount, A, Finset.filter_filter]
  have hsum : ∑ S ∈ U.powerset, monoCount k n (c S) * 2 ^ (k - 1) ≤
      ∑ S ∈ U.powerset, (A (k - 1) n).card := by
    simp only [hmc, Finset.card_filter, Finset.sum_mul, Finset.sum_comm (s := U.powerset)]
    simp only [Finset.sum_const, smul_eq_mul]
    calc _ ≤ ∑ p ∈ A (k - 1) n, 2 ^ n := by
          apply Finset.sum_le_sum
          intro p hp
          simp only [A, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
          have := count_S k n p.1 p.2 hk hp.1.1.1 hp.1.2.1 hp.2
          rw [Finset.card_filter, Finset.sum_mul] at this
          exact this
      _ = _ := by simp [U, mul_comm]
  have hlow : ∑ S ∈ U.powerset, minMonoCount k n * 2 ^ (k - 1) ≤
      ∑ S ∈ U.powerset, monoCount k n (c S) * 2 ^ (k - 1) :=
    Finset.sum_le_sum fun S _ => Nat.mul_le_mul_right _ (minMonoCount_le k n (c S))
  have := le_trans hlow hsum
  simp only [Finset.sum_const, smul_eq_mul] at this
  exact Nat.le_of_mul_le_mul_left this (by simp)

end P

theorem erdos_1186.variants.probabilistic (k : ℕ) (hk : 2 ≤ k) :
    δ k ≤ 1 / (((k : ℝ) - 1) * 2 ^ k) := by
  have key : ∀ n : ℕ, 1 ≤ n → (minMonoCount k n : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (((k : ℝ) - 1) * 2 ^ k) := by
    intro n hn
    have h1 := P.min_bound k n (by omega)
    have h2 := P.A_count (k - 1) (by omega) n
    have h3 : minMonoCount k n * 2 ^ k * (k - 1) ≤ n ^ 2 := by
      have e : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      rw [e]
      calc minMonoCount k n * (2 ^ (k - 1) * 2) * (k - 1)
          = 2 * (k - 1) * (minMonoCount k n * 2 ^ (k - 1)) := by ring
        _ ≤ 2 * (k - 1) * (P.A (k - 1) n).card := Nat.mul_le_mul_left _ h1
        _ ≤ n ^ 2 := h2
    have h4 : ((minMonoCount k n : ℝ) * 2 ^ k * ((k : ℝ) - 1)) ≤ (n : ℝ) ^ 2 := by
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [← this]
      exact_mod_cast h3
    have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff₀ hn' (by positivity)]
    nlinarith
  refine Filter.liminf_le_of_frequently_le ?_ ?_
  · rw [Filter.frequently_atTop]
    intro a
    exact ⟨a + 1, by omega, key (a + 1) (by omega)⟩
  · exact Filter.isBoundedUnder_of ⟨0, fun x => div_nonneg (Nat.cast_nonneg _) (by positivity)⟩

end Erdos1186

#print axioms Erdos1186.erdos_1186.variants.probabilistic
