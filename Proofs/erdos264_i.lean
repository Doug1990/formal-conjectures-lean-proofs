import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace Erdos264

def IsIrrationalitySequence (a : ℕ → ℕ) : Prop := ∀ b : ℕ → ℤ,
  BddAbove (Set.range b) → BddBelow (Set.range b) →
  0 ∉ Set.range (fun n ↦ (a n : ℤ) + b n) → 0 ∉ Set.range b →
  Irrational (∑' n, (1 : ℝ) / ((a n : ℤ) + b n))

namespace Greedy

variable (f : ℕ → ℕ → ℝ) (K : ℕ)

/-- tail of the low choices -/
noncomputable def Tlo (n : ℕ) : ℝ := ∑' m, f (m + n) K
/-- tail of the high choices -/
noncomputable def Thi (n : ℕ) : ℝ := ∑' m, f (m + n) 0

open Classical in
noncomputable def ch (n : ℕ) (x : ℝ) : ℕ :=
  if h : ∃ j, f n j + Tlo f K (n + 1) ≤ x then Nat.find h else 0

noncomputable def R (t : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => R t n - f n (ch f K n (R t n))

variable {f K}

lemma tail_split {g : ℕ → ℝ} (hg : Summable g) (n : ℕ) :
    ∑' m, g (m + n) = g n + ∑' m, g (m + (n + 1)) := by
  have hs : Summable (fun m => g (m + n)) := (summable_nat_add_iff n).2 hg
  rw [hs.tsum_eq_zero_add]
  congr 1
  · simp
  · exact tsum_congr (fun m => by congr 1; omega)

section
variable (h0 : ∀ n j, 0 ≤ f n j) (hmono : ∀ n j, f n (j + 1) ≤ f n j)
  (hsum : Summable (fun n => f n 0))
  (hgap : ∀ n j, j < K → f n j - f n (j + 1) ≤ f (n + 1) 0 - f (n + 1) K)
include h0 hmono hsum

omit h0 hsum in
lemma le_zero' (n j : ℕ) : f n j ≤ f n 0 := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact (hmono n j).trans ih

omit h0 hsum in
lemma lo_le (n j : ℕ) (hj : j ≤ K) : f n K ≤ f n j := by
  induction K, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (hmono n k).trans ih

omit hmono in
lemma sum_lo (hK : ∀ n, f n K ≤ f n 0) : Summable (fun n => f n K) :=
  Summable.of_nonneg_of_le (fun n => h0 n K) hK hsum

lemma lo_le_hi (n : ℕ) : Tlo f K n ≤ Thi f n := by
  have hl := sum_lo h0 hsum (fun n => le_zero' hmono n K)
  exact ((summable_nat_add_iff n).2 hl).tsum_le_tsum
    (fun m => le_zero' hmono _ K) ((summable_nat_add_iff n).2 hsum)

include hgap in
lemma step (n : ℕ) (x : ℝ) (h1 : Tlo f K n ≤ x) (h2 : x ≤ Thi f n) :
    ch f K n x ≤ K ∧ Tlo f K (n + 1) ≤ x - f n (ch f K n x) ∧
      x - f n (ch f K n x) ≤ Thi f (n + 1) := by
  have hl := sum_lo h0 hsum (fun n => le_zero' hmono n K)
  have elo : Tlo f K n = f n K + Tlo f K (n + 1) := tail_split hl n
  have ehi : Thi f n = f n 0 + Thi f (n + 1) := tail_split hsum n
  have ehi1 : Thi f (n + 1) = f (n + 1) 0 + Thi f (n + 2) := tail_split hsum (n + 1)
  have elo1 : Tlo f K (n + 1) = f (n + 1) K + Tlo f K (n + 2) := tail_split hl (n + 1)
  have hlh2 := lo_le_hi (K := K) h0 hmono hsum (n + 2)
  have hex : ∃ j, f n j + Tlo f K (n + 1) ≤ x := ⟨K, by linarith⟩
  have hch : ch f K n x = Nat.find hex := by
    unfold ch; rw [dif_pos hex]
  rw [hch]
  refine ⟨Nat.find_min' hex (by linarith), by linarith [Nat.find_spec hex], ?_⟩
  rcases hj : Nat.find hex with _ | i
  · linarith
  · have hlt : i < Nat.find hex := by omega
    have hmin := Nat.find_min hex hlt
    have hiK : i < K := by
      have := Nat.find_min' hex (show f n K + Tlo f K (n + 1) ≤ x by linarith)
      omega
    have hg := hgap n i hiK
    push Not at hmin
    linarith

include hgap in
lemma inv (t : ℝ) (ht1 : Tlo f K 0 ≤ t) (ht2 : t ≤ Thi f 0) (n : ℕ) :
    Tlo f K n ≤ R f K t n ∧ R f K t n ≤ Thi f n := by
  induction n with
  | zero => exact ⟨ht1, ht2⟩
  | succ n ih =>
    obtain ⟨-, a, b⟩ := step h0 hmono hsum hgap n _ ih.1 ih.2
    exact ⟨a, b⟩

omit h0 hmono hsum in
lemma partial_sum (t : ℝ) (n : ℕ) :
    ∑ m ∈ Finset.range n, f m (ch f K m (R f K t m)) = t - R f K t n := by
  induction n with
  | zero => simp [R]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [R]
    ring

include hgap in
theorem greedy (t : ℝ) (ht1 : Tlo f K 0 ≤ t) (ht2 : t ≤ Thi f 0) :
    ∃ c : ℕ → ℕ, (∀ n, c n ≤ K) ∧ HasSum (fun n => f n (c n)) t := by
  refine ⟨fun m => ch f K m (R f K t m), fun n => ?_, ?_⟩
  · have := inv h0 hmono hsum hgap t ht1 ht2 n
    exact (step h0 hmono hsum hgap n _ this.1 this.2).1
  have hs : Summable (fun m => f m (ch f K m (R f K t m))) :=
    Summable.of_nonneg_of_le (fun m => h0 _ _) (fun m => le_zero' hmono _ _) hsum
  rw [hs.hasSum_iff_tendsto_nat]
  have hl := sum_lo h0 hsum (fun n => le_zero' hmono n K)
  have hR : Tendsto (fun n => R f K t n) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_sum_nat_add (fun m => f m K))
      (tendsto_sum_nat_add (fun m => f m 0))
      (fun n => (inv h0 hmono hsum hgap t ht1 ht2 n).1)
      (fun n => (inv h0 hmono hsum hgap t ht1 ht2 n).2)
  have := (tendsto_const_nhds (x := t)).sub hR
  rw [sub_zero] at this
  refine this.congr (fun n => ?_)
  rw [partial_sum]

end
end Greedy

/-- the concrete choices: 1 / (2^(n+4) + (j+1)) -/
noncomputable def F (n j : ℕ) : ℝ := 1 / ((2 : ℝ) ^ (n + 4) + (j + 1))

lemma F_pos (n j : ℕ) : 0 < F n j := by unfold F; positivity

lemma F_mono (n j : ℕ) : F n (j + 1) ≤ F n j := by
  unfold F
  apply one_div_le_one_div_of_le (by positivity)
  push_cast; linarith

lemma F_sum : Summable (fun n => F n 0) := by
  refine Summable.of_nonneg_of_le (fun n => (F_pos n 0).le) (fun n => ?_)
    (summable_geometric_two)
  unfold F
  rw [one_div_pow]
  apply one_div_le_one_div_of_le (by positivity)
  have : (2 : ℝ) ^ n ≤ 2 ^ (n + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
  push_cast; linarith

lemma F_gap (n j : ℕ) (hj : j < 16) : F n j - F n (j + 1) ≤ F (n + 1) 0 - F (n + 1) 16 := by
  unfold F
  have hP : (16 : ℝ) ≤ 2 ^ (n + 4) := by
    have : (2 : ℝ) ^ 4 ≤ 2 ^ (n + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; linarith
  have e : (2 : ℝ) ^ (n + 1 + 4) = 2 * 2 ^ (n + 4) := by ring
  rw [e]
  generalize (2 : ℝ) ^ (n + 4) = P at hP ⊢
  have hj' : (j : ℝ) ≤ 15 := by exact_mod_cast (by omega : j ≤ 15)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast
  have hx : (0 : ℝ) < P + (j + 1) := by linarith
  have hx1 : (0 : ℝ) < P + (j + 1 + 1) := by linarith
  have hy : (0 : ℝ) < 2 * P + (0 + 1) := by linarith
  have hy1 : (0 : ℝ) < 2 * P + (16 + 1) := by linarith
  rw [div_sub_div _ _ hx.ne' hx1.ne', div_sub_div _ _ hy.ne' hy1.ne',
    div_le_div_iff₀ (mul_pos hx hx1) (mul_pos hy hy1)]
  nlinarith

theorem erdos_264.parts.i : ¬IsIrrationalitySequence (2 ^ ·) := by
  intro h
  have h0 : ∀ n j, 0 ≤ F n j := fun n j => (F_pos n j).le
  have hlt : Greedy.Tlo F 16 0 < Greedy.Thi F 0 := by
    unfold Greedy.Tlo Greedy.Thi
    simp only [add_zero]
    exact Summable.tsum_lt_tsum (i := 0)
      (fun n => Greedy.le_zero' F_mono n 16)
      (by unfold F; apply one_div_lt_one_div_of_lt (by positivity); push_cast; linarith)
      (Greedy.sum_lo h0 F_sum (fun n => Greedy.le_zero' F_mono n 16)) F_sum
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show Greedy.Tlo F 16 0 + 103 / 90 <
    Greedy.Thi F 0 + 103 / 90 by linarith)
  obtain ⟨c, hc, hsum⟩ := Greedy.greedy h0 F_mono F_sum F_gap ((q : ℝ) - 103 / 90)
    (by linarith) (by linarith)
  let b : ℕ → ℤ := fun n => if n < 4 then 1 else (c (n - 4) : ℤ) + 1
  have hb1 : ∀ n, 1 ≤ b n := by
    intro n; simp only [b]; split_ifs <;> omega
  have hb2 : ∀ n, b n ≤ 17 := by
    intro n; simp only [b]; split_ifs
    · omega
    · have := hc (n - 4); omega
  have key := h b ⟨17, by rintro _ ⟨n, rfl⟩; exact hb2 n⟩ ⟨1, by rintro _ ⟨n, rfl⟩; exact hb1 n⟩
    (by
      rintro ⟨n, hn⟩
      have := hb1 n
      have hpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
      beta_reduce at hn
      linarith)
    (by rintro ⟨n, hn⟩; have := hb1 n; omega)
  set g : ℕ → ℝ := fun n => (1 : ℝ) / ((((2 ^ n : ℕ) : ℤ) : ℝ) + ((b n : ℤ) : ℝ)) with hg
  have hshift : (fun i => g (i + 4)) = fun i => F i (c i) := by
    funext i
    simp only [hg, b, F, show ¬ (i + 4 < 4) by omega, if_false, Nat.add_sub_cancel]
    push_cast
    ring_nf
  have hgs : Summable g := by
    rw [← summable_nat_add_iff 4, hshift]
    exact hsum.summable
  have htot : ∑' n, g n = q := by
    rw [← hgs.sum_add_tsum_nat_add 4, hshift, hsum.tsum_eq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hg, b]
    norm_num
  exact key.ne_rat q htot

end Erdos264

#print axioms Erdos264.erdos_264.parts.i
