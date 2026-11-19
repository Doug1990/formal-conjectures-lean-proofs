import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace Erdos263

def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, a n > 0) ∧
    StrictMono a ∧
    (∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
      atTop.Tendsto (fun n : ℕ => (a n : ℝ) / (b n : ℝ)) (𝓝 1) →
      Irrational (∑' n, 1 / (b n : ℝ)))

/-! Greedy lemma with a variable range `K n` of choices at step `n`. -/
namespace GreedyV

variable (f : ℕ → ℕ → ℝ) (K : ℕ → ℕ)

noncomputable def Tlo (n : ℕ) : ℝ := ∑' m, f (m + n) (K (m + n))
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
  (hgap : ∀ n j, j < K n → f n j - f n (j + 1) ≤ f (n + 1) 0 - f (n + 1) (K (n + 1)))
include h0 hmono hsum

omit h0 hsum in
lemma le_zero' (n j : ℕ) : f n j ≤ f n 0 := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact (hmono n j).trans ih

omit hmono in
lemma sum_lo (hK : ∀ n, f n (K n) ≤ f n 0) : Summable (fun n => f n (K n)) :=
  Summable.of_nonneg_of_le (fun n => h0 n (K n)) hK hsum

lemma lo_le_hi (n : ℕ) : Tlo f K n ≤ Thi f n := by
  have hl := sum_lo (K := K) h0 hsum (fun n => le_zero' hmono n (K n))
  exact ((summable_nat_add_iff n).2 hl).tsum_le_tsum
    (fun m => le_zero' hmono _ _) ((summable_nat_add_iff n).2 hsum)

include hgap in
lemma step (n : ℕ) (x : ℝ) (h1 : Tlo f K n ≤ x) (h2 : x ≤ Thi f n) :
    ch f K n x ≤ K n ∧ Tlo f K (n + 1) ≤ x - f n (ch f K n x) ∧
      x - f n (ch f K n x) ≤ Thi f (n + 1) := by
  have hl := sum_lo (K := K) h0 hsum (fun n => le_zero' hmono n (K n))
  have elo : Tlo f K n = f n (K n) + Tlo f K (n + 1) :=
    tail_split (g := fun n => f n (K n)) hl n
  have ehi : Thi f n = f n 0 + Thi f (n + 1) := tail_split (g := fun n => f n 0) hsum n
  have ehi1 : Thi f (n + 1) = f (n + 1) 0 + Thi f (n + 2) :=
    tail_split (g := fun n => f n 0) hsum (n + 1)
  have elo1 : Tlo f K (n + 1) = f (n + 1) (K (n + 1)) + Tlo f K (n + 2) :=
    tail_split (g := fun n => f n (K n)) hl (n + 1)
  have hlh2 := lo_le_hi (K := K) h0 hmono hsum (n + 2)
  have hex : ∃ j, f n j + Tlo f K (n + 1) ≤ x := ⟨K n, by linarith⟩
  have hch : ch f K n x = Nat.find hex := by
    unfold ch; rw [dif_pos hex]
  rw [hch]
  refine ⟨Nat.find_min' hex (by linarith), by linarith [Nat.find_spec hex], ?_⟩
  rcases hj : Nat.find hex with _ | i
  · linarith
  · have hlt : i < Nat.find hex := by omega
    have hmin := Nat.find_min hex hlt
    have hiK : i < K n := by
      have := Nat.find_min' hex (show f n (K n) + Tlo f K (n + 1) ≤ x by linarith)
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
    ∃ c : ℕ → ℕ, (∀ n, c n ≤ K n) ∧ HasSum (fun n => f n (c n)) t := by
  refine ⟨fun m => ch f K m (R f K t m), fun n => ?_, ?_⟩
  · have := inv h0 hmono hsum hgap t ht1 ht2 n
    exact (step h0 hmono hsum hgap n _ this.1 this.2).1
  have hs : Summable (fun m => f m (ch f K m (R f K t m))) :=
    Summable.of_nonneg_of_le (fun m => h0 _ _) (fun m => le_zero' hmono _ _) hsum
  rw [hs.hasSum_iff_tendsto_nat]
  have hl := sum_lo (K := K) h0 hsum (fun n => le_zero' hmono n (K n))
  have hR : Tendsto (fun n => R f K t n) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_sum_nat_add (fun m => f m (K m)))
      (tendsto_sum_nat_add (fun m => f m 0))
      (fun n => (inv h0 hmono hsum hgap t ht1 ht2 n).1)
      (fun n => (inv h0 hmono hsum hgap t ht1 ht2 n).2)
  have := (tendsto_const_nhds (x := t)).sub hR
  rw [sub_zero] at this
  refine this.congr (fun n => ?_)
  rw [partial_sum]

end
end GreedyV

namespace S

/-- number of choices at step `n` -/
def Kf (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => 2 * a (m + 1) ^ 2 / a m ^ 2 + 1

lemma Kf_pos (a : ℕ → ℕ) (n : ℕ) : 1 ≤ Kf a n := by
  cases n <;> simp [Kf]

lemma Kf_spec (a : ℕ → ℕ) (m : ℕ) (ha : 0 < a m) :
    2 * a (m + 1) ^ 2 ≤ Kf a (m + 1) * a m ^ 2 := by
  have hy : 0 < a m ^ 2 := by positivity
  have := Nat.lt_div_mul_add (a := 2 * a (m + 1) ^ 2) hy
  simp only [Kf]
  rw [Nat.add_mul, one_mul]
  omega

lemma Kf_le (a : ℕ → ℕ) (m : ℕ) :
    (Kf a (m + 1) : ℝ) ≤ 2 * (a (m + 1) : ℝ) ^ 2 / (a m : ℝ) ^ 2 + 1 := by
  simp only [Kf]
  push_cast
  have := Nat.cast_div_le (α := ℝ) (m := 2 * a (m + 1) ^ 2) (n := a m ^ 2)
  push_cast at this
  linarith

lemma ratio (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (hmono : StrictMono a)
    (h : Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (Kf a n : ℝ) / a n) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have h1 : Tendsto (fun n : ℕ => 1 / (a (n + 1) : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : (n : ℝ) + 1 ≤ a (n + 1) := by exact_mod_cast hmono.id_le (n + 1)
    exact one_div_le_one_div_of_le (by positivity) h1
  have h2 := (h.const_mul 2).add h1
  rw [mul_zero, add_zero] at h2
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) h2
  have hA : (0 : ℝ) < a n := by exact_mod_cast hpos n
  have hB : (0 : ℝ) < a (n + 1) := by exact_mod_cast hpos (n + 1)
  have hk := Kf_le a n
  rw [div_le_iff₀ hB]
  have e : (2 * ((a (n + 1) : ℝ) / (a n : ℝ) ^ 2) + 1 / (a (n + 1) : ℝ)) * (a (n + 1) : ℝ)
      = 2 * (a (n + 1) : ℝ) ^ 2 / (a n : ℝ) ^ 2 + 1 := by
    field_simp
  rw [e]
  exact hk

lemma gap (A B K j : ℝ) (hA : 0 < A) (hB : 0 < B) (hK0 : 0 ≤ K) (hKB : K ≤ B)
    (hspec : 2 * B ^ 2 ≤ K * A ^ 2) (hj : 0 ≤ j) :
    1 / (A + j) - 1 / (A + (j + 1)) ≤ 1 / (B + 0) - 1 / (B + K) := by
  have h1 : (0 : ℝ) < A + j := by linarith
  have h2 : (0 : ℝ) < A + (j + 1) := by linarith
  have h3 : (0 : ℝ) < B + 0 := by linarith
  have h4 : (0 : ℝ) < B + K := by linarith
  rw [div_sub_div _ _ h1.ne' h2.ne', div_sub_div _ _ h3.ne' h4.ne',
    div_le_div_iff₀ (mul_pos h1 h2) (mul_pos h3 h4)]
  have hAA : A ^ 2 ≤ (A + j) * (A + (j + 1)) := by nlinarith
  have hK : K * A ^ 2 ≤ K * ((A + j) * (A + (j + 1))) := mul_le_mul_of_nonneg_left hAA hK0
  have hBB : B * (B + K) ≤ 2 * B ^ 2 := by nlinarith
  nlinarith

lemma dist_bound (A c K : ℝ) (hA : 0 < A) (hc : 0 ≤ c) (hcK : c ≤ K) :
    |A / (A + c) - 1| ≤ K / A := by
  have hpos : 0 < A + c := by linarith
  rw [div_sub_one hpos.ne', abs_div, abs_of_pos hpos, show A - (A + c) = -c by ring,
    abs_neg, abs_of_nonneg hc]
  exact div_le_div₀ (by linarith) hcK hA (by linarith)

end S

open S in
theorem erdos_263.variants.sub_doubly_exponential (a: ℕ -> ℕ)
    (ha' : StrictMono a)
    (ha'' : Summable (fun n : ℕ => 1 / (a n : ℝ)))
    (ha''' : atTop.Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n ^ 2) (𝓝 0)) :
    ¬ IsIrrationalitySequence a := by
  rintro ⟨hpos, -, H⟩
  have hrat := ratio a hpos ha' ha'''
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hrat.eventually (gt_mem_nhds zero_lt_one))
  have hKa : ∀ n, N0 ≤ n → (Kf a n : ℝ) ≤ a n := by
    intro n hn
    have := hN0 n hn
    have hA : (0 : ℝ) < a n := by exact_mod_cast hpos n
    rw [div_lt_one hA] at this
    exact this.le
  set f : ℕ → ℕ → ℝ := fun n j => 1 / ((a (N0 + n) : ℝ) + j) with hf
  set K : ℕ → ℕ := fun n => Kf a (N0 + n) with hK
  have h0 : ∀ n j, 0 ≤ f n j := fun n j => by
    simp only [hf]; positivity
  have hmono : ∀ n j, f n (j + 1) ≤ f n j := fun n j => by
    simp only [hf]
    have : (0 : ℝ) < a (N0 + n) := by exact_mod_cast hpos _
    apply one_div_le_one_div_of_le (by positivity)
    push_cast; linarith
  have hsum : Summable (fun n => f n 0) := by
    have := (summable_nat_add_iff N0).2 ha''
    refine this.congr (fun n => ?_)
    simp only [hf, Nat.cast_zero, add_zero, add_comm n N0]
  have hgap : ∀ n j, j < K n → f n j - f n (j + 1) ≤ f (n + 1) 0 - f (n + 1) (K (n + 1)) := by
    intro n j _
    simp only [hf, hK]
    have hA : (0 : ℝ) < a (N0 + n) := by exact_mod_cast hpos _
    have hB : (0 : ℝ) < a (N0 + n + 1) := by exact_mod_cast hpos _
    have hspec := Kf_spec a (N0 + n) (hpos _)
    have hspec' : 2 * (a (N0 + n + 1) : ℝ) ^ 2 ≤ (Kf a (N0 + n + 1) : ℝ) * (a (N0 + n) : ℝ) ^ 2 := by
      exact_mod_cast hspec
    have hKB := hKa (N0 + n + 1) (by omega)
    have := gap (a (N0 + n)) (a (N0 + n + 1)) (Kf a (N0 + n + 1)) j hA hB (by positivity) hKB
      hspec' (by positivity)
    push_cast
    simpa [add_assoc] using this
  have hlt : GreedyV.Tlo f K 0 < GreedyV.Thi f 0 := by
    unfold GreedyV.Tlo GreedyV.Thi
    simp only [add_zero]
    refine Summable.tsum_lt_tsum (i := 0) (fun n => GreedyV.le_zero' hmono n (K n)) ?_
      (GreedyV.sum_lo h0 hsum (fun n => GreedyV.le_zero' hmono n (K n))) hsum
    simp only [hf, hK]
    have hA : (0 : ℝ) < a (N0 + 0) := by exact_mod_cast hpos _
    apply one_div_lt_one_div_of_lt (by positivity)
    have : (1 : ℝ) ≤ Kf a (N0 + 0) := by exact_mod_cast Kf_pos a _
    push_cast; linarith
  set P : ℝ := ∑ i ∈ Finset.range N0, 1 / (a i : ℝ) with hP
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show GreedyV.Tlo f K 0 + P <
    GreedyV.Thi f 0 + P by linarith)
  obtain ⟨c, hc, hsumc⟩ := GreedyV.greedy h0 hmono hsum hgap ((q : ℝ) - P)
    (by linarith) (by linarith)
  let b : ℕ → ℕ := fun n => if n < N0 then a n else a n + c (n - N0)
  have hbpos : ∀ n, b n > 0 := by
    intro n; simp only [b]; split_ifs
    · exact hpos n
    · have := hpos n; omega
  have htend : Tendsto (fun n : ℕ => (a n : ℝ) / (b n : ℝ)) atTop (𝓝 1) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall (fun n => dist_nonneg)) ?_ hrat
    rw [eventually_atTop]
    refine ⟨N0, fun n hn => ?_⟩
    rw [Real.dist_eq]
    simp only [b, show ¬ n < N0 by omega, if_false]
    have hcn := hc (n - N0)
    simp only [hK, show N0 + (n - N0) = n by omega] at hcn
    push_cast
    exact dist_bound _ _ _ (by exact_mod_cast hpos n) (by positivity) (by exact_mod_cast hcn)
  have key := H b ⟨hbpos, htend⟩
  set g : ℕ → ℝ := fun n => 1 / (b n : ℝ) with hg
  have hshift : (fun i => g (i + N0)) = fun i => f i (c i) := by
    funext i
    have h1 : ¬ (i + N0 < N0) := by omega
    have h2 : i + N0 - N0 = i := by omega
    have h3 : i + N0 = N0 + i := by omega
    simp only [hg, b, hf, h1, if_false, h2]
    rw [h3]
    push_cast
    rfl
  have hgs : Summable g := by
    rw [← summable_nat_add_iff N0, hshift]
    exact hsumc.summable
  have htot : ∑' n, g n = q := by
    rw [← hgs.sum_add_tsum_nat_add N0, hshift, hsumc.tsum_eq]
    have : ∑ i ∈ Finset.range N0, g i = P := by
      rw [hP]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have : i < N0 := Finset.mem_range.1 hi
      simp only [hg, b, this, if_true]
    rw [this]
    ring
  exact key.ne_rat q htot

end Erdos263

#print axioms Erdos263.erdos_263.variants.sub_doubly_exponential
