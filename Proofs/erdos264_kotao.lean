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
  (hgap : ∀ n j, j < K → f n j - f n (j + 1) ≤ Thi f (n + 1) - Tlo f K (n + 1))
include h0 hmono hsum

omit h0 hsum in
lemma le_zero' (n j : ℕ) : f n j ≤ f n 0 := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact (hmono n j).trans ih

omit hmono in
lemma sum_lo (hK : ∀ n, f n K ≤ f n 0) : Summable (fun n => f n K) :=
  Summable.of_nonneg_of_le (fun n => h0 n K) hK hsum

include hgap in
lemma step (n : ℕ) (x : ℝ) (h1 : Tlo f K n ≤ x) (h2 : x ≤ Thi f n) :
    ch f K n x ≤ K ∧ Tlo f K (n + 1) ≤ x - f n (ch f K n x) ∧
      x - f n (ch f K n x) ≤ Thi f (n + 1) := by
  have hl := sum_lo h0 hsum (fun n => le_zero' hmono n K)
  have elo : Tlo f K n = f n K + Tlo f K (n + 1) := tail_split hl n
  have ehi : Thi f n = f n 0 + Thi f (n + 1) := tail_split hsum n
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
/-- greedy lemma, version with the full tail spread in the gap condition -/
theorem greedy (t : ℝ) (ht1 : Tlo f K 0 ≤ t) (ht2 : t ≤ Thi f 0) :
    ∃ c : ℕ → ℕ, (∀ n, c n ≤ K) ∧ HasSum (fun n => f n (c n)) t := by
  refine ⟨fun m => ch f K m (R f K t m), fun n => ?_, ?_⟩
  · have := inv h0 hmono hsum hgap t ht1 ht2 n
    exact (step h0 hmono hsum hgap n _ this.1 this.2).1
  have hs : Summable (fun m => f m (ch f K m (R f K t m))) :=
    Summable.of_nonneg_of_le (fun m => h0 _ _) (fun m => le_zero' hmono _ _) hsum
  rw [hs.hasSum_iff_tendsto_nat]
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

/-- reindexing ℕ ≃ (n, ∞) -/
def eIoi (n : ℕ) : ℕ ≃ Set.Ioi n where
  toFun m := ⟨m + n + 1, by simp only [Set.mem_Ioi]; omega⟩
  invFun k := k.1 - n - 1
  left_inv m := by show m + n + 1 - n - 1 = m; omega
  right_inv k := Subtype.ext (by
    have := k.2
    simp only [Set.mem_Ioi] at this
    show k.1 - n - 1 + n + 1 = k.1
    omega)

lemma tsum_Ioi_a (a : ℕ → ℕ) (n : ℕ) :
    ∑' k : Set.Ioi n, (1 : ℝ) / (a k : ℝ) ^ 2 = ∑' m, (1 : ℝ) / (a (m + n + 1) : ℝ) ^ 2 :=
  ((eIoi n).tsum_eq (fun k => (1 : ℝ) / (a k : ℝ) ^ 2)).symm

/-- the concrete choices: 1 / (a (n + N) + (j + 1)) -/
noncomputable def G (a : ℕ → ℕ) (N n j : ℕ) : ℝ := 1 / ((a (n + N) : ℝ) + ((j : ℝ) + 1))

section KT
variable {a : ℕ → ℕ} {N : ℕ}

lemma G_pos (n j : ℕ) : 0 < G a N n j := by unfold G; positivity

lemma G_mono (n j : ℕ) : G a N n (j + 1) ≤ G a N n j := by
  unfold G
  apply one_div_le_one_div_of_le (by positivity)
  push_cast; linarith

lemma inv_sq_summable (hpos : ∀ n, 0 < a n) (h₃ : Summable ((1 : ℝ) / a ·)) :
    Summable (fun k => (1 : ℝ) / (a k : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h₃
  show (1 : ℝ) / (a k : ℝ) ^ 2 ≤ 1 / (a k : ℝ)
  have h1 : (1 : ℝ) ≤ a k := by exact_mod_cast hpos k
  apply one_div_le_one_div_of_le (by linarith)
  nlinarith

lemma G_sum (hpos : ∀ n, 0 < a n) (h₃ : Summable ((1 : ℝ) / a ·)) :
    Summable (fun n => G a N n 0) := by
  have hs : Summable (fun n => (1 : ℝ) / (a (n + N) : ℝ)) :=
    (summable_nat_add_iff (f := fun k => (1 : ℝ) / (a k : ℝ)) N).2 h₃
  refine Summable.of_nonneg_of_le (fun n => (G_pos n 0).le) (fun n => ?_) hs
  unfold G
  apply one_div_le_one_div_of_le (Nat.cast_pos.2 (hpos _))
  push_cast; linarith

lemma G_gap1 (hpos : ∀ n, 0 < a n) (n j : ℕ) :
    G a N n j - G a N n (j + 1) ≤ 1 / (a (n + N) : ℝ) ^ 2 := by
  unfold G
  have hA : (0 : ℝ) < a (n + N) := Nat.cast_pos.2 (hpos _)
  generalize (a (n + N) : ℝ) = A at hA ⊢
  push_cast
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hx : (0 : ℝ) < A + (j + 1) := by linarith
  have hx1 : (0 : ℝ) < A + (j + 1 + 1) := by linarith
  rw [div_sub_div _ _ hx.ne' hx1.ne', div_le_div_iff₀ (mul_pos hx hx1) (by positivity)]
  nlinarith

lemma G_spread (n K : ℕ) (hA : (K : ℝ) + 1 ≤ a (n + N)) :
    (K : ℝ) / 4 * (1 / (a (n + N) : ℝ) ^ 2) ≤ G a N n 0 - G a N n K := by
  unfold G
  rw [Nat.cast_zero, zero_add]
  generalize (a (n + N) : ℝ) = A at hA ⊢
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hA0 : (0 : ℝ) < A := by linarith
  have hx : (0 : ℝ) < A + 1 := by linarith
  have hx1 : (0 : ℝ) < A + (K + 1) := by linarith
  rw [div_sub_div _ _ hx.ne' hx1.ne', mul_one_div,
    div_le_div_iff₀ (by positivity) (mul_pos hx hx1)]
  have h1 : (A + 1) * (A + (K + 1)) ≤ 4 * A ^ 2 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 hK
  nlinarith

lemma spread_tail (hpos : ∀ n, 0 < a n) (h₃ : Summable ((1 : ℝ) / a ·)) (K : ℕ)
    (hbig : ∀ m, (K : ℝ) + 1 ≤ a (m + N)) (n : ℕ) :
    (K : ℝ) / 4 * ∑' m, 1 / (a (m + (n + N) + 1) : ℝ) ^ 2 ≤
      Greedy.Thi (G a N) (n + 1) - Greedy.Tlo (G a N) K (n + 1) := by
  have hs0 : Summable (fun m => G a N (m + (n + 1)) 0) :=
    (summable_nat_add_iff (f := fun k => G a N k 0) (n + 1)).2 (G_sum hpos h₃)
  have hsK : Summable (fun m => G a N (m + (n + 1)) K) :=
    Summable.of_nonneg_of_le (fun m => (G_pos _ _).le)
      (fun m => Greedy.le_zero' G_mono _ K) hs0
  have hsq : Summable (fun m => 1 / (a (m + (n + N) + 1) : ℝ) ^ 2) := by
    have := (summable_nat_add_iff (f := fun k => (1 : ℝ) / (a k : ℝ) ^ 2) (n + N + 1)).2
      (inv_sq_summable hpos h₃)
    simpa only [← add_assoc] using this
  unfold Greedy.Thi Greedy.Tlo
  rw [← hs0.tsum_sub hsK, ← tsum_mul_left]
  refine (hsq.mul_left _).tsum_le_tsum (fun m => ?_) (hs0.sub hsK)
  have e : m + (n + 1) + N = m + (n + N) + 1 := by omega
  have := G_spread (a := a) (N := N) (m + (n + 1)) K (hbig _)
  rw [e] at this
  exact this

end KT

theorem erdos_264.variants.ko_tao_neg {a : ℕ → ℕ} (h₁ : StrictMono a) (h₂ : 0 ∉ Set.range a)
    (h₃ : Summable ((1 : ℝ) / a ·))
    (h₄ : ∃ C > 0, ∀ᶠ n in atTop, C ≤ a n ^ 2 * ∑' k : Set.Ioi n, (1 : ℝ) / a k ^ 2) :
    ¬IsIrrationalitySequence a := by
  intro h
  obtain ⟨C, hC, hev⟩ := h₄
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  have hpos : ∀ n, 0 < a n := fun n => Nat.pos_of_ne_zero (fun h0 => h₂ ⟨n, h0⟩)
  obtain ⟨K, hK1, hKC⟩ : ∃ K : ℕ, 1 ≤ K ∧ 4 ≤ (K : ℝ) * C := by
    refine ⟨⌈4 / C⌉₊ + 1, by omega, ?_⟩
    have h1 : 4 / C ≤ ((⌈4 / C⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (4 / C)]
    exact (div_le_iff₀ hC).1 h1
  obtain ⟨N, hNN0, hNK⟩ : ∃ N, N0 ≤ N ∧ K + 1 ≤ N := ⟨N0 + K + 1, by omega, by omega⟩
  have hbig : ∀ m, (K : ℝ) + 1 ≤ a (m + N) := by
    intro m
    have : m + N ≤ a (m + N) := h₁.id_le (m + N)
    exact_mod_cast (by omega : K + 1 ≤ a (m + N))
  have hgap : ∀ n j, j < K → G a N n j - G a N n (j + 1) ≤
      Greedy.Thi (G a N) (n + 1) - Greedy.Tlo (G a N) K (n + 1) := by
    intro n j _
    refine (G_gap1 hpos n j).trans (le_trans ?_ (spread_tail hpos h₃ K hbig n))
    have h4 := hN0 (n + N) (by omega)
    have h4' : C ≤ (a (n + N) : ℝ) ^ 2 *
        ∑' m, (1 : ℝ) / (a (m + (n + N) + 1) : ℝ) ^ 2 := by
      rw [← tsum_Ioi_a]; exact_mod_cast h4
    have hA : (0 : ℝ) < a (n + N) := Nat.cast_pos.2 (hpos _)
    generalize (∑' m, (1 : ℝ) / (a (m + (n + N) + 1) : ℝ) ^ 2) = T at h4' ⊢
    generalize (a (n + N) : ℝ) = A at hA h4' ⊢
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have h3 := mul_le_mul_of_nonneg_left h4' hK0
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h0 : ∀ n j, 0 ≤ G a N n j := fun n j => (G_pos n j).le
  have hsum := G_sum (N := N) hpos h₃
  have hlt : Greedy.Tlo (G a N) K 0 < Greedy.Thi (G a N) 0 := by
    unfold Greedy.Tlo Greedy.Thi
    simp only [add_zero]
    have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    exact Summable.tsum_lt_tsum (i := 0)
      (fun n => Greedy.le_zero' G_mono n K)
      (by unfold G; apply one_div_lt_one_div_of_lt (by positivity); push_cast; linarith)
      (Greedy.sum_lo h0 hsum (fun n => Greedy.le_zero' G_mono n K)) hsum
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i ∈ Finset.range N, (1 : ℝ) / ((a i : ℝ) + 1) := ⟨_, rfl⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show Greedy.Tlo (G a N) K 0 + S <
    Greedy.Thi (G a N) 0 + S by linarith)
  obtain ⟨c, hc, hsumc⟩ := Greedy.greedy h0 G_mono hsum hgap ((q : ℝ) - S)
    (by linarith) (by linarith)
  let b : ℕ → ℤ := fun n => if n < N then 1 else (c (n - N) : ℤ) + 1
  have hb1 : ∀ n, 1 ≤ b n := by
    intro n; simp only [b]; split_ifs <;> omega
  have hb2 : ∀ n, b n ≤ (K : ℤ) + 1 := by
    intro n; simp only [b]; split_ifs
    · omega
    · have := hc (n - N); omega
  have key := h b ⟨(K : ℤ) + 1, by rintro _ ⟨n, rfl⟩; exact hb2 n⟩
    ⟨1, by rintro _ ⟨n, rfl⟩; exact hb1 n⟩
    (by
      rintro ⟨n, hn⟩
      have := hb1 n
      have hpos' : (0 : ℤ) ≤ ((a n : ℕ) : ℤ) := Int.natCast_nonneg _
      beta_reduce at hn
      linarith)
    (by rintro ⟨n, hn⟩; have := hb1 n; omega)
  set g : ℕ → ℝ := fun n => (1 : ℝ) / (((a n : ℤ) : ℝ) + ((b n : ℤ) : ℝ)) with hg
  have hshift : (fun i => g (i + N)) = fun i => G a N i (c i) := by
    funext i
    simp [hg, b, G, show ¬ (i + N < N) by omega]
  have hgs : Summable g := by
    rw [← summable_nat_add_iff N, hshift]
    exact hsumc.summable
  have hfin : ∑ i ∈ Finset.range N, g i = S := by
    rw [hS]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < N := Finset.mem_range.1 hi
    simp [hg, b, hi']
  have htot : ∑' n, g n = q := by
    rw [← hgs.sum_add_tsum_nat_add N, hshift, hsumc.tsum_eq, hfin]
    ring
  exact key.ne_rat q htot

end Erdos264

#print axioms Erdos264.erdos_264.variants.ko_tao_neg
