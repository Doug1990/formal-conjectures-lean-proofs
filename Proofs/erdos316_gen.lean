import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Partition.Finpartition

namespace Erdos316

/-- Every `m ≤ n!` is a sum of distinct divisors of `n!` (from results/erdos18_upper.lean). -/
theorem rep (n : ℕ) (hn : 2 ≤ n) : ∀ m ≤ n.factorial, ∃ B : Finset ℕ,
    B ⊆ n.factorial.divisors ∧ B.card ≤ n - 1 ∧ ∑ i ∈ B, i = m := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro m hm
    have h2 : Nat.factorial 2 = 2 := rfl
    rw [h2] at hm ⊢
    interval_cases m
    · exact ⟨∅, by simp, by simp, by simp⟩
    · exact ⟨{1}, by decide, by simp, by simp⟩
    · exact ⟨{2}, by decide, by simp, by simp⟩
  | succ n hn ih =>
    intro m hm
    rw [Nat.factorial_succ] at hm
    have hq : m / (n + 1) ≤ n.factorial := Nat.div_le_of_le_mul hm
    obtain ⟨B, hBsub, hBcard, hBsum⟩ := ih (m / (n + 1)) hq
    have hr : m % (n + 1) < n + 1 := Nat.mod_lt m (Nat.succ_pos n)
    have hdm : m = (n + 1) * (m / (n + 1)) + m % (n + 1) := (Nat.div_add_mod m (n + 1)).symm
    set q := m / (n + 1)
    set r := m % (n + 1)
    have hfpos : 0 < n.factorial := Nat.factorial_pos n
    have hinj : Set.InjOn (fun d : ℕ => d * (n + 1)) B := by
      intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n) h
    have hsumB' : ∑ i ∈ B.image (fun d : ℕ => d * (n + 1)), i = (n + 1) * q := by
      rw [Finset.sum_image hinj, ← Finset.sum_mul, hBsum, Nat.mul_comm]
    have hsub' : B.image (fun d : ℕ => d * (n + 1)) ⊆ (n + 1).factorial.divisors := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      have hd' := Nat.dvd_of_mem_divisors (hBsub hd)
      refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
      rw [Nat.factorial_succ, Nat.mul_comm (n + 1)]
      exact Nat.mul_dvd_mul_right hd' _
    have hcard' : (B.image (fun d : ℕ => d * (n + 1))).card ≤ n - 1 :=
      (Finset.card_image_le).trans hBcard
    by_cases hr0 : r = 0
    · refine ⟨B.image (fun d : ℕ => d * (n + 1)), hsub', by omega, ?_⟩
      rw [hsumB']; omega
    · have hnot : r ∉ B.image (fun d : ℕ => d * (n + 1)) := by
        intro hx
        obtain ⟨d, hd, hdr⟩ := Finset.mem_image.mp hx
        have hdpos : 0 < d := Nat.pos_of_mem_divisors (hBsub hd)
        have : n + 1 ≤ d * (n + 1) := Nat.le_mul_of_pos_left _ hdpos
        omega
      refine ⟨insert r (B.image (fun d : ℕ => d * (n + 1))), ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]
          refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
          exact Nat.dvd_factorial (by omega) (by omega)
        · exact hsub' h
      · rw [Finset.card_insert_of_notMem hnot]; omega
      · rw [Finset.sum_insert hnot, hsumB']; omega

/-- `g K = ∑_{k=2}^{K} 1/k`. -/
def g (K : ℕ) : ℚ := ∑ k ∈ Finset.Icc 2 K, (1 / k : ℚ)

lemma g_succ (K : ℕ) (hK : 1 ≤ K) : g (K + 1) = g K + 1 / ((K : ℚ) + 1) := by
  unfold g
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast
  ring

lemma g_eq (K : ℕ) (hK : 1 ≤ K) : g K = harmonic K - 1 := by
  induction K, hK using Nat.le_induction with
  | base =>
    simp [g, harmonic]
  | succ K hK ih =>
    rw [g_succ K hK, ih, harmonic_succ]
    push_cast
    ring

lemma g_unbounded (n : ℕ) : ∃ N, (n : ℚ) ≤ g N := by
  have h1 := log_le_harmonic_floor (Real.exp (n + 1)) (Real.exp_pos _).le
  rw [Real.log_exp] at h1
  have h2 : ((n : ℚ) + 1) ≤ harmonic ⌊Real.exp (n + 1)⌋₊ := by exact_mod_cast h1
  refine ⟨⌊Real.exp (n + 1)⌋₊ + 1, ?_⟩
  rw [g_eq _ (by omega), harmonic_succ]
  have : (0 : ℚ) ≤ (↑(⌊Real.exp (n + 1)⌋₊ + 1))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  linarith

lemma g_small (K : ℕ) (hK : K ≤ 2) : g K ≤ 1 / 2 := by
  interval_cases K
  · simp [g]
  · simp [g]
  · simp [g]

/-- Sum of `L / a` cast to `ℚ`. -/
lemma castA (s : Finset ℕ) (L : ℕ) (hdvd : ∀ a ∈ s, a ∣ L) (h0 : 0 ∉ s) :
    ((∑ a ∈ s, L / a : ℕ) : ℚ) = L * ∑ a ∈ s, (1 / a : ℚ) := by
  rw [Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 : (x : ℚ) ≠ 0 := by
    have : x ≠ 0 := fun h => h0 (h ▸ hx)
    exact_mod_cast this
  rw [Nat.cast_div (hdvd x hx) hx0]
  ring

lemma no_split (A : Finset ℕ) (L n : ℕ) (hn : 2 ≤ n) (hL : 0 < L)
    (hdvd : ∀ a ∈ A, a ∣ L) (h0 : 0 ∉ A)
    (hsum : ∑ a ∈ A, L / a = n * L - 1) (P : Finpartition A) (hP : P.parts.card ≤ n) :
    ∃ p ∈ P.parts, 1 ≤ ∑ x ∈ p, (1 / x : ℚ) := by
  by_contra hcon
  push Not at hcon
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hpart : ∀ p ∈ P.parts, ∑ x ∈ p, L / x ≤ L - 1 := by
    intro p hp
    have h1 := hcon p hp
    have hsub : p ⊆ A := P.le hp
    have hc := castA p L (fun a ha => hdvd a (hsub ha)) (fun h => h0 (hsub h))
    have h3 : ((∑ x ∈ p, L / x : ℕ) : ℚ) < L := by
      rw [hc]
      calc (L : ℚ) * ∑ x ∈ p, (1 / x : ℚ) < L * 1 := mul_lt_mul_of_pos_left h1 hLq
        _ = L := mul_one _
    have h4 : ∑ x ∈ p, L / x < L := by exact_mod_cast h3
    omega
  have htot : ∑ a ∈ A, L / a = ∑ p ∈ P.parts, ∑ x ∈ p, L / x := by
    conv_lhs => rw [← P.biUnion_parts]
    rw [Finset.sum_biUnion P.disjoint]
    rfl
  have hle : ∑ p ∈ P.parts, ∑ x ∈ p, L / x ≤ P.parts.card • (L - 1) :=
    Finset.sum_le_card_nsmul _ _ _ hpart
  rw [smul_eq_mul] at hle
  have h5 : P.parts.card * (L - 1) ≤ n * (L - 1) := Nat.mul_le_mul_right (L - 1) hP
  have h6 : n * (L - 1) = n * L - n := Nat.mul_sub_one n L
  have h7 : n ≤ n * L := Nat.le_mul_of_pos_right n hL
  omega

lemma construct (n : ℕ) (hn : 2 ≤ n) : ∃ (A : Finset ℕ) (L : ℕ), 2 ∈ A ∧ 0 ∉ A ∧ 1 ∉ A ∧
    0 < L ∧ (∀ a ∈ A, a ∣ L) ∧ ∑ a ∈ A, L / a = n * L - 1 := by
  classical
  have hex := g_unbounded n
  obtain ⟨N, hN, hmin⟩ : ∃ N, (n : ℚ) ≤ g N ∧ ∀ K < N, g K < n :=
    ⟨Nat.find hex, Nat.find_spec hex, fun K hK => lt_of_not_ge (Nat.find_min hex hK)⟩
  have hn' : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hN3 : 3 ≤ N := by
    by_contra h
    have := g_small N (by omega)
    linarith
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  have hgK : g K < n := hmin K (by omega)
  set F := (K + 1).factorial with hFdef
  have hFpos : 0 < F := Nat.factorial_pos _
  have hKpos : 0 < K.factorial := Nat.factorial_pos _
  -- s = ∑_{k=2}^K F / k
  have hdK : ∀ a ∈ Finset.Icc 2 K, a ∣ F := fun a ha => by
    have := Finset.mem_Icc.mp ha
    exact Nat.dvd_factorial (by omega) (by omega)
  have h0K : 0 ∉ Finset.Icc 2 K := by simp
  have hs := castA (Finset.Icc 2 K) F hdK h0K
  rw [← g] at hs
  set s := ∑ a ∈ Finset.Icc 2 K, F / a with hsdef
  have hFq : (F : ℚ) = ((K : ℚ) + 1) * K.factorial := by
    rw [hFdef, Nat.factorial_succ]; push_cast; ring
  have hK1 : ((K : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero K
  have hFK : (F : ℚ) * (1 / ((K : ℚ) + 1)) = K.factorial := by
    rw [hFq]; field_simp
  have hFq0 : (0 : ℚ) ≤ F := Nat.cast_nonneg _
  have h1 : s < n * F := by
    have : (s : ℚ) < n * F := by
      rw [hs]
      have := mul_lt_mul_of_pos_left hgK (show (0 : ℚ) < F by exact_mod_cast hFpos)
      linarith
    exact_mod_cast this
  have h2 : n * F ≤ s + K.factorial := by
    have : ((n * F : ℕ) : ℚ) ≤ ((s + K.factorial : ℕ) : ℚ) := by
      have := mul_le_mul_of_nonneg_left hN hFq0
      rw [g_succ K (by omega), mul_add, ← hs, hFK] at this
      push_cast
      linarith
    exact_mod_cast this
  have hr : n * F - 1 - s ≤ K.factorial := by omega
  obtain ⟨B, hBsub, -, hBsum⟩ := rep K (by omega) (n * F - 1 - s) hr
  have hB : ∀ e ∈ B, e ∣ F ∧ 0 < e ∧ K + 1 ≤ F / e ∧ F / (F / e) = e := by
    intro e he
    have hd := Nat.dvd_of_mem_divisors (hBsub he)
    have hpos := Nat.pos_of_mem_divisors (hBsub he)
    have hle : e ≤ K.factorial := Nat.divisor_le (hBsub he)
    have hdF : e ∣ F := hd.trans (Nat.factorial_dvd_factorial (Nat.le_succ K))
    refine ⟨hdF, hpos, ?_, Nat.div_div_self hdF hFpos.ne'⟩
    have h3 : F / K.factorial ≤ F / e := Nat.div_le_div_left hle hpos
    have h4 : F / K.factorial = K + 1 := by
      rw [hFdef, Nat.factorial_succ, Nat.mul_div_cancel _ hKpos]
    omega
  have hinj : Set.InjOn (fun e => F / e) B := by
    intro a ha b hb hab
    have := (hB a ha).2.2.2
    rw [← (hB a ha).2.2.2, ← (hB b hb).2.2.2]
    simp only at hab
    rw [hab]
  have hdisj : Disjoint (Finset.Icc 2 K) (B.image (fun e => F / e)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    have := (hB e he).2.2.1
    have := (Finset.mem_Icc.mp ha).2
    omega
  refine ⟨Finset.Icc 2 K ∪ B.image (fun e => F / e), F, ?_, ?_, ?_, hFpos, ?_, ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact h0K h
    · obtain ⟨e, he, he0⟩ := Finset.mem_image.mp h
      have := (hB e he).2.2.1
      omega
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · simp at h
    · obtain ⟨e, he, he0⟩ := Finset.mem_image.mp h
      have := (hB e he).2.2.1
      omega
  · intro a ha
    rcases Finset.mem_union.mp ha with h | h
    · exact hdK a h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      exact Nat.div_dvd_of_dvd (hB e he).1
  · rw [Finset.sum_union hdisj, Finset.sum_image hinj, ← hsdef]
    have : ∑ e ∈ B, F / (F / e) = ∑ e ∈ B, e :=
      Finset.sum_congr rfl fun e he => (hB e he).2.2.2
    rw [this, hBsum]
    omega

theorem erdos_316.variants.generalized (n : ℕ) (hn : 2 ≤ n) : ∃ A : Finset ℕ,
    A.Nonempty ∧ 0 ∉ A ∧ 1 ∉ A ∧ ∑ k ∈ A, (1 / k : ℚ) < n ∧ ∀ P : Finpartition A,
    P.parts.card ≤ n → ∃ p ∈ P.parts, 1 ≤ ∑ n ∈ p, (1 / n : ℚ) := by
  obtain ⟨A, L, h2, h0, h1, hL, hdvd, hsum⟩ := construct n hn
  refine ⟨A, ⟨2, h2⟩, h0, h1, ?_, fun P hP => no_split A L n hn hL hdvd h0 hsum P hP⟩
  have hc := castA A L hdvd h0
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have h7 : n ≤ n * L := Nat.le_mul_of_pos_right n hL
  have h8 : ∑ a ∈ A, L / a + 1 = n * L := by omega
  have h9 : ((∑ a ∈ A, L / a : ℕ) : ℚ) + 1 = n * L := by exact_mod_cast h8
  by_contra hge
  push Not at hge
  have := mul_le_mul_of_nonneg_left hge hLq.le
  rw [← hc] at this
  nlinarith

end Erdos316

#print axioms Erdos316.erdos_316.variants.generalized
