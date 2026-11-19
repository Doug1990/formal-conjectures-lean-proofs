import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.ZMod.Basic

open Finset

namespace LS

noncomputable def e (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_int (k : ℤ) : e k = 1 := by
  unfold e
  rw [show (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) = (k : ℂ) * (2 * Real.pi * Complex.I)
    by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1; push_cast; ring

lemma e_nat_mul (n : ℕ) (x : ℝ) : e (n * x) = e x ^ n := by
  induction n with
  | zero => simp [e]
  | succ n ih => rw [pow_succ, ← ih, ← e_add]; congr 1; push_cast; ring

lemma e_fract (x : ℝ) : e x = e (Int.fract x) := by
  conv_lhs => rw [← Int.fract_add_floor x]
  rw [e_add, e_int, mul_one]

lemma norm_e_sub_one (x : ℝ) : ‖e x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  unfold e
  rw [show (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) = Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)
    from mul_comm _ _, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_two]
  congr 3; ring

lemma sin_lb (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    2 * min f (1 - f) ≤ Real.sin (Real.pi * f) := by
  have hp := Real.pi_pos
  rcases le_total f (1 / 2) with h | h
  · have := Real.mul_le_sin (x := Real.pi * f) (by positivity) (by nlinarith)
    rw [← mul_assoc, div_mul_cancel₀ _ Real.pi_ne_zero] at this
    have := min_le_left f (1 - f)
    linarith
  · have := Real.mul_le_sin (x := Real.pi * (1 - f)) (by nlinarith) (by nlinarith)
    rw [← mul_assoc, div_mul_cancel₀ _ Real.pi_ne_zero,
      show Real.pi * (1 - f) = Real.pi - Real.pi * f by ring, Real.sin_pi_sub] at this
    have := min_le_right f (1 - f)
    linarith

lemma norm_e_sub_one_lb (x : ℝ) :
    4 * min (Int.fract x) (1 - Int.fract x) ≤ ‖e x - 1‖ := by
  rw [e_fract, norm_e_sub_one]
  have h := sin_lb (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le
  have := le_abs_self (Real.sin (Real.pi * Int.fract x))
  linarith

noncomputable def D (K : ℕ) (x : ℝ) : ℂ := ∑ k ∈ range K, e (k * x)

lemma D_mul (K : ℕ) (x : ℝ) : D K x * (e x - 1) = e x ^ K - 1 := by
  unfold D; simp_rw [e_nat_mul]; exact geom_sum_mul _ _

lemma D_le_card (K : ℕ) (x : ℝ) : ‖D K x‖ ≤ K := by
  unfold D
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

lemma D_bound (K : ℕ) (x : ℝ) (h : 0 < ‖e x - 1‖) : ‖D K x‖ ≤ 2 / ‖e x - 1‖ := by
  rw [le_div_iff₀ h, ← norm_mul, D_mul]
  calc ‖e x ^ K - 1‖ ≤ ‖e x ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, norm_e]; norm_num

lemma D_neg (K : ℕ) (x : ℝ) : ‖D K (-x)‖ = ‖D K x‖ := by
  have : D K (-x) = (starRingEnd ℂ) (D K x) := by
    unfold D; rw [map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← e_neg]; congr 1; ring
  rw [this, Complex.norm_conj]

/-- Kernel bound away from integers. -/
lemma DD_bound (A B : ℕ) (x : ℝ) (h0 : 0 < Int.fract x) :
    ‖D A x‖ * ‖D B x‖ ≤ (1 / (Int.fract x) ^ 2 + 1 / (1 - Int.fract x) ^ 2) / 4 := by
  set f := Int.fract x with hf
  have h1 : 0 < 1 - f := by have := Int.fract_lt_one x; linarith
  set m := min f (1 - f) with hm
  have hm0 : 0 < m := lt_min h0 h1
  have hlb := norm_e_sub_one_lb x
  rw [← hf, ← hm] at hlb
  have hpos : 0 < ‖e x - 1‖ := by linarith
  have hA := D_bound A x hpos
  have hB := D_bound B x hpos
  have h2 : 2 / ‖e x - 1‖ ≤ 1 / (2 * m) := by
    rw [div_le_div_iff₀ hpos (by positivity)]; linarith
  have hprod : ‖D A x‖ * ‖D B x‖ ≤ (1 / (2 * m)) * (1 / (2 * m)) :=
    mul_le_mul (hA.trans h2) (hB.trans h2) (norm_nonneg _) (by positivity)
  have hmm : 1 / m ^ 2 ≤ 1 / f ^ 2 + 1 / (1 - f) ^ 2 := by
    rcases min_choice f (1 - f) with h | h
    · rw [← hm] at h; rw [h]; have : 0 ≤ 1 / (1 - f) ^ 2 := by positivity
      linarith
    · rw [← hm] at h; rw [h]; have : 0 ≤ 1 / f ^ 2 := by positivity
      linarith
  calc ‖D A x‖ * ‖D B x‖ ≤ (1 / (2 * m)) * (1 / (2 * m)) := hprod
    _ = (1 / m ^ 2) / 4 := by field_simp; ring
    _ ≤ _ := by linarith

lemma inv_sq_sum (K : ℕ) : ∑ k ∈ range K, 1 / ((k : ℝ) + 1) ^ 2 ≤ 2 - 2 / ((K : ℝ) + 1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [sum_range_succ]
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have : 1 / ((K : ℝ) + 1) ^ 2 ≤ 2 / ((K : ℝ) + 1) - 2 / (((K + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- Spacing sum: points `≥ δ`, pairwise `δ`-separated. -/
lemma spacing (G : Finset ℝ) (δ : ℝ) (hδ : 0 < δ) (hlo : ∀ f ∈ G, δ ≤ f)
    (hsep : ∀ f ∈ G, ∀ g ∈ G, f < g → δ ≤ g - f) :
    ∑ f ∈ G, 1 / f ^ 2 ≤ 2 / δ ^ 2 := by
  let φ : ℝ → ℕ := fun f => ⌊f / δ⌋₊ - 1
  have hφ1 : ∀ f ∈ G, 1 ≤ ⌊f / δ⌋₊ := fun f hf =>
    Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ]; linarith [hlo f hf])
  have hφle : ∀ f ∈ G, ((φ f : ℕ) + 1 : ℝ) * δ ≤ f := by
    intro f hf
    have h1 := hφ1 f hf
    have : ((φ f : ℕ) : ℝ) + 1 = (⌊f / δ⌋₊ : ℝ) := by
      simp only [φ]; rw [Nat.cast_sub h1]; ring
    rw [this]
    have := Nat.floor_le (div_nonneg (hδ.le.trans (hlo f hf)) hδ.le)
    rwa [le_div_iff₀ hδ] at this
  have hlt : ∀ f ∈ G, ∀ g ∈ G, f < g → φ f < φ g := by
    intro f hf g hg hfg
    have h1 := hφ1 f hf
    have hgf : f / δ + 1 ≤ g / δ := by
      rw [div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]; linarith [hsep f hf g hg hfg]
    have := Nat.floor_le_floor hgf
    rw [Nat.floor_add_one (div_nonneg (hδ.le.trans (hlo f hf)) hδ.le)] at this
    simp only [φ]; omega
  have hinj : Set.InjOn φ G := by
    intro f hf g hg hfg
    rcases lt_trichotomy f g with h | h | h
    · exact absurd hfg (hlt f hf g hg h).ne
    · exact h
    · exact absurd hfg (hlt g hg f hf h).ne'
  obtain ⟨M, hM⟩ : ∃ M, ∀ f ∈ G, φ f < M :=
    ⟨(G.image φ).sup id + 1, fun f hf => Nat.lt_succ_of_le
      (le_sup (f := id) (mem_image_of_mem φ hf))⟩
  calc ∑ f ∈ G, 1 / f ^ 2 ≤ ∑ f ∈ G, (1 / δ ^ 2) * (1 / (((φ f : ℕ) : ℝ) + 1) ^ 2) := by
        refine sum_le_sum fun f hf => ?_
        have h := hφle f hf
        have hp : 0 < ((φ f : ℝ) + 1) * δ := by positivity
        calc 1 / f ^ 2 ≤ 1 / (((φ f : ℝ) + 1) * δ) ^ 2 :=
              one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp.le h 2)
          _ = _ := by rw [mul_pow, one_div_mul_one_div, mul_comm (δ ^ 2)]
    _ = (1 / δ ^ 2) * ∑ k ∈ G.image φ, 1 / ((k : ℝ) + 1) ^ 2 := by
        rw [sum_image hinj, mul_sum]
    _ ≤ (1 / δ ^ 2) * ∑ k ∈ range M, 1 / ((k : ℝ) + 1) ^ 2 := by
        gcongr
        intro k hk
        obtain ⟨f, hf, rfl⟩ := mem_image.1 hk
        exact mem_range.2 (hM f hf)
    _ ≤ (1 / δ ^ 2) * 2 := by
        gcongr
        have := inv_sq_sum M
        have : 0 ≤ 2 / ((M : ℝ) + 1) := by positivity
        linarith
    _ = 2 / δ ^ 2 := by ring

/-! ## Duality -/

noncomputable def Sf (S : Finset ℕ) (x : ℝ) : ℂ := ∑ n ∈ S, e (n * x)

noncomputable def Bf (F : Finset ℝ) (c : ℝ → ℂ) (m : ℤ) : ℂ := ∑ r ∈ F, c r * e (m * r)

lemma stepA (S : Finset ℕ) (N L : ℕ) (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N) (g : ℤ → ℝ)
    (hg : ∀ m, 0 ≤ g m) :
    (L : ℝ) * ∑ n ∈ S, g n ≤ ∑ j ∈ range L, ∑ k ∈ range (N + L), g ((k : ℤ) - j + 1) := by
  have h : ∀ j ∈ range L, ∑ n ∈ S, g n ≤ ∑ k ∈ range (N + L), g ((k : ℤ) - j + 1) := by
    intro j hj
    have hj' := mem_range.1 hj
    have hinj : Set.InjOn (fun n : ℕ => n - 1 + j) S := by
      intro a ha b hb hab
      have := (hS a ha).1; have := (hS b hb).1
      simp only at hab; omega
    calc ∑ n ∈ S, g n = ∑ k ∈ S.image (fun n : ℕ => n - 1 + j), g ((k : ℤ) - j + 1) := by
          rw [sum_image hinj]
          refine sum_congr rfl fun n hn => ?_
          have h1 := (hS n hn).1
          congr 1
          rw [Nat.cast_add, Nat.cast_sub h1]; push_cast; ring
      _ ≤ _ := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro k hk
            obtain ⟨n, hn, rfl⟩ := mem_image.1 hk
            have := (hS n hn).2
            exact mem_range.2 (by omega)
          · intro _ _ _; exact hg _
  calc (L : ℝ) * ∑ n ∈ S, g n = ∑ j ∈ range L, ∑ n ∈ S, g n := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum h

lemma normsq_eq (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma B_conj (F : Finset ℝ) (c : ℝ → ℂ) (m : ℤ) :
    Bf F c m * (starRingEnd ℂ) (Bf F c m) =
      ∑ r ∈ F, ∑ s ∈ F, c r * (starRingEnd ℂ) (c s) * e (m * (r - s)) := by
  unfold Bf
  rw [map_sum, sum_mul_sum]
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  rw [map_mul, ← e_neg, show (m : ℝ) * (r - s) = m * r + -(m * s) by ring, e_add]
  ring

lemma ker_norm (A B : ℕ) (β : ℝ) :
    ‖∑ j ∈ range A, ∑ k ∈ range B, e ((((k : ℤ) - j + 1 : ℤ) : ℝ) * β)‖ ≤
      ‖D B β‖ * ‖D A β‖ := by
  have : ∑ j ∈ range A, ∑ k ∈ range B, e ((((k : ℤ) - j + 1 : ℤ) : ℝ) * β) =
      e β * ((∑ j ∈ range A, e (j * (-β))) * D B β) := by
    unfold D
    rw [sum_mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← e_add, ← e_add]; congr 1; push_cast; ring
  rw [this, norm_mul, norm_e, one_mul, norm_mul, mul_comm]
  have h2 : ‖∑ j ∈ range A, e (j * (-β))‖ = ‖D A β‖ := D_neg A β
  rw [h2]

lemma stepB (F : Finset ℝ) (c : ℝ → ℂ) (A B : ℕ) :
    ∑ j ∈ range A, ∑ k ∈ range B, ‖Bf F c ((k : ℤ) - j + 1)‖ ^ 2 ≤
      ∑ r ∈ F, ∑ s ∈ F, ‖c r‖ * ‖c s‖ * (‖D B (r - s)‖ * ‖D A (r - s)‖) := by
  have hre : ∑ j ∈ range A, ∑ k ∈ range B, ‖Bf F c ((k : ℤ) - j + 1)‖ ^ 2 =
      (∑ j ∈ range A, ∑ k ∈ range B, Bf F c ((k : ℤ) - j + 1) *
        (starRingEnd ℂ) (Bf F c ((k : ℤ) - j + 1))).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [Complex.re_sum]
    exact sum_congr rfl fun k _ => normsq_eq _
  have hswap : ∑ j ∈ range A, ∑ k ∈ range B, Bf F c ((k : ℤ) - j + 1) *
        (starRingEnd ℂ) (Bf F c ((k : ℤ) - j + 1)) =
      ∑ r ∈ F, ∑ s ∈ F, c r * (starRingEnd ℂ) (c s) *
        ∑ j ∈ range A, ∑ k ∈ range B, e ((((k : ℤ) - j + 1 : ℤ) : ℝ) * (r - s)) := by
    simp_rw [B_conj, mul_sum]
    calc _ = ∑ j ∈ range A, ∑ r ∈ F, ∑ k ∈ range B, ∑ s ∈ F,
          c r * (starRingEnd ℂ) (c s) * e ((((k : ℤ) - j + 1 : ℤ) : ℝ) * (r - s)) :=
          sum_congr rfl fun j _ => sum_comm
      _ = ∑ r ∈ F, ∑ j ∈ range A, ∑ k ∈ range B, ∑ s ∈ F,
          c r * (starRingEnd ℂ) (c s) * e ((((k : ℤ) - j + 1 : ℤ) : ℝ) * (r - s)) := sum_comm
      _ = ∑ r ∈ F, ∑ j ∈ range A, ∑ s ∈ F, ∑ k ∈ range B,
          c r * (starRingEnd ℂ) (c s) * e ((((k : ℤ) - j + 1 : ℤ) : ℝ) * (r - s)) :=
          sum_congr rfl fun r _ => sum_congr rfl fun j _ => sum_comm
      _ = _ := sum_congr rfl fun r _ => sum_comm
  rw [hre, hswap]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (sum_le_sum fun r _ =>
    (norm_sum_le _ _).trans (sum_le_sum fun s _ => ?_)))
  rw [norm_mul, norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (ker_norm A B (r - s)) (by positivity)

lemma stepC (F : Finset ℝ) (a : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (M : ℝ)
    (hK : ∀ r s, K r s = K s r) (hM : ∀ r ∈ F, ∑ s ∈ F, K r s ≤ M) (hK0 : ∀ r s, 0 ≤ K r s) :
    ∑ r ∈ F, ∑ s ∈ F, a r * a s * K r s ≤ M * ∑ r ∈ F, a r ^ 2 := by
  have h1 : ∀ r s, a r * a s * K r s ≤ (a r ^ 2 * K r s + a s ^ 2 * K s r) / 2 := by
    intro r s
    rw [← hK r s]
    have := hK0 r s
    nlinarith [sq_nonneg (a r - a s), mul_nonneg this (sq_nonneg (a r - a s))]
  have h2 : ∑ r ∈ F, ∑ s ∈ F, a s ^ 2 * K s r = ∑ r ∈ F, ∑ s ∈ F, a r ^ 2 * K r s := sum_comm
  have h3 : ∑ r ∈ F, ∑ s ∈ F, a r ^ 2 * K r s ≤ M * ∑ r ∈ F, a r ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun r hr => ?_
    rw [← mul_sum, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM r hr) (sq_nonneg _)
  calc _ ≤ ∑ r ∈ F, ∑ s ∈ F, (a r ^ 2 * K r s + a s ^ 2 * K s r) / 2 :=
        sum_le_sum fun r _ => sum_le_sum fun s _ => h1 r s
    _ = ((∑ r ∈ F, ∑ s ∈ F, a r ^ 2 * K r s) + ∑ r ∈ F, ∑ s ∈ F, a s ^ 2 * K s r) / 2 := by
        simp only [← sum_add_distrib, div_eq_mul_inv, ← sum_mul]
    _ ≤ _ := by rw [h2]; linarith

/-- Duality: `L · Σ_F |S(α)|² ≤ |S| · M`. -/
lemma duality (S : Finset ℕ) (F : Finset ℝ) (N L : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (hM : ∀ r ∈ F, ∑ s ∈ F, ‖D (N + L) (r - s)‖ * ‖D L (r - s)‖ ≤ M) :
    (L : ℝ) * ∑ r ∈ F, ‖Sf S r‖ ^ 2 ≤ S.card * M := by
  set T := ∑ r ∈ F, ‖Sf S r‖ ^ 2 with hT
  set c : ℝ → ℂ := fun r => (starRingEnd ℂ) (Sf S r) with hc
  have hT0 : 0 ≤ T := sum_nonneg fun _ _ => sq_nonneg _
  have hsum : ((T : ℝ) : ℂ) = ∑ n ∈ S, Bf F c n := by
    rw [hT, Complex.ofReal_sum]
    unfold Bf
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_sum]
    simp only [hc, Int.cast_natCast]
    rw [mul_comm, ← Sf, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hTle : T ≤ ∑ n ∈ S, ‖Bf F c n‖ := by
    have : T = (∑ n ∈ S, Bf F c n).re := by rw [← hsum, Complex.ofReal_re]
    rw [this]
    exact (Complex.re_le_norm _).trans (norm_sum_le _ _)
  have hcs : T ^ 2 ≤ S.card * ∑ n ∈ S, ‖Bf F c n‖ ^ 2 :=
    (pow_le_pow_left₀ hT0 hTle 2).trans sq_sum_le_card_mul_sum_sq
  have hA := stepA S N L hS (fun m => ‖Bf F c m‖ ^ 2) (fun _ => sq_nonneg _)
  have hB := stepB F c L (N + L)
  have hC := stepC F (fun r => ‖c r‖) (fun r s => ‖D (N + L) (r - s)‖ * ‖D L (r - s)‖) M
    (fun r s => by
      rw [show s - r = -(r - s) by ring, D_neg, D_neg])
    hM (fun _ _ => by positivity)
  have hcT : ∑ r ∈ F, ‖c r‖ ^ 2 = T := by
    rw [hT]; refine sum_congr rfl fun r _ => ?_; simp only [hc, Complex.norm_conj]
  rw [hcT] at hC
  have hchain : (L : ℝ) * ∑ n ∈ S, ‖Bf F c n‖ ^ 2 ≤ M * T := by
    refine hA.trans (le_trans ?_ (hB.trans ?_))
    · exact le_of_eq rfl
    · simpa only [mul_assoc] using hC
  rcases hT0.lt_or_eq with hpos | hzero
  · have hcard : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have h1 : (L : ℝ) * T ^ 2 ≤ S.card * (M * T) := by
      calc (L : ℝ) * T ^ 2 ≤ L * (S.card * ∑ n ∈ S, ‖Bf F c n‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg _)
        _ = S.card * (L * ∑ n ∈ S, ‖Bf F c n‖ ^ 2) := by ring
        _ ≤ S.card * (M * T) := mul_le_mul_of_nonneg_left hchain hcard
    have h2 : (L : ℝ) * T * T ≤ S.card * M * T := by nlinarith
    exact le_of_mul_le_mul_right h2 hpos
  · rw [← hzero, mul_zero]
    positivity

/-! ## Montgomery's lemma for one prime -/

lemma e_eq_one (x : ℝ) (h : e x = 1) : ∃ k : ℤ, x = k := by
  unfold e at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨k, ?_⟩
  have h1 : (((2 * Real.pi * x : ℝ) : ℂ)) * Complex.I =
      (((2 * Real.pi * k : ℝ) : ℂ)) * Complex.I := by
    rw [hk]; push_cast; ring
  have h2 := Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h1)
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  exact mul_left_cancel₀ hp h2

lemma orth (p : ℕ) (hp : 0 < p) (m : ℤ) :
    ∑ a ∈ range p, e (a * (m / p)) = if (p : ℤ) ∣ m then (p : ℂ) else 0 := by
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  have hgeom : ∑ a ∈ range p, e (a * (m / p)) = ∑ a ∈ range p, e (m / p) ^ a := by
    simp_rw [e_nat_mul]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    have : e ((((p : ℤ) * q : ℤ) : ℝ) / p) = 1 := by
      rw [show ((((p : ℤ) * q : ℤ) : ℝ) / p) = ((q : ℤ) : ℝ) by push_cast; field_simp]
      exact e_int q
    rw [hgeom, this]; simp
  · have hne : e (m / p) ≠ 1 := by
      intro h1
      obtain ⟨k, hk⟩ := e_eq_one _ h1
      apply h; refine ⟨k, ?_⟩
      rw [div_eq_iff hp'] at hk
      have : (m : ℝ) = p * k := by linarith
      exact_mod_cast this
    have hpow : e (m / p) ^ p = 1 := by
      rw [← e_nat_mul, show (p : ℝ) * (m / p) = ((m : ℤ) : ℝ) by field_simp]; exact e_int m
    rw [hgeom]
    have := geom_sum_mul (e (m / p)) p
    rw [hpow, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)

lemma normsq_c (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma mont (p : ℕ) [NeZero p] (A : Finset (ZMod p)) (S : Finset ℕ)
    (hS : ∀ n ∈ S, (n : ZMod p) ∉ A) (hA : A.card < p) :
    (p : ℝ) * S.card ^ 2 ≤ (p - A.card) * ∑ a ∈ range p, ‖Sf S (a / p)‖ ^ 2 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  set Q : ℝ := ∑ n ∈ S, ∑ n' ∈ S, (if (p : ℤ) ∣ ((n : ℤ) - n') then (1 : ℝ) else 0) with hQ
  have hexp : ∀ x : ℝ, Sf S x * (starRingEnd ℂ) (Sf S x) =
      ∑ n ∈ S, ∑ n' ∈ S, e ((((n : ℤ) - n' : ℤ) : ℝ) * x) := by
    intro x; unfold Sf; rw [map_sum, sum_mul_sum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun n' _ => ?_
    rw [← e_neg, ← e_add]; congr 1; push_cast; ring
  have h1 : ∑ a ∈ range p, ‖Sf S (a / p)‖ ^ 2 = p * Q := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum]
    simp_rw [normsq_c, hexp]
    rw [sum_comm]
    have : ∀ n ∈ S, ∑ a ∈ range p, ∑ n' ∈ S, e ((((n : ℤ) - n' : ℤ) : ℝ) * ((a : ℝ) / p)) =
        ∑ n' ∈ S, (if (p : ℤ) ∣ ((n : ℤ) - n') then (p : ℂ) else 0) := by
      intro n _
      rw [sum_comm]
      refine sum_congr rfl fun n' _ => ?_
      rw [← orth p hp]
      refine sum_congr rfl fun a _ => ?_
      congr 1; ring
    rw [sum_congr rfl this, hQ]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun n' _ => ?_
    split_ifs <;> simp
  -- Cauchy–Schwarz over the residue classes
  let κ : ℕ → ZMod p := fun n => (n : ZMod p)
  let t : Finset (ZMod p) := univ \ A
  let c : ZMod p → ℕ := fun h => (S.filter (fun n => κ n = h)).card
  have hmaps : ∀ n ∈ S, κ n ∈ t := fun n hn => mem_sdiff.2 ⟨mem_univ _, hS n hn⟩
  have hcard : S.card = ∑ h ∈ t, c h := card_eq_sum_card_fiberwise hmaps
  have hQ2 : Q = ∑ h ∈ t, (c h : ℝ) ^ 2 := by
    have hdv : ∀ n n' : ℕ, ((p : ℤ) ∣ ((n : ℤ) - n')) ↔ κ n' = κ n := by
      intro n n'
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simp [κ]
    have : Q = ∑ n ∈ S, (c (κ n) : ℝ) := by
      rw [hQ]
      refine sum_congr rfl fun n _ => ?_
      simp_rw [hdv]
      rw [sum_boole]
    rw [this, ← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun h _ => ?_
    rw [sum_congr rfl (fun n hn => by rw [(mem_filter.1 hn).2]), sum_const, nsmul_eq_mul, sq]
  have htc : t.card = p - A.card := by
    rw [card_univ_sdiff, ZMod.card]
  have hcs : ((S.card : ℕ) : ℝ) ^ 2 ≤ t.card * ∑ h ∈ t, (c h : ℝ) ^ 2 := by
    rw [hcard]; push_cast
    exact sq_sum_le_card_mul_sum_sq
  rw [htc, Nat.cast_sub hA.le, ← hQ2] at hcs
  rw [h1]
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  nlinarith

/-! ## Spacing of the frequencies and the kernel sum -/

lemma spacing' (I : Finset ℝ) (g : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hlo : ∀ s ∈ I, δ ≤ g s)
    (hsep : ∀ s ∈ I, ∀ t ∈ I, s ≠ t → δ ≤ |g s - g t|) :
    ∑ s ∈ I, 1 / (g s) ^ 2 ≤ 2 / δ ^ 2 := by
  have hinj : Set.InjOn g I := by
    intro s hs t ht hst
    by_contra hne
    have := hsep s hs t ht hne
    rw [hst, sub_self, abs_zero] at this; linarith
  rw [← sum_image (f := fun f => 1 / f ^ 2) hinj]
  apply spacing _ δ hδ
  · intro f hf; obtain ⟨s, hs, rfl⟩ := mem_image.1 hf; exact hlo s hs
  · intro f hf f' hf' hlt
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hf
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hf'
    have hne : s ≠ t := by rintro rfl; exact lt_irrefl _ hlt
    have := hsep s hs t ht hne
    rw [abs_sub_comm, abs_of_pos (by linarith)] at this
    exact this

lemma sep_of_fract (x y δ : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (h1 : δ ≤ Int.fract (x - y)) (h2 : Int.fract (x - y) ≤ 1 - δ) : δ ≤ |x - y| := by
  rcases le_or_gt y x with h | h
  · rw [Int.fract_eq_self.2 ⟨by linarith, by linarith⟩] at h1
    rw [abs_of_nonneg (by linarith)]; exact h1
  · have : Int.fract (x - y) = x - y + 1 := by
      rw [← Int.fract_add_one, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    rw [this] at h2
    rw [abs_of_neg (by linarith)]; linarith

lemma fract_diff (r s t : ℝ) :
    Int.fract (Int.fract (r - s) - Int.fract (r - t)) = Int.fract (t - s) := by
  have : Int.fract (r - s) - Int.fract (r - t) = (t - s) + ((⌊r - t⌋ - ⌊r - s⌋ : ℤ) : ℝ) := by
    unfold Int.fract; push_cast; ring
  rw [this, Int.fract_eq_fract]
  exact ⟨⌊r - t⌋ - ⌊r - s⌋, by ring⟩

lemma kernel_sum (F : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsp : ∀ r ∈ F, ∀ s ∈ F, r ≠ s → δ ≤ Int.fract (r - s) ∧ Int.fract (r - s) ≤ 1 - δ)
    (A B : ℕ) (r : ℝ) (hr : r ∈ F) :
    ∑ s ∈ F, ‖D A (r - s)‖ * ‖D B (r - s)‖ ≤ A * B + 1 / δ ^ 2 := by
  rw [← add_sum_erase _ _ hr]
  have h0 : ‖D A (r - r)‖ * ‖D B (r - r)‖ ≤ A * B :=
    mul_le_mul (D_le_card _ _) (D_le_card _ _) (norm_nonneg _) (Nat.cast_nonneg _)
  set f : ℝ → ℝ := fun s => Int.fract (r - s) with hf
  have hmem : ∀ s ∈ F.erase r, s ∈ F ∧ r ≠ s := fun s hs =>
    ⟨(mem_erase.1 hs).2, fun h => (mem_erase.1 hs).1 h.symm⟩
  have hsepf : ∀ s ∈ F.erase r, ∀ t ∈ F.erase r, s ≠ t → δ ≤ |f s - f t| := by
    intro s hs t ht hst
    have h := hsp t (hmem t ht).1 s (hmem s hs).1 (Ne.symm hst)
    rw [← fract_diff r s t] at h
    exact sep_of_fract _ _ δ (Int.fract_nonneg _) (Int.fract_lt_one _) (Int.fract_nonneg _)
      (Int.fract_lt_one _) h.1 h.2
  have hS1 : ∑ s ∈ F.erase r, 1 / (f s) ^ 2 ≤ 2 / δ ^ 2 :=
    spacing' _ f δ hδ (fun s hs => (hsp r hr s (hmem s hs).1 (hmem s hs).2).1) hsepf
  have hS2 : ∑ s ∈ F.erase r, 1 / ((fun s => 1 - f s) s) ^ 2 ≤ 2 / δ ^ 2 := by
    apply spacing' _ (fun s => 1 - f s) δ hδ
    · intro s hs; have := (hsp r hr s (hmem s hs).1 (hmem s hs).2).2
      simp only [hf]; linarith
    · intro s hs t ht hst
      have := hsepf s hs t ht hst
      rw [abs_sub_comm] at this
      show δ ≤ |(1 - f s) - (1 - f t)|
      rw [show 1 - f s - (1 - f t) = f t - f s by ring]; exact this
  have hrest : ∑ s ∈ F.erase r, ‖D A (r - s)‖ * ‖D B (r - s)‖ ≤ 1 / δ ^ 2 := by
    calc ∑ s ∈ F.erase r, ‖D A (r - s)‖ * ‖D B (r - s)‖
        ≤ ∑ s ∈ F.erase r, (1 / (f s) ^ 2 + 1 / (1 - f s) ^ 2) / 4 := by
          refine sum_le_sum fun s hs => DD_bound A B (r - s) ?_
          have := (hsp r hr s (hmem s hs).1 (hmem s hs).2).1
          linarith
      _ = ((∑ s ∈ F.erase r, 1 / (f s) ^ 2) +
            ∑ s ∈ F.erase r, 1 / ((fun s => 1 - f s) s) ^ 2) / 4 := by
          simp only [← sum_add_distrib, div_eq_mul_inv, ← sum_mul]
      _ ≤ (2 / δ ^ 2 + 2 / δ ^ 2) / 4 := by gcongr
      _ = 1 / δ ^ 2 := by ring
  linarith

lemma frac_sp (Q : ℕ) (a P b P' : ℕ) (hP : 1 ≤ P) (hP' : 1 ≤ P')
    (hPQ : P ≤ Q) (hP'Q : P' ≤ Q) (ha : a < P) (hb : b < P') (hne : (a : ℝ) / P ≠ b / P') :
    1 / (Q : ℝ) ^ 2 ≤ Int.fract ((a : ℝ) / P - b / P') ∧
      Int.fract ((a : ℝ) / P - b / P') ≤ 1 - 1 / (Q : ℝ) ^ 2 := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hP'r : (0 : ℝ) < P' := by exact_mod_cast hP'
  set m : ℤ := a * P' - b * P with hm
  set D : ℕ := P * P' with hD
  have hDr : (0 : ℝ) < D := by rw [hD]; push_cast; positivity
  have hx : (a : ℝ) / P - b / P' = m / D := by
    rw [hm, hD]; push_cast; field_simp
  have hm0 : m ≠ 0 := by
    intro h0; apply hne
    have : ((a : ℝ) / P - b / P') = 0 := by rw [hx, h0]; simp
    linarith
  have h1 : (a : ℤ) * P' < P * P' := by
    have := Nat.mul_lt_mul_of_pos_right ha (by omega : 0 < P'); exact_mod_cast this
  have h2 : (b : ℤ) * P < P * P' := by
    have := Nat.mul_lt_mul_of_pos_right hb (by omega : 0 < P)
    rw [mul_comm P' P] at this; exact_mod_cast this
  have hmlo : -((D : ℤ)) < m := by rw [hm, hD]; push_cast; nlinarith
  have hmhi : m < (D : ℤ) := by rw [hm, hD]; push_cast; nlinarith
  have hDQ : (D : ℝ) ≤ (Q : ℝ) ^ 2 := by
    rw [hD]; push_cast
    have : (P : ℝ) ≤ Q := by exact_mod_cast hPQ
    have : (P' : ℝ) ≤ Q := by exact_mod_cast hP'Q
    nlinarith
  have hinv : 1 / (Q : ℝ) ^ 2 ≤ 1 / D := one_div_le_one_div_of_le hDr hDQ
  rw [hx]
  rcases lt_or_gt_of_ne hm0 with hneg | hpos
  · have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    have hm2 : -(D : ℝ) + 1 ≤ m := by exact_mod_cast (show -(D : ℤ) + 1 ≤ m by omega)
    have hfr : Int.fract ((m : ℝ) / D) = m / D + 1 := by
      rw [← Int.fract_add_one, Int.fract_eq_self.2 ⟨?_, ?_⟩]
      · rw [div_add_one hDr.ne', le_div_iff₀ hDr]; linarith
      · rw [div_add_one hDr.ne', div_lt_one hDr]; linarith
    rw [hfr]
    constructor
    · have : 1 / (D : ℝ) ≤ m / D + 1 := by
        rw [div_add_one hDr.ne', div_le_div_iff_of_pos_right hDr]; linarith
      linarith
    · have : (m : ℝ) / D + 1 ≤ 1 - 1 / D := by
        have : (m : ℝ) / D ≤ -1 / D := div_le_div_of_nonneg_right hm1 hDr.le
        rw [neg_div] at this; linarith
      linarith
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hm2 : (m : ℝ) ≤ D - 1 := by exact_mod_cast (show m ≤ (D : ℤ) - 1 by omega)
    have hfr : Int.fract ((m : ℝ) / D) = m / D := by
      rw [Int.fract_eq_self.2 ⟨by positivity, by rw [div_lt_one hDr]; linarith⟩]
    rw [hfr]
    constructor
    · have : 1 / (D : ℝ) ≤ m / D := div_le_div_of_nonneg_right hm1 hDr.le
      linarith
    · have : (m : ℝ) / D ≤ 1 - 1 / D := by
        rw [one_sub_div hDr.ne']; exact div_le_div_of_nonneg_right hm2 hDr.le
      linarith

end LS

namespace Green44

open LS

set_option maxRecDepth 200000 in
theorem green_44.variants.less_than_sqrt :
    ∀ (N : ℕ) (p : Fin 1000 → ℕ) (A : (i : Fin 1000) → Finset (ZMod (p i))),
      let remaining := (Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i)
      (∀ i, (p i).Prime) →
      StrictMono p →
      (p 999) ^ 2 < N →
      (∀ i, (A i).card = (p i) / 2) →
      10 * remaining.card ≤ N := by
  intro N p A S hp hmono hN hA
  have hSall : ∀ n ∈ S, (1 ≤ n ∧ n ≤ N) ∧ ∀ i, (n : ZMod (p i)) ∉ A i := fun n hn => by
    have := Finset.mem_filter.1 hn; exact ⟨Finset.mem_Icc.1 this.1, this.2⟩
  clear_value S
  set Q := p 999 with hQ
  have hle : ∀ i, p i ≤ Q := fun i =>
    hmono.monotone (show i ≤ (999 : Fin 1000) from Fin.le_last i)
  have hp2 : ∀ i, 2 ≤ p i := fun i => (hp i).two_le
  have hQ1 : 1 ≤ Q := by have := hp2 999; omega
  set L : ℕ := Q ^ 2 with hL
  have hLpos : (0 : ℝ) < L := by rw [hL]; push_cast; positivity
  have hSmem : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N := fun n hn => (hSall n hn).1
  -- the frequencies
  obtain ⟨G, hG⟩ : ∃ G : Fin 1000 → Finset ℝ,
      G = fun i => (Finset.Ico 1 (p i)).image (fun a : ℕ => (a : ℝ) / p i) := ⟨_, rfl⟩
  have hGi : ∀ i, G i = (Finset.Ico 1 (p i)).image (fun a : ℕ => (a : ℝ) / p i) := by
    intro i; rw [hG]
  obtain ⟨F, hF⟩ : ∃ F : Finset ℝ, F = insert 0 (Finset.univ.biUnion G) := ⟨_, rfl⟩
  -- every frequency is a/P with a < P ≤ Q
  have hrep : ∀ r ∈ F, ∃ a P : ℕ, 1 ≤ P ∧ P ≤ Q ∧ a < P ∧ r = (a : ℝ) / P := by
    intro r hr
    rw [hF] at hr
    rcases Finset.mem_insert.1 hr with h | hr
    · exact ⟨0, 1, le_rfl, hQ1, one_pos, by rw [h]; simp⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hr
      rw [hGi] at hi
      obtain ⟨a, ha, hra⟩ := Finset.mem_image.1 hi
      exact ⟨a, p i, by have := hp2 i; omega, hle i, (Finset.mem_Ico.1 ha).2, hra.symm⟩
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hsp : ∀ r ∈ F, ∀ s ∈ F, r ≠ s →
      1 / (Q : ℝ) ^ 2 ≤ Int.fract (r - s) ∧ Int.fract (r - s) ≤ 1 - 1 / (Q : ℝ) ^ 2 := by
    intro r hr s hs hrs
    obtain ⟨a, P, hP, hPQ, ha, hra⟩ := hrep r hr
    obtain ⟨b, P', hP', hP'Q, hb, hsb⟩ := hrep s hs
    rw [hra, hsb] at hrs ⊢
    exact frac_sp Q a P b P' hP hP' hPQ hP'Q ha hb hrs
  have hM : ∀ r ∈ F, ∑ s ∈ F, ‖D (N + L) (r - s)‖ * ‖D L (r - s)‖ ≤
      ((N + L : ℕ) : ℝ) * L + (L : ℝ) ^ 2 := by
    intro r hr
    have := kernel_sum F _ hδ hsp (N + L) L r hr
    have hL2 : 1 / (1 / (Q : ℝ) ^ 2) ^ 2 = (L : ℝ) ^ 2 := by rw [hL]; push_cast; field_simp
    rw [hL2] at this; exact this
  have hdual := duality S F N L _ (by positivity) hSmem hM
  -- lower bound
  have hS0 : ‖Sf S 0‖ ^ 2 = (S.card : ℝ) ^ 2 := by
    simp [Sf, e_zero]
  have hY : ∀ i, (S.card : ℝ) ^ 2 ≤ 2 * ∑ a ∈ Finset.Ico 1 (p i), ‖Sf S (a / p i)‖ ^ 2 := by
    intro i
    have : NeZero (p i) := ⟨(hp i).ne_zero⟩
    have hSA : ∀ n ∈ S, (n : ZMod (p i)) ∉ A i := fun n hn => (hSall n hn).2 i
    have hAc : (A i).card < p i := by rw [hA i]; have := hp2 i; omega
    have hm := mont (p i) (A i) S hSA hAc
    have hsplit : ∑ a ∈ Finset.range (p i), ‖Sf S (a / p i)‖ ^ 2 =
        ‖Sf S 0‖ ^ 2 + ∑ a ∈ Finset.Ico 1 (p i), ‖Sf S (a / p i)‖ ^ 2 := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by have := hp2 i; omega)]
      simp
    rw [hsplit, hS0] at hm
    set Y := ∑ a ∈ Finset.Ico 1 (p i), ‖Sf S (a / p i)‖ ^ 2
    have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hω : ((p i / 2 : ℕ) : ℝ) * 3 ≥ p i := by
      have : p i ≤ 3 * (p i / 2) := by have := hp2 i; omega
      exact_mod_cast (by omega : p i ≤ p i / 2 * 3)
    have hω1 : (1 : ℝ) ≤ ((p i / 2 : ℕ) : ℝ) := by
      exact_mod_cast (by have := hp2 i; omega : 1 ≤ p i / 2)
    rw [hA i] at hm
    have hc0 : (0 : ℝ) ≤ (S.card : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 1000))) G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.2 fun x hxi hxj => ?_
    rw [hGi] at hxi hxj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hxi
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 hxj
    have ha' := Finset.mem_Ico.1 ha
    have hb' := Finset.mem_Ico.1 hb
    have hpi : (0 : ℝ) < p i := by have := hp2 i; positivity
    have hpj : (0 : ℝ) < p j := by have := hp2 j; positivity
    have : (b : ℝ) * p i = a * p j := by
      field_simp at hab; linarith
    have hnat : b * p i = a * p j := by exact_mod_cast this
    have hpij : p i ≠ p j := fun h => hij (hmono.injective h)
    have hdvd : p i ∣ a * p j := ⟨b, by rw [← hnat]; ring⟩
    rcases (Nat.Prime.dvd_mul (hp i)).1 hdvd with h | h
    · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · exact hpij ((Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).1 h)
  have h0 : (0 : ℝ) ∉ Finset.univ.biUnion G := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h
    rw [hGi] at hi
    obtain ⟨a, ha, hav⟩ := Finset.mem_image.1 hi
    have := (Finset.mem_Ico.1 ha).1
    have hpi : (0 : ℝ) < p i := by have := hp2 i; positivity
    rw [div_eq_zero_iff] at hav
    rcases hav with h | h
    · have : (a : ℝ) = 0 := h
      have : a = 0 := by exact_mod_cast this
      omega
    · linarith
  have hT : ∑ r ∈ F, ‖Sf S r‖ ^ 2 =
      ‖Sf S 0‖ ^ 2 + ∑ i, ∑ a ∈ Finset.Ico 1 (p i), ‖Sf S (a / p i)‖ ^ 2 := by
    rw [hF, Finset.sum_insert h0, Finset.sum_biUnion hdisj]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGi, Finset.sum_image]
    intro a _ b _ hab
    have hpi : (p i : ℝ) ≠ 0 := by have := hp2 i; positivity
    have : (a : ℝ) = b := by
      have := hab; simp only at this; field_simp at this; exact this
    exact_mod_cast this
  have hTlb : (501 : ℝ) * (S.card : ℝ) ^ 2 ≤ ∑ r ∈ F, ‖Sf S r‖ ^ 2 := by
    rw [hT, hS0]
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 1000))) fun i _ => hY i
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    push_cast at this
    linarith
  -- combine
  have hNr : (L : ℝ) < N := by rw [hL]; exact_mod_cast hN
  have hcard0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have key : (L : ℝ) * (501 * (S.card : ℝ) ^ 2) ≤ S.card * (((N + L : ℕ) : ℝ) * L + (L : ℝ) ^ 2) :=
    (mul_le_mul_of_nonneg_left hTlb hLpos.le).trans hdual
  push_cast at key
  have key2 : (S.card : ℝ) * (501 * S.card) ≤ S.card * (N + 2 * L) := by
    have : (L : ℝ) * ((S.card : ℝ) * (501 * S.card)) ≤ L * (S.card * (N + 2 * L)) := by
      nlinarith
    exact le_of_mul_le_mul_left this hLpos
  rcases hcard0.lt_or_eq with hpos | hzero
  · have : (501 : ℝ) * S.card ≤ N + 2 * L := by
      have := le_of_mul_le_mul_left (by linarith : (S.card : ℝ) * (501 * S.card) ≤
        S.card * (N + 2 * L)) hpos
      linarith
    have : (10 : ℝ) * S.card ≤ N := by linarith
    exact_mod_cast this
  · have : S.card = 0 := by exact_mod_cast hzero.symm
    omega

#print axioms green_44.variants.less_than_sqrt

end Green44
