import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter

namespace Erdos1122

namespace M

variable (f : ℕ → ℝ)

lemma f_one (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) : f 1 = 0 := by
  have h := hf 1 one_pos 1 one_pos (Nat.coprime_one_left 1)
  rw [one_mul] at h
  linarith

lemma mono (hmono : ∀ n ≥ 1, f n ≤ f (n + 1)) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    f a ≤ f b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ b hb ih => exact ih.trans (hmono b (ha.trans hb))

lemma nonneg (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hmono : ∀ n ≥ 1, f n ≤ f (n + 1)) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ f n := by
  have := mono f hmono le_rfl hn
  rwa [f_one f hf] at this

lemma pow_bounds (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hmono : ∀ n ≥ 1, f n ≤ f (n + 1)) {t : ℕ} (ht : 1 ≤ t) (k : ℕ) :
    (k : ℝ) * f t ≤ f ((t + 1) ^ k) ∧ f ((t + 1) ^ k) ≤ (k : ℝ) * f (t + 2) := by
  induction k with
  | zero => simp [f_one f hf]
  | succ k ih =>
    have hpos : 0 < (t + 1) ^ k := Nat.pow_pos (Nat.succ_pos t)
    have c1 : Nat.Coprime ((t + 1) ^ k) t :=
      Nat.Coprime.pow_left k ((Nat.coprime_self_add_left).2 (Nat.coprime_one_left t))
    have c2 : Nat.Coprime ((t + 1) ^ k) (t + 2) := by
      apply Nat.Coprime.pow_left k
      rw [show t + 2 = (t + 1) + 1 by omega]
      exact Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)
    have e1 := hf _ hpos t (by omega) c1
    have e2 := hf _ hpos (t + 2) (by omega) c2
    have l1 : f ((t + 1) ^ k * t) ≤ f ((t + 1) ^ (k + 1)) :=
      mono f hmono (Nat.mul_pos hpos (by omega))
        (by rw [pow_succ]; exact Nat.mul_le_mul_left _ (by omega))
    have l2 : f ((t + 1) ^ (k + 1)) ≤ f ((t + 1) ^ k * (t + 2)) :=
      mono f hmono (Nat.pow_pos (Nat.succ_pos t))
        (by rw [pow_succ]; exact Nat.mul_le_mul_left _ (by omega))
    push_cast
    constructor <;> linarith [ih.1, ih.2]

lemma limit_arg {A B L : ℝ} (h : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * A ≤ ((k : ℝ) * L + 1) * B) :
    A ≤ L * B := by
  by_contra hc
  have hd : 0 < A - L * B := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (B / (A - L * B))
  have hB : 0 ≤ B := by
    have := h 1 le_rfl
    by_contra hB
    push Not at hB
    nlinarith
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg hB hd.le) hk
  have hk1 : 1 ≤ k := by
    have : 0 < k := by exact_mod_cast hk0
    omega
  have h1 := h k hk1
  have h2 : B < k * (A - L * B) := (div_lt_iff₀ hd).1 hk
  nlinarith

lemma ratio (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hmono : ∀ n ≥ 1, f n ≤ f (n + 1)) {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    f s * Real.log ((t : ℝ) + 1) ≤ f (t + 2) * Real.log ((s : ℝ) + 1) := by
  have hlt : 0 < Real.log ((t : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hls : 0 ≤ Real.log ((s : ℝ) + 1) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ s := by positivity
    linarith
  set L := Real.log ((s : ℝ) + 1) / Real.log ((t : ℝ) + 1) with hL
  have hB : 0 ≤ f (t + 2) := nonneg f hf hmono (by omega)
  have key : f s ≤ L * f (t + 2) := by
    apply limit_arg
    intro k hk
    set j := ⌈(k : ℝ) * L⌉₊ with hj
    have hj1 : (k : ℝ) * L ≤ j := Nat.le_ceil _
    have hj2 : (j : ℝ) < (k : ℝ) * L + 1 := Nat.ceil_lt_add_one (by positivity)
    have hpow : (s + 1) ^ k ≤ (t + 1) ^ j := by
      have h1 : (k : ℝ) * Real.log ((s : ℝ) + 1) ≤ (j : ℝ) * Real.log ((t : ℝ) + 1) := by
        have := mul_le_mul_of_nonneg_right hj1 hlt.le
        rw [hL, mul_assoc, div_mul_cancel₀ _ hlt.ne'] at this
        exact this
      rw [← Real.log_pow, ← Real.log_pow] at h1
      have h2 : ((s : ℝ) + 1) ^ k ≤ ((t : ℝ) + 1) ^ j :=
        (Real.log_le_log_iff (by positivity) (by positivity)).1 h1
      exact_mod_cast h2
    have b1 := (pow_bounds f hf hmono hs k).1
    have b2 := (pow_bounds f hf hmono ht j).2
    have b3 : f ((s + 1) ^ k) ≤ f ((t + 1) ^ j) :=
      mono f hmono (Nat.pow_pos (Nat.succ_pos s)) hpow
    have b4 : (j : ℝ) * f (t + 2) ≤ ((k : ℝ) * L + 1) * f (t + 2) :=
      mul_le_mul_of_nonneg_right hj2.le hB
    linarith
  have := mul_le_mul_of_nonneg_right key hlt.le
  calc f s * Real.log ((t : ℝ) + 1) ≤ L * f (t + 2) * Real.log ((t : ℝ) + 1) := this
    _ = f (t + 2) * Real.log ((s : ℝ) + 1) := by
      rw [hL]; field_simp

lemma log_gap {X : ℝ} (hX : 1 < X) :
    Real.log (X + 1) - Real.log X ≤ 1 / (X - 1) ∧
      Real.log X - Real.log (X - 1) ≤ 1 / (X - 1) := by
  have hX0 : 0 < X := by linarith
  have hX1 : 0 < X - 1 := by linarith
  constructor
  · have h1 : Real.log ((X + 1) / X) ≤ (X + 1) / X - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) hX0.ne', div_sub_one hX0.ne', add_sub_cancel_left] at h1
    have h2 : 1 / X ≤ 1 / (X - 1) := one_div_le_one_div_of_le hX1 (by linarith)
    linarith
  · have h1 : Real.log (X / (X - 1)) ≤ X / (X - 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hX0.ne' hX1.ne', div_sub_one hX1.ne', sub_sub_cancel] at h1
    exact h1

end M

theorem erdos_1122.variants.monotone (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hmono : ∀ n ≥ 1, f n ≤ f (n + 1)) :
    ∃ c : ℝ, ∀ n > 0, f n = c * Real.log n := by
  -- the sup constant
  set a : ℕ → ℝ := fun s => f (s + 1) / Real.log ((s : ℝ) + 2) with ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogs : ∀ s : ℕ, 0 < Real.log ((s : ℝ) + 2) := fun s => by
    apply Real.log_pos; have : (0 : ℝ) ≤ s := by positivity
    linarith
  have hcast : ∀ s : ℕ, ((s + 1 : ℕ) : ℝ) + 1 = (s : ℝ) + 2 := fun s => by push_cast; ring
  have hbdd : BddAbove (Set.range a) := by
    refine ⟨f 3 / Real.log 2, ?_⟩
    rintro _ ⟨s, rfl⟩
    have h := M.ratio f hf hmono (s := s + 1) (t := 1) (by omega) le_rfl
    rw [hcast] at h
    norm_num at h
    rw [show (s : ℝ) + 1 + 1 = s + 2 by ring] at h
    simp only [ha]
    rw [div_le_div_iff₀ (hlogs s) hlog2]
    linarith
  set C := ⨆ s, a s with hC
  have hupper : ∀ x : ℕ, 1 ≤ x → f x ≤ C * Real.log ((x : ℝ) + 1) := by
    intro x hx
    obtain ⟨s, rfl⟩ : ∃ s, x = s + 1 := ⟨x - 1, by omega⟩
    have h := le_ciSup hbdd s
    simp only [ha] at h
    rw [div_le_iff₀ (hlogs s)] at h
    rw [hcast]; exact h
  have hlower : ∀ t : ℕ, 1 ≤ t → C * Real.log ((t : ℝ) + 1) ≤ f (t + 2) := by
    intro t ht
    have hlt : 0 < Real.log ((t : ℝ) + 1) := by
      apply Real.log_pos
      have : (1 : ℝ) ≤ t := by exact_mod_cast ht
      linarith
    have h : C ≤ f (t + 2) / Real.log ((t : ℝ) + 1) := by
      apply ciSup_le
      intro s
      simp only [ha]
      have h := M.ratio f hf hmono (s := s + 1) (t := t) (by omega) ht
      rw [hcast] at h
      rw [div_le_div_iff₀ (hlogs s) hlt]
      linarith
    rwa [le_div_iff₀ hlt] at h
  have hC0 : 0 ≤ C := by
    have h := le_ciSup hbdd 0
    simp only [ha, M.f_one f hf] at h
    simpa using h
  -- error bound
  have hbound : ∀ x : ℕ, 3 ≤ x → |f x - C * Real.log x| ≤ C / ((x : ℝ) - 1) := by
    intro x hx
    have hX : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
    obtain ⟨g1, g2⟩ := M.log_gap hX
    have u := hupper x (by omega)
    have l := hlower (x - 2) (by omega)
    have e : ((x - 2 : ℕ) : ℝ) + 1 = (x : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e, show x - 2 + 2 = x by omega] at l
    have m1 := mul_le_mul_of_nonneg_left g1 hC0
    have m2 := mul_le_mul_of_nonneg_left g2 hC0
    rw [abs_le]
    constructor
    · rw [mul_one_div] at m2
      nlinarith
    · rw [mul_one_div] at m1
      nlinarith
  refine ⟨C, fun n hn => ?_⟩
  have hk : ∀ k : ℕ, 2 ≤ k → |f n - C * Real.log n| ≤ 2 * C / k := by
    intro k hk
    have hq : Nat.Coprime n (k * n + 1) :=
      (Nat.coprime_mul_right_add_right n 1 k).2 (Nat.coprime_one_right n)
    have e := hf n hn (k * n + 1) (by omega) hq
    have hkn : 2 ≤ k * n := le_trans hk (Nat.le_mul_of_pos_right k hn)
    have hnq : 3 ≤ n * (k * n + 1) := by
      have : k * n + 1 ≤ n * (k * n + 1) := Nat.le_mul_of_pos_left _ hn
      omega
    have b1 := hbound _ hnq
    have b2 := hbound (k * n + 1) (by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hknR : (k : ℝ) ≤ (k : ℝ) * n := by nlinarith
    push_cast at b1 b2 e
    rw [e, Real.log_mul (by positivity) (by positivity)] at b1
    have d1 : C / ((n : ℝ) * (k * n + 1) - 1) ≤ C / k := by
      apply div_le_div_of_nonneg_left hC0 (by positivity)
      nlinarith
    have d2 : C / ((k : ℝ) * n + 1 - 1) ≤ C / k := by
      apply div_le_div_of_nonneg_left hC0 (by positivity)
      linarith
    have : f n - C * Real.log n =
        (f n + f (k * n + 1) - C * (Real.log n + Real.log ((k : ℝ) * n + 1))) -
          (f (k * n + 1) - C * Real.log ((k : ℝ) * n + 1)) := by ring
    rw [this]
    calc _ ≤ |f n + f (k * n + 1) - C * (Real.log n + Real.log ((k : ℝ) * n + 1))| +
          |f (k * n + 1) - C * Real.log ((k : ℝ) * n + 1)| := abs_sub _ _
      _ ≤ C / k + C / k := add_le_add (b1.trans d1) (b2.trans d2)
      _ = 2 * C / k := by ring
  by_contra hne
  have hpos : 0 < |f n - C * Real.log n| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hkk⟩ := exists_nat_gt (2 * C / |f n - C * Real.log n| + 2)
  have hnn : 0 ≤ 2 * C / |f n - C * Real.log n| := by positivity
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) < k := by linarith
    have : 2 < k := by exact_mod_cast this
    omega
  have h1 := hk k hk2
  have hk0 : (0 : ℝ) < k := by linarith
  have h2 : 2 * C < k * |f n - C * Real.log n| := (div_lt_iff₀ hpos).1 (by linarith)
  rw [le_div_iff₀ hk0] at h1
  linarith

end Erdos1122

#print axioms Erdos1122.erdos_1122.variants.monotone
