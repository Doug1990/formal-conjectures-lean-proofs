import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.MeanValue

/-! Mathoverflow 17560, variant `all_nats` (FormalConjectures/Mathoverflow/17560.lean:43).
Proof: finite differences. If `x ∉ ℕ`, take `k = ⌊x⌋₊ + 1`. The `k`-th forward difference
of `n ↦ n ^ x` at `n` is an integer and equals `x(x-1)…(x-k+1) ξ ^ (x - k)` for some
`ξ ≥ n` (iterated mean value theorem), which is nonzero and tends to `0`. -/

namespace Mathoverflow17560

/-- Iterated forward difference, defined recursively. -/
noncomputable def D : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, h => h
  | k + 1, h => D k (fun s => h (s + 1) - h s)

/-- Iterated mean value theorem. -/
theorem D_mvt : ∀ (k : ℕ) (h : ℕ → ℝ → ℝ) (t : ℝ), 0 < t →
    (∀ i < k, ∀ s > 0, HasDerivAt (h i) (h (i + 1) s) s) →
    ∃ ξ, t ≤ ξ ∧ ξ ≤ t + k ∧ D k (h 0) t = h k ξ := by
  intro k
  induction k with
  | zero =>
    intro h t _ _
    exact ⟨t, le_rfl, by simp, rfl⟩
  | succ k ih =>
    intro h t ht hd
    set H : ℕ → ℝ → ℝ := fun i s => h i (s + 1) - h i s with hH
    have hdH : ∀ i < k, ∀ s > 0, HasDerivAt (H i) (H (i + 1) s) s := by
      intro i hi s hs
      have h1 : HasDerivAt (fun s => h i (s + 1)) (h (i + 1) (s + 1)) s :=
        (hd i (by omega) (s + 1) (by linarith)).comp_add_const s 1
      exact h1.sub (hd i (by omega) s hs)
    obtain ⟨ξ, h1, h2, h3⟩ := ih H t ht hdH
    have hξ : 0 < ξ := by linarith
    have hcont : ContinuousOn (h k) (Set.Icc ξ (ξ + 1)) := by
      intro y hy
      exact (hd k (by omega) y (by linarith [hy.1])).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (h k) (h (k + 1)) (by linarith : ξ < ξ + 1)
      hcont (fun y hy => hd k (by omega) y (by linarith [hy.1]))
    refine ⟨c, by linarith [hc.1], ?_, ?_⟩
    · push_cast; linarith [hc.2]
    · show D k (H 0) t = h (k + 1) c
      rw [h3, hc']
      simp [H]

/-- Iterated differences of integer-valued sequences are integers. -/
theorem D_int : ∀ (k : ℕ) (h : ℝ → ℝ) (n : ℝ), (∀ m : ℕ, ∃ z : ℤ, h (n + m) = z) →
    ∃ z : ℤ, D k h n = z := by
  intro k
  induction k with
  | zero =>
    intro h n hh
    obtain ⟨z, hz⟩ := hh 0
    exact ⟨z, by simpa [D] using hz⟩
  | succ k ih =>
    intro h n hh
    apply ih
    intro m
    obtain ⟨a, ha⟩ := hh (m + 1)
    obtain ⟨b, hb⟩ := hh m
    refine ⟨a - b, ?_⟩
    have e : n + (m : ℝ) + 1 = n + ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    simp only [Int.cast_sub]
    rw [e, ha, hb]

theorem mathoverflow_17560.variants.all_nats {x : ℝ} (hx : ∀ n : ℕ, ∃ m : ℕ, (n : ℝ) ^ x = m) :
    ∃ m : ℕ, x = m := by
  by_contra hne
  simp only [not_exists] at hne
  set k : ℕ := ⌊x⌋₊ + 1 with hk
  have hxk : x < k := by rw [hk]; push_cast; exact Nat.lt_floor_add_one x
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun i => ∏ j ∈ Finset.range i, (x - j) := ⟨_, rfl⟩
  have hck : c k ≠ 0 := by
    rw [hc]
    rw [Finset.prod_ne_zero_iff]
    intro j _
    exact sub_ne_zero.2 (hne j)
  have hcs : ∀ i, c (i + 1) = c i * (x - i) := by
    intro i; rw [hc]; exact Finset.prod_range_succ _ _
  have hc0 : c 0 = 1 := by rw [hc]; simp
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ℝ → ℝ, h = fun i s => c i * s ^ (x - i) := ⟨_, rfl⟩
  have hd : ∀ i < k, ∀ s > 0, HasDerivAt (h i) (h (i + 1) s) s := by
    intro i _ s hs
    have h1 : HasDerivAt (fun s : ℝ => s ^ (x - i)) ((x - i) * s ^ (x - i - 1)) s :=
      Real.hasDerivAt_rpow_const (Or.inl hs.ne')
    have h2 := h1.const_mul (c i)
    have e : x - ((i + 1 : ℕ) : ℝ) = x - i - 1 := by push_cast; ring
    have e2 : h (i + 1) s = c i * ((x - i) * s ^ (x - i - 1)) := by
      rw [hh]; dsimp only; rw [hcs, e]; ring
    rw [e2]
    have e3 : h i = fun s : ℝ => c i * s ^ (x - i) := by rw [hh]
    rw [e3]
    exact h2
  -- choose n large
  have hlim : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) ^ (-((k : ℝ) - x))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hpos : 0 < 1 / (|c k| + 1) := by positivity
  obtain ⟨n, hn1, hn2⟩ := ((Filter.eventually_ge_atTop 1).and
    ((tendsto_order.1 hlim).2 _ hpos)).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨ξ, hξ1, _, hξ⟩ := D_mvt k h n hn0 hd
  have hξ0 : 0 < ξ := by linarith
  obtain ⟨z, hz⟩ := D_int k (h 0) n (by
    intro m
    obtain ⟨a, ha⟩ := hx (n + m)
    refine ⟨a, ?_⟩
    rw [hh]; dsimp only
    rw [hc0, one_mul, Nat.cast_zero, sub_zero]
    push_cast at ha
    rw [ha]; rfl)
  -- bound
  have hb : |h k ξ| < 1 := by
    simp only [hh]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hξ0 _)]
    have e1 : ξ ^ (x - k) ≤ (n : ℝ) ^ (x - k) :=
      Real.rpow_le_rpow_of_nonpos hn0 hξ1 (by linarith)
    have e2 : (n : ℝ) ^ (x - k) < 1 / (|c k| + 1) := by
      have : -((k : ℝ) - x) = x - k := by ring
      rw [← this]; exact hn2
    have e3 : 0 ≤ ξ ^ (x - k) := (Real.rpow_pos_of_pos hξ0 _).le
    calc |c k| * ξ ^ (x - k) ≤ |c k| * (1 / (|c k| + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith
      _ < 1 := by
          rw [mul_one_div, div_lt_one (by positivity)]; linarith
  have hz0 : z = 0 := by
    rw [hξ] at hz
    rw [hz] at hb
    have : |z| < 1 := by exact_mod_cast hb
    exact Int.abs_lt_one_iff.1 this
  rw [hz0, hξ] at hz
  simp only [hh, Int.cast_zero] at hz
  exact (mul_ne_zero hck (Real.rpow_pos_of_pos hξ0 _).ne') hz

end Mathoverflow17560

#print axioms Mathoverflow17560.mathoverflow_17560.variants.all_nats
