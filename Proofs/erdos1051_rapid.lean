import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Erdos1051

/--
The series $\sum_{n=0}^\infty \frac{1}{a_n \cdot a_{n+1}}$.
-/
noncomputable def ErdosSeries (a : ℕ → ℤ) : ℝ :=
  ∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))

namespace RG

lemma geom (f : ℕ → ℝ) (N : ℕ) (hstep : ∀ m ≥ N, f (m + 1) ≤ f m / 4) :
    ∀ n ≥ N, ∀ j : ℕ, f (j + n) ≤ f n * (1 / 4) ^ j := by
  intro n hn j
  induction j with
  | zero => simp
  | succ j ih =>
    have h := hstep (j + n) (by omega)
    rw [show j + 1 + n = (j + n) + 1 by omega, pow_succ]
    calc f ((j + n) + 1) ≤ f (j + n) / 4 := h
      _ ≤ f n * (1 / 4) ^ j / 4 := by linarith
      _ = f n * ((1 / 4) ^ j * (1 / 4)) := by ring

lemma summ (f : ℕ → ℝ) (N : ℕ) (hpos : ∀ m ≥ N, 0 < f m)
    (hstep : ∀ m ≥ N, f (m + 1) ≤ f m / 4) : Summable f := by
  refine (summable_nat_add_iff N).1 ?_
  refine Summable.of_nonneg_of_le (fun j => (hpos _ (by omega)).le)
    (geom f N hstep N le_rfl) ?_
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (f N)

lemma tail (f : ℕ → ℝ) (N : ℕ) (hpos : ∀ m ≥ N, 0 < f m)
    (hstep : ∀ m ≥ N, f (m + 1) ≤ f m / 4) (n : ℕ) (hn : N ≤ n) :
    0 < ∑' j, f (j + n) ∧ ∑' j, f (j + n) ≤ 2 * f n := by
  have hs : Summable (fun j => f (j + n)) :=
    (summable_nat_add_iff n).2 (summ f N hpos hstep)
  have hg : Summable (fun j : ℕ => f n * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (f n)
  refine ⟨?_, ?_⟩
  · exact hs.tsum_pos (fun j => (hpos _ (by omega)).le) 0 (by simpa using hpos n hn)
  · have h4 : (1 - 1 / 4 : ℝ)⁻¹ = 4 / 3 := by norm_num
    calc ∑' j, f (j + n) ≤ ∑' j : ℕ, f n * (1 / 4 : ℝ) ^ j :=
          hs.tsum_le_tsum (geom f N hstep n hn) hg
      _ = f n * (1 - 1 / 4)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ ≤ 2 * f n := by rw [h4]; linarith [hpos n hn]

end RG

theorem erdos_1051.variants.rapid_growth (a : ℕ → ℤ) (h_mono : StrictMono a)
    (h_rapid : ∃ C > 0, ∀ n, (a (n + 1) : ℝ) ≥ C * (a n : ℝ) ^ 2) :
    Irrational (ErdosSeries a) := by
  obtain ⟨C, hC, hgrow⟩ := h_rapid
  have hlin : ∀ m : ℕ, (a 0 : ℝ) + m ≤ a m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : a m + 1 ≤ a (m + 1) := h_mono (Nat.lt_succ_self m)
      have h2 : (a m : ℝ) + 1 ≤ a (m + 1) := by exact_mod_cast h1
      push_cast; linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (1 + 2 / C + 4 / C ^ 2 - a 0)
  have hbig : ∀ m ≥ N, 1 + 2 / C + 4 / C ^ 2 ≤ (a m : ℝ) := by
    intro m hm
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith [hlin m]
  have hC2pos : 0 < C ^ 2 := by positivity
  have hd1 : 0 ≤ 2 / C := by positivity
  have hd2 : 0 ≤ 4 / C ^ 2 := by positivity
  have ha1 : ∀ m ≥ N, (1 : ℝ) ≤ a m := by
    intro m hm; have := hbig m hm
    linarith
  have hCa : ∀ m ≥ N, (2 : ℝ) ≤ C * a m := by
    intro m hm; have := hbig m hm
    have h : 2 / C ≤ (a m : ℝ) := by linarith
    rw [div_le_iff₀ hC] at h; linarith
  have hC2a : ∀ m ≥ N, (4 : ℝ) ≤ C ^ 2 * a m := by
    intro m hm; have := hbig m hm
    have h : 4 / C ^ 2 ≤ (a m : ℝ) := by linarith
    rw [div_le_iff₀ hC2pos] at h; linarith
  have hdouble : ∀ m ≥ N, 2 * (a m : ℝ) ≤ a (m + 1) := by
    intro m hm
    have h1 := hgrow m
    have h2 := mul_le_mul_of_nonneg_right (hCa m hm)
      (show (0 : ℝ) ≤ a m by linarith [ha1 m hm])
    nlinarith
  have hapos : ∀ m ≥ N, (0 : ℝ) < a m := fun m hm => by linarith [ha1 m hm]
  set f : ℕ → ℝ := fun m => 1 / ((a m : ℝ) * (a (m + 1) : ℝ)) with hf
  have hfpos : ∀ m ≥ N, 0 < f m := by
    intro m hm
    have h0 := hapos m hm
    have h1 := hapos (m + 1) (by omega)
    simp only [hf]
    exact one_div_pos.2 (mul_pos h0 h1)
  have hfstep : ∀ m ≥ N, f (m + 1) ≤ f m / 4 := by
    intro m hm
    have h0 := hapos m hm
    have h1 := hapos (m + 1) (by omega)
    have hd0 := hdouble m hm
    have hd1 := hdouble (m + 1) (by omega)
    simp only [hf]
    rw [div_div]
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos h0 h1) (by norm_num)
    · nlinarith [mul_le_mul_of_nonneg_left
        (show 4 * (a m : ℝ) ≤ a (m + 1 + 1) by linarith) h1.le]
  have hsum : Summable f := RG.summ f N hfpos hfstep
  have hx : ErdosSeries a = ∑' m, f m := rfl
  -- integer data
  set a' : ℕ → ℤ := fun k => if a k = 0 then 1 else a k with ha'
  have ha'ne : ∀ k, a' k ≠ 0 := by
    intro k
    simp only [ha']
    split_ifs with h
    · exact one_ne_zero
    · exact h
  have ha'eq : ∀ k ≥ N, a' k = a k := by
    intro k hk
    have h1 : (a k : ℝ) ≠ 0 := (hapos k hk).ne'
    have h2 : a k ≠ 0 := by exact_mod_cast h1
    simp only [ha', h2, if_false]
  let Q : ℕ → ℤ := fun n => ∏ k ∈ Finset.range n, a' k
  let q : ℕ → ℤ := fun n => ∏ k ∈ Finset.range (n + 1), a' k
  have hqQ : ∀ n, q n = Q n * a' n := fun n => Finset.prod_range_succ _ _
  have hqne : ∀ n, q n ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.2 (fun k _ => ha'ne k)
  let p : ℕ → ℤ := fun n => ∑ m ∈ Finset.range n,
    (if a m = 0 ∨ a (m + 1) = 0 then 0 else q n / (a m * a (m + 1)))
  have hp : ∀ n, (p n : ℝ) = q n * ∑ m ∈ Finset.range n, f m := by
    intro n
    simp only [p, Int.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    split_ifs with h
    · rcases h with h | h <;> simp [hf, h]
    · push Not at h
      have hdvd : a m * a (m + 1) ∣ q n := by
        have e : a' m * a' (m + 1) = a m * a (m + 1) := by simp [ha', h.1, h.2]
        rw [← e, ← Finset.prod_pair (show m ≠ m + 1 by omega)]
        exact Finset.prod_dvd_prod_of_subset _ _ _ (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_range]
          omega)
      have hne : ((a m * a (m + 1) : ℤ) : ℝ) ≠ 0 := by
        push_cast
        exact mul_ne_zero (by exact_mod_cast h.1) (by exact_mod_cast h.2)
      rw [Int.cast_div hdvd hne]
      simp only [hf]
      push_cast
      ring
  -- the error sequence
  let g : ℕ → ℝ := fun n => |(Q n : ℝ)| / a (n + 1)
  have hgstep : ∀ n ≥ N, g (n + 1) ≤ g n / 4 := by
    intro n hn
    have h0 := hapos n hn
    have h1 := hapos (n + 1) (by omega)
    have hQ : (Q (n + 1) : ℝ) = Q n * a n := by
      have e : Q (n + 1) = Q n * a' n := Finset.prod_range_succ _ _
      rw [e, ha'eq n hn]
      push_cast
      ring
    have e1 : C * (a (n + 1) : ℝ) ≥ 4 * a n := by
      have H1 := mul_le_mul_of_nonneg_left (hgrow n) hC.le
      have H2 := mul_le_mul_of_nonneg_right (hC2a n hn) h0.le
      nlinarith
    have e2 : (a (n + 1 + 1) : ℝ) ≥ 4 * a n * a (n + 1) := by
      have H1 := hgrow (n + 1)
      have H2 := mul_le_mul_of_nonneg_right e1 h1.le
      nlinarith
    have hc : (0 : ℝ) < 4 * a n * a (n + 1) := mul_pos (mul_pos (by norm_num) h0) h1
    simp only [g]
    rw [hQ, abs_mul, abs_of_pos h0, div_div]
    calc |(Q n : ℝ)| * a n / a (n + 1 + 1)
        ≤ |(Q n : ℝ)| * a n / (4 * a n * a (n + 1)) :=
          div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) h0.le) hc e2
      _ = |(Q n : ℝ)| / (a (n + 1) * 4) := by
          rw [div_eq_div_iff hc.ne' (mul_pos h1 (by norm_num)).ne']
          ring
  have hgN := RG.geom g N hgstep N le_rfl
  rw [hx]
  intro hmem
  obtain ⟨r, hr⟩ := hmem
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hgN0 : 0 ≤ g N := div_nonneg (abs_nonneg _) (hapos (N + 1) (by omega)).le
  set K : ℝ := 2 * r.den * g N with hK
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) hden.le) hgN0
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 / (K + 1) from one_div_pos.2 (by linarith))
    (show (1 / 4 : ℝ) < 1 by norm_num)
  have hKj : K * (1 / 4 : ℝ) ^ j < 1 := by
    calc K * (1 / 4 : ℝ) ^ j ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left hj.le hK0
      _ < 1 := by
          rw [mul_one_div, div_lt_one (by linarith)]
          linarith
  have hgj : g (j + N) ≤ g N * (1 / 4) ^ j := hgN j
  set n := j + N with hn
  have hnN : N ≤ n := by omega
  obtain ⟨hT0, hT2⟩ := RG.tail f N hfpos hfstep n hnN
  have hdecomp := hsum.sum_add_tsum_nat_add n
  set T := ∑' i, f (i + n) with hT
  let z : ℤ := r.num * q n - r.den * p n
  have hd0 : (r.den : ℝ) ≠ 0 := hden.ne'
  have hrx : (r.num : ℝ) = r.den * ∑' m, f m := by
    rw [← hr, Rat.cast_def, mul_div_assoc']
    exact (mul_div_cancel_left₀ _ hd0).symm
  have hz : (z : ℝ) = r.den * q n * T := by
    simp only [z]
    push_cast
    rw [hp n, hrx, ← hdecomp]
    ring
  have hq : (q n : ℝ) ≠ 0 := by exact_mod_cast hqne n
  have hzne : z ≠ 0 := by
    intro h0
    have h1 : (z : ℝ) = 0 := by rw [h0]; simp
    rw [hz] at h1
    exact mul_ne_zero (mul_ne_zero hd0 hq) hT0.ne' h1
  have hzlt : |(z : ℝ)| < 1 := by
    rw [hz, abs_mul, abs_mul, abs_of_pos hden, abs_of_pos hT0]
    have hqn : |(q n : ℝ)| = |(Q n : ℝ)| * a n := by
      rw [hqQ n, ha'eq n hnN]
      push_cast
      rw [abs_mul, abs_of_pos (hapos n hnN)]
    have hgn : |(q n : ℝ)| * f n = g n := by
      have han := (hapos n hnN).ne'
      rw [hqn]
      simp only [hf, g]
      rw [mul_one_div, mul_comm |(Q n : ℝ)|, mul_div_mul_left _ _ han]
    calc (r.den : ℝ) * |(q n : ℝ)| * T ≤ r.den * |(q n : ℝ)| * (2 * f n) := by
          apply mul_le_mul_of_nonneg_left hT2
          positivity
      _ = 2 * r.den * (|(q n : ℝ)| * f n) := by ring
      _ = 2 * r.den * g n := by rw [hgn]
      _ ≤ 2 * r.den * (g N * (1 / 4) ^ j) := by
          apply mul_le_mul_of_nonneg_left hgj
          positivity
      _ = K * (1 / 4) ^ j := by rw [hK]; ring
      _ < 1 := hKj
  have hzlt' : |z| < 1 := by
    have h : ((|z| : ℤ) : ℝ) < 1 := by push_cast; exact hzlt
    exact_mod_cast h
  have hz0 : z = 0 := by
    rw [abs_lt] at hzlt'
    omega
  exact hzne hz0

end Erdos1051

#print axioms Erdos1051.erdos_1051.variants.rapid_growth
