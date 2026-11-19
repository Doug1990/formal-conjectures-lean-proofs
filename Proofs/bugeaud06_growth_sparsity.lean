import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Bugeaud06

open Filter

/-- Finitely many multiples `z • ξ`, `|z| ≤ L`, are `ε`-dense on the circle. -/
lemma cover (ξ : ℝ) (hξ : Irrational ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, ∀ y : AddCircle (1 : ℝ), ∃ z : ℤ, -(L : ℤ) ≤ z ∧ z ≤ L ∧
      dist y (z • (ξ : AddCircle (1 : ℝ))) < ε := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hd : DenseRange (· • (ξ : AddCircle (1 : ℝ)) : ℤ → AddCircle (1 : ℝ)) :=
    AddCircle.denseRange_zsmul_coe_iff.2 (by rw [div_one]; exact hξ)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun z : ℤ => Metric.ball (z • (ξ : AddCircle (1 : ℝ))) ε) (fun _ => Metric.isOpen_ball)
    (fun y _ => by
      obtain ⟨z, hz⟩ := Metric.denseRange_iff.1 hd y ε hε
      exact Set.mem_iUnion.2 ⟨z, Metric.mem_ball.2 hz⟩)
  refine ⟨t.sup Int.natAbs, fun y => ?_⟩
  obtain ⟨z, hzt, hz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  have h1 : z.natAbs ≤ t.sup Int.natAbs := Finset.le_sup hzt
  have h2 : |z| ≤ ((t.sup Int.natAbs : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]; exact_mod_cast h1
  exact ⟨z, (abs_le.1 h2).1, (abs_le.1 h2).2, Metric.mem_ball.1 hz⟩

/-- Offset of block `k = ⌊√n⌋`. -/
def H (f : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range ((k + 1) * (k + 1)), f i

/-- The sequence: runs `[k², (k+1)²)` shifted by `H f k`. -/
def M (f : ℕ → ℕ) (n : ℕ) : ℕ := n + H f (Nat.sqrt n)

lemma H_mono (f : ℕ → ℕ) : Monotone (H f) := fun a b hab =>
  Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.mul_le_mul (by omega) (by omega)))

lemma le_H (f : ℕ → ℕ) (k : ℕ) : f k ≤ H f k :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_mul_self _)))

lemma le_M (f : ℕ → ℕ) (n : ℕ) : f n ≤ M f n := by
  have : f n ≤ H f (Nat.sqrt n) :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_sqrt n))
  simp only [M]; omega

lemma M_strictMono (f : ℕ → ℕ) : StrictMono (M f) := strictMono_nat_of_lt_succ fun n => by
  have := H_mono f (Nat.sqrt_le_sqrt (Nat.le_add_right n 1))
  simp only [M]; omega

lemma M_dense (f : ℕ → ℕ) (ξ : ℝ) (hξ : Irrational ξ) :
    Dense (Set.range fun n => (↑(ξ * M f n) : AddCircle (1 : ℝ))) := by
  refine Metric.denseRange_iff.2 fun y ε hε => ?_
  obtain ⟨k, hk⟩ := cover ξ hξ ε hε
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = k * k + k + H f k := ⟨_, rfl⟩
  obtain ⟨z, hz1, hz2, hd⟩ := hk (y - ↑(ξ * a))
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = k + z := ⟨(k + z).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hsq : Nat.sqrt (k * k + j) = k := Nat.sqrt_add_eq k (by omega)
  have hZ : ((M f (k * k + j) : ℕ) : ℤ) = (a : ℤ) + z := by
    simp only [M, hsq]
    generalize k * k = q at ha
    omega
  have hR : ((M f (k * k + j) : ℕ) : ℝ) = (a : ℝ) + z := by exact_mod_cast hZ
  refine ⟨k * k + j, ?_⟩
  show dist y (↑(ξ * (M f (k * k + j) : ℝ)) : AddCircle (1 : ℝ)) < ε
  have hs : ξ * (z : ℝ) = z • ξ := by rw [zsmul_eq_mul, mul_comm]
  rw [hR, mul_add, AddCircle.coe_add, hs, AddCircle.coe_zsmul]
  rw [show y = (↑(ξ * a) : AddCircle (1 : ℝ)) + (y - ↑(ξ * a)) by simp, dist_add_left]
  exact hd

theorem exists_dense_of_growth (f : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ n, f n ≤ m n) ∧
      ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) :=
  ⟨M f, M_strictMono f, le_M f, M_dense f⟩

def countingFn (m : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun n => m n ≤ N).card

/-- Every counted index `n` satisfies `n + 1 ≤ (log log N)²` once `f k ≥ exp (exp (k+1))`. -/
lemma idx_bound (g : ℕ → ℕ) (hg : ∀ k : ℕ, Real.exp (Real.exp ((k : ℝ) + 1)) ≤ g k) (N n : ℕ)
    (hn : M g n ≤ N) : ((n + 1 : ℕ) : ℝ) ≤ (Real.log (Real.log N)) ^ 2 := by
  have h1 : g (Nat.sqrt n) ≤ M g n := by have := le_H g (Nat.sqrt n); simp only [M]; omega
  have h5 : n + 1 ≤ (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  generalize Nat.sqrt n = k at h1 h5
  have h2 : Real.exp (Real.exp (k + 1)) ≤ (N : ℝ) :=
    (hg k).trans (by exact_mod_cast h1.trans hn)
  have hN : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) h2
  have h3 : Real.exp (k + 1) ≤ Real.log N := (Real.le_log_iff_exp_le hN).2 h2
  have h4 : (k : ℝ) + 1 ≤ Real.log (Real.log N) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h3)).2 h3
  have h6 : ((n + 1 : ℕ) : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
    rw [sq]; exact_mod_cast h5
  exact h6.trans (pow_le_pow_left₀ (by positivity) h4 2)

lemma count_bound (g : ℕ → ℕ) (hg : ∀ k : ℕ, Real.exp (Real.exp ((k : ℝ) + 1)) ≤ g k) (N : ℕ) :
    (countingFn (M g) N : ℝ) ≤ (Real.log (Real.log N)) ^ 2 := by
  have hsub : (Finset.range (N + 1)).filter (fun n => M g n ≤ N) ⊆
      Finset.range ⌊(Real.log (Real.log N)) ^ 2⌋₊ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_range, Nat.lt_iff_add_one_le]
    exact Nat.le_floor (idx_bound g hg N n hn.2)
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  exact (Nat.cast_le.2 this).trans (Nat.floor_le (sq_nonneg _))

theorem exists_dense_of_growth_and_sparsity (f : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ n, f n ≤ m n) ∧
      (∀ᶠ N : ℕ in atTop, (countingFn m N : ℝ) ≤ (Real.log (Real.log N)) ^ 2) ∧
      ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  let g : ℕ → ℕ := fun n => max (f n) ⌈Real.exp (Real.exp ((n : ℝ) + 1))⌉₊
  have hg : ∀ k : ℕ, Real.exp (Real.exp ((k : ℝ) + 1)) ≤ g k := fun k =>
    (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right (f k) _))
  refine ⟨M g, M_strictMono g, fun n => (le_max_left _ _).trans (le_M g n),
    Eventually.of_forall (count_bound g hg), M_dense g⟩

end Bugeaud06

#print axioms Bugeaud06.exists_dense_of_growth
#print axioms Bugeaud06.exists_dense_of_growth_and_sparsity
