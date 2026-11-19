import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Roots

open scoped Polynomial

namespace Erdos1114

open Polynomial

/-- The open intervals `(a + d k, a + d (k + 1))` are pairwise disjoint. -/
lemma interval_eq {a d : ℝ} (hd : 0 < d) {j k : ℕ} {x : ℝ}
    (hj : x ∈ Set.Ioo (a + d * j) (a + d * (j + 1)))
    (hk : x ∈ Set.Ioo (a + d * k) (a + d * (k + 1))) : j = k := by
  obtain ⟨hj1, hj2⟩ := hj
  obtain ⟨hk1, hk2⟩ := hk
  have h1 : (j : ℝ) < k + 1 := lt_of_mul_lt_mul_left (by linarith) hd.le
  have h2 : (k : ℝ) < j + 1 := lt_of_mul_lt_mul_left (by linarith) hd.le
  have h1' : j < k + 1 := by exact_mod_cast h1
  have h2' : k < j + 1 := by exact_mod_cast h2
  omega

/-- Rolle's theorem for real polynomials. -/
lemma rolle_point {f : ℝ[X]} {u v : ℝ} (h : u < v) (hu : f.eval u = 0) (hv : f.eval v = 0) :
    ∃ x ∈ Set.Ioo u v, f.derivative.eval x = 0 := by
  obtain ⟨c, hc, h0⟩ := exists_deriv_eq_zero (f := fun x => f.eval x) h
    f.differentiable.continuous.continuousOn (by simp only [hu, hv])
  rw [Polynomial.deriv] at h0
  exact ⟨c, hc, h0⟩

theorem erdos_1114.variants.rolle {N : ℕ} {a d : ℝ} (hd : 0 < d) {f : ℝ[X]}
    (hdegree : f.natDegree = N + 1)
    (hroots : ∀ j : ℕ, j ≤ N → f.eval (a + d * j) = 0) :
    (∀ k : ℕ, k < N →
      ∃! x : ℝ, x ∈ Set.Ioo (a + d * k) (a + d * (k + 1)) ∧ f.derivative.eval x = 0) ∧
    (∀ x : ℝ, f.derivative.eval x = 0 →
      ∃ k : ℕ, k < N ∧ x ∈ Set.Ioo (a + d * k) (a + d * (k + 1))) := by
  have hf' : f.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hdeg' : f.derivative.natDegree ≤ N := by
    have := natDegree_derivative_le f
    omega
  have hex : ∀ k : ℕ, k < N →
      ∃ x ∈ Set.Ioo (a + d * k) (a + d * (k + 1)), f.derivative.eval x = 0 := by
    intro k hk
    apply rolle_point
    · linarith
    · exact hroots k hk.le
    · have := hroots (k + 1) (by omega)
      push_cast at this
      exact this
  choose! c hc hc0 using hex
  have hinj : Set.InjOn c (Finset.range N) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact interval_eq hd (hc i hi) (by rw [hij]; exact hc j hj)
  have hScard : ((Finset.range N).image c).card = N := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have key : ∀ x, f.derivative.eval x = 0 → x ∈ (Finset.range N).image c := by
    intro x hx
    by_contra hxS
    have hsub : insert x ((Finset.range N).image c) ⊆ f.derivative.roots.toFinset := by
      intro y hy
      rw [Multiset.mem_toFinset, mem_roots hf']
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
        exact hc0 k (Finset.mem_range.mp hk)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hxS, hScard] at h1
    have h2 := (Multiset.toFinset_card_le f.derivative.roots).trans (card_roots' _)
    omega
  refine ⟨fun k hk => ⟨c k, ⟨hc k hk, hc0 k hk⟩, fun y hy => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (key y hy.2)
    rw [Finset.mem_range] at hj
    rw [interval_eq hd (hc j hj) hy.1]
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (key x hx)
    rw [Finset.mem_range] at hj
    exact ⟨j, hj, hc j hj⟩

end Erdos1114

#print axioms Erdos1114.erdos_1114.variants.rolle
