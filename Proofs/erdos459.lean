import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Lattice.Nat

namespace Erdos459

noncomputable def f (u : ℕ) : ℕ := sInf {v | u < v ∧ v.primeFactors ⊆ u.primeFactors}

lemma sq_mem {u : ℕ} (hu : 2 ≤ u) : u ^ 2 ∈ {v | u < v ∧ v.primeFactors ⊆ u.primeFactors} := by
  refine ⟨?_, ?_⟩
  · have : u * 2 ≤ u * u := Nat.mul_le_mul_left u hu
    rw [pow_two]; omega
  · rw [Nat.primeFactors_pow u (by decide)]

lemma f_mem {u : ℕ} (hu : 2 ≤ u) : f u ∈ {v | u < v ∧ v.primeFactors ⊆ u.primeFactors} :=
  Nat.sInf_mem ⟨_, sq_mem hu⟩

lemma succ_not_mem {u : ℕ} (hu : 2 ≤ u) : ¬ (u + 1).primeFactors ⊆ u.primeFactors := by
  intro h
  have hq : (u + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hmem : (u + 1).minFac ∈ (u + 1).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hq, Nat.minFac_dvd _, by omega⟩
  have hu' := Nat.mem_primeFactors.1 (h hmem)
  have h1 : (u + 1).minFac ∣ 1 := (Nat.dvd_add_right hu'.2.1).mp (Nat.minFac_dvd _)
  exact hq.one_lt.ne' (Nat.dvd_one.mp h1)

theorem erdos_459 {u : ℕ} (hu : 2 ≤ u) : u + 2 ≤ f u ∧ f u ≤ u ^ 2 := by
  refine ⟨?_, Nat.sInf_le (sq_mem hu)⟩
  obtain ⟨h1, h2⟩ := f_mem hu
  rcases Nat.lt_or_ge (f u) (u + 2) with h | h
  · have : f u = u + 1 := by omega
    rw [this] at h2
    exact absurd h2 (succ_not_mem hu)
  · exact h

theorem erdos_459.variants.upper_tight {p : ℕ} (hp : p.Prime) : f p = p ^ 2 := by
  have h2 := hp.two_le
  refine le_antisymm (Nat.sInf_le (sq_mem h2)) ?_
  obtain ⟨h1, hsub⟩ := f_mem h2
  have hne : f p ≠ 0 := by omega
  have heq : f p = p ^ (f p).primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd hne
    intro d hd hdv
    have := hsub (Nat.mem_primeFactors.2 ⟨hd, hdv, hne⟩)
    rw [hp.primeFactors] at this
    exact Finset.mem_singleton.1 this
  generalize hk : (f p).primeFactorsList.length = k at heq
  rw [heq] at h1 ⊢
  apply Nat.pow_le_pow_right hp.pos
  rcases k with _ | _ | k
  · simp at h1; omega
  · simp at h1
  · omega

end Erdos459

#print axioms Erdos459.erdos_459
#print axioms Erdos459.erdos_459.variants.upper_tight
