import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Filter

namespace Erdos454

/-- Define `f n` to be the minimum of `(n + i).nth Prime + (n - i).nth Prime` over `0 < i < n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else ⨅ i : {i : Fin n // 0 < (i : ℕ)}, (n + i).nth Prime + (n - i).nth Prime

namespace P

open Finset

/-! ### Sieve helpers (copied from results/erdos673_i.lean) -/

lemma totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    have hpP := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hpP (hs' q hq)).2 (fun h => hp (h ▸ hq))
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.totient_mul hcop,
      Nat.totient_prime hpP, ih hs']

lemma totient_prod_primes_real (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (Nat.totient (∏ p ∈ s, p) : ℝ) = (∏ p ∈ s, (p : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) := by
  rw [totient_prod_primes s hs, ← Finset.prod_mul_distrib, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h1 : 1 ≤ p := (hs p hp).one_lt.le
  have h0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hs p hp).ne_zero
  rw [Nat.cast_sub h1, mul_sub, mul_one_div_cancel h0]
  simp

lemma cop_mul (Q q : ℕ) : #{n ∈ range (q * Q) | Q.Coprime n} = q * Nat.totient Q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * Q = q * Q + Q by ring, Finset.range_eq_Ico,
      ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (q * Q)) (Nat.le_add_right _ _),
      Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ← Finset.range_eq_Ico, ih, Nat.filter_coprime_Ico_eq_totient]
    ring

lemma cop_count (Q b : ℕ) (hQ : 0 < Q) :
    #{n ∈ range b | Q.Coprime n} ≤ (b / Q + 1) * Nat.totient Q := by
  rw [← cop_mul]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  have h := Nat.lt_mul_div_succ b hQ
  rw [Finset.mem_range] at hx ⊢
  rw [mul_comm]
  omega

lemma block_exists (a : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ b, a < b ∧ ∏ p ∈ (Ico a b).filter Nat.Prime, (1 - 1 / (p : ℝ)) ≤ δ := by
  set f := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n) with hf
  have hnn : ∀ n, 0 ≤ f n := fun n =>
    Set.indicator_nonneg (fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n)) n
  have hns := not_summable_one_div_on_primes
  rw [← hf, not_summable_iff_tendsto_nat_atTop_of_nonneg hnn] at hns
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (tendsto_atTop.1 hns ((∑ i ∈ range a, f i) - Real.log δ))
  refine ⟨max N (a + 1), by omega, ?_⟩
  have hab : a ≤ max N (a + 1) := by omega
  have hsplit := Finset.sum_range_add_sum_Ico f hab
  have hbig := hN (max N (a + 1)) (le_max_left _ _)
  have hIco : ∑ i ∈ Ico a (max N (a + 1)), f i =
      ∑ p ∈ (Ico a (max N (a + 1))).filter Nat.Prime, (1 / (p : ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hf, Set.indicator_apply]
    rfl
  have hL : -Real.log δ ≤ ∑ p ∈ (Ico a (max N (a + 1))).filter Nat.Prime, (1 / (p : ℝ)) := by
    linarith
  calc ∏ p ∈ (Ico a (max N (a + 1))).filter Nat.Prime, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ (Ico a (max N (a + 1))).filter Nat.Prime, Real.exp (-(1 / (p : ℝ))) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hpP := (Finset.mem_filter.1 hp).2
          have : (1 : ℝ) / p ≤ 1 :=
            div_le_one_of_le₀ (by exact_mod_cast hpP.one_lt.le) (Nat.cast_nonneg _)
          linarith
        · intro p _
          have := Real.add_one_le_exp (-(1 / (p : ℝ)))
          linarith
    _ = Real.exp (-(∑ p ∈ (Ico a (max N (a + 1))).filter Nat.Prime, (1 / (p : ℝ)))) := by
        rw [← Real.exp_sum, Finset.sum_neg_distrib]
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 (by linarith)
    _ = δ := Real.exp_log hδ

/-- Product of the primes in `[a, b)`. -/
def Qb (a b : ℕ) : ℕ := ∏ p ∈ (Ico a b).filter Nat.Prime, p

lemma Qb_pos (a b : ℕ) : 0 < Qb a b :=
  Finset.prod_pos fun _ hp => (Finset.mem_filter.1 hp).2.pos

lemma not_cop (a b n : ℕ) (h : ¬ (Qb a b).Coprime n) :
    ∃ p, p.Prime ∧ a ≤ p ∧ p < b ∧ p ∣ n := by
  by_contra hc
  apply h
  refine Nat.Coprime.prod_left fun p hp => ?_
  obtain ⟨hpI, hpP⟩ := Finset.mem_filter.1 hp
  rw [Finset.mem_Ico] at hpI
  rw [Nat.Prime.coprime_iff_not_dvd hpP]
  intro hd
  exact hc ⟨p, hpP, hpI.1, hpI.2, hd⟩

lemma cop_density (a b N : ℕ) (δ : ℝ)
    (hR : ∏ p ∈ (Ico a b).filter Nat.Prime, (1 - 1 / (p : ℝ)) ≤ δ) :
    (#{n ∈ range N | (Qb a b).Coprime n} : ℝ) ≤ δ * N + Qb a b := by
  have hQ := Qb_pos a b
  have hQr : (0 : ℝ) < Qb a b := by exact_mod_cast hQ
  have h1 := cop_count (Qb a b) N hQ
  have h2 : (#{n ∈ range N | (Qb a b).Coprime n} : ℝ) ≤
      ((N / Qb a b : ℕ) : ℝ) * Nat.totient (Qb a b) + Nat.totient (Qb a b) := by
    have : ((#{n ∈ range N | (Qb a b).Coprime n} : ℕ) : ℝ) ≤
        (((N / Qb a b + 1) * Nat.totient (Qb a b) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  have h3 : ((N / Qb a b : ℕ) : ℝ) ≤ (N : ℝ) / Qb a b := Nat.cast_div_le
  have h4 : (Nat.totient (Qb a b) : ℝ) =
      (Qb a b : ℝ) * ∏ p ∈ (Ico a b).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
    unfold Qb
    rw [totient_prod_primes_real _ (fun p hp => (Finset.mem_filter.1 hp).2), Nat.cast_prod]
  have h5 : (Nat.totient (Qb a b) : ℝ) ≤ Qb a b := by exact_mod_cast Nat.totient_le _
  have h6 : ((N / Qb a b : ℕ) : ℝ) * Nat.totient (Qb a b) ≤
      (N : ℝ) / Qb a b * Nat.totient (Qb a b) :=
    mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
  have h7 : (N : ℝ) / Qb a b * Nat.totient (Qb a b) =
      N * ∏ p ∈ (Ico a b).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
    rw [h4]
    field_simp
  have h8 : (N : ℝ) * ∏ p ∈ (Ico a b).filter Nat.Prime, (1 - 1 / (p : ℝ)) ≤ N * δ :=
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
  linarith

/-! ### Primes grow faster than any linear function -/

lemma growth (s : ℕ) : ∃ C : ℕ, ∀ k, s * k ≤ Nat.nth Nat.Prime k + C := by
  obtain ⟨b, -, hb⟩ := block_exists 0 (1 / ((s : ℝ) + 1)) (by positivity)
  refine ⟨(s + 1) * (b + Qb 0 b), fun k => ?_⟩
  have hcount : k + 1 ≤ b + #{n ∈ range (Nat.nth Nat.Prime k + 1) | (Qb 0 b).Coprime n} := by
    have hsub : (range (k + 1)).image (Nat.nth Nat.Prime) ⊆
        range b ∪ {n ∈ range (Nat.nth Nat.Prime k + 1) | (Qb 0 b).Coprime n} := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
      rw [Finset.mem_range] at hj
      have hpr := Nat.prime_nth_prime j
      have hle : Nat.nth Nat.Prime j ≤ Nat.nth Nat.Prime k :=
        (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)
      by_cases hc : (Qb 0 b).Coprime (Nat.nth Nat.Prime j)
      · apply Finset.mem_union_right
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hc⟩
      · apply Finset.mem_union_left
        obtain ⟨q, hq, -, hqb, hqd⟩ := not_cop 0 b _ hc
        have := (Nat.prime_dvd_prime_iff_eq hq hpr).1 hqd
        rw [Finset.mem_range]
        omega
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (Nat.nth_injective Nat.infinite_setOfPred_prime),
      Finset.card_range] at h1
    exact h1.trans ((Finset.card_union_le _ _).trans (by rw [Finset.card_range]))
  have hd := cop_density 0 b (Nat.nth Nat.Prime k + 1) _ hb
  have hk : ((k : ℝ) + 1) ≤ b + 1 / ((s : ℝ) + 1) * ((Nat.nth Nat.Prime k : ℝ) + 1) + Qb 0 b := by
    have : ((k + 1 : ℕ) : ℝ) ≤
        ((b + #{n ∈ range (Nat.nth Nat.Prime k + 1) | (Qb 0 b).Coprime n} : ℕ) : ℝ) := by
      exact_mod_cast hcount
    push_cast at this hd
    linarith
  have hs : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hk hs.le
  have e : ((s : ℝ) + 1) * (1 / ((s : ℝ) + 1) * ((Nat.nth Nat.Prime k : ℝ) + 1)) =
      (Nat.nth Nat.Prime k : ℝ) + 1 := by
    field_simp
  have key : ((s * k : ℕ) : ℝ) ≤ ((Nat.nth Nat.Prime k + (s + 1) * (b + Qb 0 b) : ℕ) : ℝ) := by
    push_cast
    nlinarith [hm, e]
  exact_mod_cast key

/-! ### Exposed points of the lower convex hull of `(n, p_n)` -/

lemma odd_nth (k : ℕ) (hk : 1 ≤ k) : ∃ a, Nat.nth Nat.Prime k = 2 * a + 1 := by
  have h := Nat.add_two_le_nth_prime k
  obtain ⟨a, ha⟩ := (Nat.prime_nth_prime k).odd_of_ne_two (by omega)
  exact ⟨a, ha⟩

lemma exposed (N : ℕ) : ∃ n, N ≤ n ∧ 2 ≤ n ∧ ∀ i, 0 < i → i < n →
    2 * Nat.nth Nat.Prime n + 2 ≤ Nat.nth Nat.Prime (n + i) + Nat.nth Nat.Prime (n - i) := by
  set M := max N 2 with hMdef
  set s := Nat.nth Nat.Prime M with hsdef
  obtain ⟨C, hC⟩ := growth (s + 1)
  set g : ℕ → ℤ := fun k => (Nat.nth Nat.Prime k : ℤ) - (s : ℤ) * k with hg
  have hlow : ∀ k : ℕ, (k : ℤ) - C ≤ g k := by
    intro k
    have := hC k
    simp only [hg]
    zify at this
    linarith
  have hMlt : ∀ k, k < M → g M < g k := by
    intro k hk
    simp only [hg]
    have h2 := Nat.add_two_le_nth_prime k
    have h1 : (1 : ℤ) ≤ (M : ℤ) - k := by omega
    have hs0 : (0 : ℤ) ≤ (s : ℤ) := by positivity
    have := mul_le_mul_of_nonneg_left h1 hs0
    have h3 : (k : ℤ) + 2 ≤ (Nat.nth Nat.Prime k : ℤ) := by exact_mod_cast h2
    have h4 : ((Nat.nth Nat.Prime M : ℕ) : ℤ) = (s : ℤ) := by rw [hsdef]
    nlinarith
  have hMle : g M ≤ s := by
    simp only [hg]
    have : (0 : ℤ) ≤ (s : ℤ) * M := by positivity
    linarith
  set K := C + s + 1 with hK
  have hbig : ∀ k, K ≤ k → g M < g k := by
    intro k hk
    have := hlow k
    have : (K : ℤ) ≤ k := by exact_mod_cast hk
    push_cast [hK] at this
    linarith
  have hMK : M < K := by
    have := Nat.add_two_le_nth_prime M
    omega
  obtain ⟨x0, hx0, hx0min⟩ := Finset.exists_min_image (Finset.range K) g
    ⟨M, Finset.mem_range.2 hMK⟩
  obtain ⟨n, hnA, hnmax⟩ := Finset.exists_max_image
    ((Finset.range K).filter (fun k => g k = g x0)) (fun k => k)
    ⟨x0, Finset.mem_filter.2 ⟨hx0, rfl⟩⟩
  obtain ⟨hnK, hnx⟩ := Finset.mem_filter.1 hnA
  have hmin : ∀ k, g n ≤ g k := by
    intro k
    rw [hnx]
    by_cases hk : k < K
    · exact hx0min k (Finset.mem_range.2 hk)
    · have := hx0min M (Finset.mem_range.2 hMK)
      have := hbig k (by omega)
      linarith
  have hstrict : ∀ k, n < k → g n < g k := by
    intro k hk
    rcases lt_or_eq_of_le (hmin k) with h | h
    · exact h
    · exfalso
      by_cases hkK : k < K
      · have := hnmax k (Finset.mem_filter.2 ⟨Finset.mem_range.2 hkK, by rw [← h, hnx]⟩)
        omega
      · have := hx0min M (Finset.mem_range.2 hMK)
        have := hbig k (by omega)
        rw [hnx] at h
        linarith
  have hnM : M ≤ n := by
    by_contra hlt
    have := hMlt n (by omega)
    have := hmin M
    linarith
  refine ⟨n, by omega, by omega, fun i hi hin => ?_⟩
  have h1 := hstrict (n + i) (by omega)
  have h2 := hmin (n - i)
  simp only [hg] at h1 h2
  have hc : (((n - i : ℕ)) : ℤ) = (n : ℤ) - i := by omega
  rw [hc] at h2
  push_cast at h1
  have hlt : 2 * Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + i) + Nat.nth Nat.Prime (n - i) := by
    zify
    nlinarith
  obtain ⟨a, ha⟩ := odd_nth n (by omega)
  obtain ⟨b, hb⟩ := odd_nth (n + i) (by omega)
  obtain ⟨c, hc⟩ := odd_nth (n - i) (by omega)
  omega

end P

/-- `limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop ≥ 2`, and this is proved in [Po79]. -/
theorem erdos_454.variants.two_le_limsup : 2 ≤ limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop := by
  apply Filter.le_limsup_of_frequently_le'
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨n, hNn, hn2, hn⟩ := P.exposed N
  refine ⟨n, hNn, ?_⟩
  have hP : (Prime : ℕ → Prop) = Nat.Prime := funext fun n => propext Nat.prime_iff.symm
  have hf : 2 * Nat.nth Nat.Prime n + 2 ≤ f n := by
    unfold f
    rw [if_neg (by omega)]
    have : Nonempty {i : Fin n // 0 < (i : ℕ)} := ⟨⟨⟨1, by omega⟩, Nat.one_pos⟩⟩
    apply le_ciInf
    rintro ⟨i, hi⟩
    rw [hP]
    exact hn i hi i.isLt
  have h2 : 2 ≤ f n - 2 * Nat.nth Nat.Prime n := by omega
  have e : ((f n - 2 * Nat.nth Nat.Prime n : ℕ) : ℕ∞) =
      (f n : ℕ∞) - 2 * (Nat.nth Nat.Prime n : ℕ∞) := by
    rw [ENat.natCast_sub, Nat.cast_mul]
    rfl
  simp only [hP]
  rw [← e]
  exact_mod_cast h2

end Erdos454

#print axioms Erdos454.erdos_454.variants.two_le_limsup
