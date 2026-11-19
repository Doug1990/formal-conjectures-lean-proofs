import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Tactic.LinearCombination

/-! Eisenstein's theorem (LittProblems/1.lean, `lam_litt.variants.eisenstein`). -/

open PowerSeries

namespace LamLitt

def ℤAdjoinInvNat (N : ℕ) : Subalgebra ℤ ℚ := Algebra.adjoin ℤ {(1 / N : ℚ)}

def IsCoeffIntegralAdjointInvNat (f : PowerSeries ℚ) (N : ℕ) : Prop :=
  ∀ n : ℕ, coeff n f ∈ ℤAdjoinInvNat N

namespace EI

/-- Every finite set of rationals lies in some `ℤ[1/N]`. -/
lemma fin_mem (T : Finset ℚ) : ∃ N : ℕ, ∀ q ∈ T, q ∈ ℤAdjoinInvNat N := by
  refine ⟨∏ q ∈ T, q.den, fun q hq => ?_⟩
  have hd : q.den ∣ ∏ q ∈ T, q.den := Finset.dvd_prod_of_mem _ hq
  have hN0 : ((∏ q ∈ T, q.den : ℕ) : ℚ) ≠ 0 := by
    push_cast
    exact Finset.prod_ne_zero_iff.2 (fun r _ => by exact_mod_cast r.den_pos.ne')
  generalize (∏ q ∈ T, q.den) = M at hd hN0 ⊢
  obtain ⟨e, he⟩ := hd
  have h1 : (1 / (M : ℚ) : ℚ) ∈ ℤAdjoinInvNat M := Algebra.subset_adjoin (Set.mem_singleton _)
  have h2 : ((e : ℕ) : ℚ) ∈ ℤAdjoinInvNat M := natCast_mem _ _
  have h3 : (q.num : ℚ) ∈ ℤAdjoinInvNat M := intCast_mem _ _
  have hMe : (M : ℚ) = q.den * e := by rw [he]; push_cast; ring
  have he0 : (e : ℚ) ≠ 0 := by intro h0; apply hN0; rw [hMe, h0, mul_zero]
  have hq' : (q.num : ℚ) * e * (1 / (M : ℚ)) = q := by
    calc (q.num : ℚ) * e * (1 / (M : ℚ)) = q.num / q.den * (e * (1 / e)) := by rw [hMe]; ring
      _ = q := by rw [mul_one_div_cancel he0, mul_one, Rat.num_div_den]
  have := mul_mem (mul_mem h3 h2) h1
  rwa [hq'] at this

variable (S : Subalgebra ℤ ℚ)

/-- coefficients below `b` lie in `S` -/
def Gd (h : ℚ⟦X⟧) (b : ℕ) : Prop := ∀ i < b, coeff i h ∈ S

lemma Gd_mul {a c : ℚ⟦X⟧} {b : ℕ} (ha : Gd S a b) (hc : Gd S c b) : Gd S (a * c) b := by
  intro i hi
  rw [coeff_mul]
  refine sum_mem fun x hx => mul_mem (ha _ ?_) (hc _ ?_)
  · have := Finset.mem_antidiagonal.1 hx; omega
  · have := Finset.mem_antidiagonal.1 hx; omega

lemma Gd_one (b : ℕ) : Gd S (1 : ℚ⟦X⟧) b := by
  intro i _
  rw [coeff_one]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

lemma Gd_pow {a : ℚ⟦X⟧} {b : ℕ} (ha : Gd S a b) (j : ℕ) : Gd S (a ^ j) b := by
  induction j with
  | zero => rw [pow_zero]; exact Gd_one S b
  | succ j ih => rw [pow_succ]; exact Gd_mul S ih ha

lemma Gd_add {a c : ℚ⟦X⟧} {b : ℕ} (ha : Gd S a b) (hc : Gd S c b) : Gd S (a + c) b := by
  intro i hi
  rw [map_add]
  exact add_mem (ha i hi) (hc i hi)

lemma Gd_sum {ι : Type*} (s : Finset ι) (F : ι → ℚ⟦X⟧) {b : ℕ}
    (h : ∀ i ∈ s, Gd S (F i) b) : Gd S (∑ i ∈ s, F i) b := by
  intro j hj
  rw [map_sum]
  exact sum_mem fun i hi => h i hi j hj

lemma Gd_Xpow (j b : ℕ) : Gd S ((X : ℚ⟦X⟧) ^ j) b := by
  intro i _
  rw [coeff_X_pow]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

lemma Gd_of {a : ℚ⟦X⟧} (ha : ∀ n, coeff n a ∈ S) (b : ℕ) : Gd S a b := fun i _ => ha i

lemma Gd_eval (Q : Polynomial ℚ⟦X⟧) (hQ : ∀ i n, coeff n (Q.coeff i) ∈ S)
    {x : ℚ⟦X⟧} {b : ℕ} (hx : Gd S x b) : Gd S (Q.eval x) b := by
  rw [Polynomial.eval_eq_sum_range]
  exact Gd_sum S _ _ fun i _ => Gd_mul S (Gd_of S (hQ i) b) (Gd_pow S hx i)

lemma coeff_alg (a : Polynomial ℚ) (n : ℕ) :
    coeff n (algebraMap (Polynomial ℚ) ℚ⟦X⟧ a) = a.coeff n := by
  rw [PowerSeries.algebraMap_apply', PowerSeries.coeff_map, Polynomial.coeff_coe,
    Algebra.algebraMap_self, RingHom.id_apply]

end EI

open EI in
theorem lam_litt.variants.eisenstein (f : PowerSeries ℚ) (hAlg : IsAlgebraic (Polynomial ℚ) f) :
    ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N := by
  classical
  -- a nonzero annihilating polynomial of minimal degree
  have hex : ∃ d, ∃ p : Polynomial (Polynomial ℚ), p ≠ 0 ∧ Polynomial.aeval f p = 0 ∧
      p.natDegree = d := by
    obtain ⟨p, hp, hpf⟩ := hAlg
    exact ⟨_, p, hp, hpf, rfl⟩
  obtain ⟨p, hp0, hpf, hpd⟩ := Nat.find_spec hex
  have hmin : ∀ q : Polynomial (Polynomial ℚ), q ≠ 0 → Polynomial.aeval f q = 0 →
      p.natDegree ≤ q.natDegree := by
    intro q hq hqf
    rw [hpd]; exact Nat.find_min' hex ⟨q, hq, hqf, rfl⟩
  have hinj : Function.Injective (algebraMap (Polynomial ℚ) ℚ⟦X⟧) := by
    intro a b hab
    exact Polynomial.ext fun n => by
      have := congrArg (coeff n) hab
      rwa [coeff_alg, coeff_alg] at this
  have hdeg : p.natDegree ≠ 0 := by
    intro h0
    have hpC := Polynomial.eq_C_of_natDegree_eq_zero h0
    rw [hpC, Polynomial.aeval_C] at hpf
    have : p.coeff 0 = 0 := hinj (by rw [hpf, map_zero])
    exact hp0 (by rw [hpC, this, map_zero])
  have hD : Polynomial.aeval f (Polynomial.derivative p) ≠ 0 := by
    intro h
    have hne : Polynomial.derivative p ≠ 0 := fun h' => hdeg (Polynomial.derivative_eq_zero.1 h')
    have h1 := hmin _ hne h
    have h2 := Polynomial.natDegree_derivative_lt hdeg
    omega
  -- move to polynomials over power series
  obtain ⟨P, hPdef⟩ : ∃ P : Polynomial ℚ⟦X⟧, P = p.map (algebraMap (Polynomial ℚ) ℚ⟦X⟧) :=
    ⟨_, rfl⟩
  have hP0 : P.eval f = 0 := by
    rw [hPdef, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hpf
  obtain ⟨D, hDdef⟩ : ∃ D : ℚ⟦X⟧, D = (Polynomial.derivative P).eval f := ⟨_, rfl⟩
  have hD' : D ≠ 0 := by
    rw [hDdef, hPdef, Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hD
  have hexk : ∃ k, coeff k D ≠ 0 := by
    by_contra h
    push Not at h
    exact hD' (PowerSeries.ext fun n => by rw [h n, map_zero])
  obtain ⟨k, hk1, hk2⟩ : ∃ k, coeff k D ≠ 0 ∧ ∀ i < k, coeff i D = 0 :=
    ⟨Nat.find hexk, Nat.find_spec hexk, fun i hi => not_not.1 (Nat.find_min hexk hi)⟩
  obtain ⟨D1, hD1⟩ : ∃ D1 : ℚ⟦X⟧, D1 = mk fun n => coeff (n + k) D := ⟨_, rfl⟩
  have hDD : D = X ^ k * D1 := by
    ext n
    rw [coeff_X_pow_mul']
    split_ifs with h
    · rw [hD1, coeff_mk, Nat.sub_add_cancel h]
    · exact hk2 n (by omega)
  -- f = A + X^(k+1) g
  obtain ⟨A, hA⟩ : ∃ A : ℚ⟦X⟧, A = ((trunc (k + 1) f : Polynomial ℚ) : ℚ⟦X⟧) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℚ⟦X⟧, g = mk fun n => coeff (n + (k + 1)) f := ⟨_, rfl⟩
  have hfA : f = A + X ^ (k + 1) * g := by
    ext n
    rw [map_add, coeff_X_pow_mul', hA, Polynomial.coeff_coe, coeff_trunc, hg]
    split_ifs <;> first | omega | (rw [coeff_mk, zero_add, Nat.sub_add_cancel (by omega)]) | simp
  have hfA' : f - A = X ^ (k + 1) * g := by linear_combination hfA
  -- Taylor expansion at A
  obtain ⟨T, hT⟩ : ∃ T : Polynomial ℚ⟦X⟧, T = Polynomial.taylor A P := ⟨_, rfl⟩
  have hTe : T.eval (X ^ (k + 1) * g) = 0 := by
    rw [hT, Polynomial.taylor_eval, add_comm, ← hfA]; exact hP0
  have hPdeg : P.natDegree = p.natDegree := by
    rw [hPdef, Polynomial.natDegree_map_eq_of_injective hinj]
  obtain ⟨d', hd'⟩ : ∃ d', p.natDegree + 1 = d' + 2 := ⟨p.natDegree - 1, by omega⟩
  have hsum : ∑ i ∈ Finset.range (d' + 2), T.coeff i * (X ^ (k + 1) * g) ^ i = 0 := by
    rw [← hTe, Polynomial.eval_eq_sum_range, hT, Polynomial.natDegree_taylor, hPdeg, hd']
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hsum
  simp only [zero_add, pow_one, pow_zero, mul_one] at hsum
  -- the linear coefficient
  obtain ⟨h, hh⟩ := Polynomial.sub_dvd_eval_sub f A (Polynomial.derivative P)
  obtain ⟨w, hwdef⟩ : ∃ w : ℚ⟦X⟧, w = D1 - X * (g * h) := ⟨_, rfl⟩
  have ht1 : T.coeff 1 = X ^ k * w := by
    rw [hT, Polynomial.taylor_coeff_one]
    have : (Polynomial.derivative P).eval A = D - (f - A) * h := by rw [hDdef, ← hh]; ring
    rw [this, hfA', hDD, hwdef]; ring
  have hc : constantCoeff w ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hwdef, map_sub, coeff_zero_X_mul, sub_zero, hD1,
      coeff_mk, zero_add]
    exact hk1
  obtain ⟨c, hcdef⟩ : ∃ c : ℚ, c = constantCoeff w := ⟨_, rfl⟩
  rw [← hcdef] at hc
  obtain ⟨w', hw'⟩ : ∃ w' : ℚ⟦X⟧, w' = mk fun n => coeff (n + 1) w := ⟨_, rfl⟩
  have hw : w = X * w' + C c := by rw [hw', hcdef]; exact eq_X_mul_shift_add_const w
  obtain ⟨H, hH⟩ : ∃ H : ℚ⟦X⟧, H = w' * g +
      ∑ i ∈ Finset.range d', X ^ (k * i + i) * T.coeff (i + 1 + 1) * g ^ (i + 1 + 1) :=
    ⟨_, rfl⟩
  have e1 : (X : ℚ⟦X⟧) ^ (k + 1 + k) * (C c * g + X * (w' * g)) =
      T.coeff 1 * (X ^ (k + 1) * g) := by
    rw [ht1, hw]; ring
  have e2 : (X : ℚ⟦X⟧) ^ (k + 1 + k) *
      (X * ∑ i ∈ Finset.range d', X ^ (k * i + i) * T.coeff (i + 1 + 1) * g ^ (i + 1 + 1)) =
      ∑ i ∈ Finset.range d', T.coeff (i + 1 + 1) * (X ^ (k + 1) * g) ^ (i + 1 + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul]
    have hx : (X : ℚ⟦X⟧) ^ ((k + 1) * (i + 1 + 1)) = X ^ (k + 1 + k) * (X * X ^ (k * i + i)) := by
      rw [← pow_succ', ← pow_add]; congr 1; ring
    rw [hx]; ring
  have key : (X : ℚ⟦X⟧) ^ (k + 1 + k) * (C c * g + X * H) = -T.coeff 0 := by
    have : (X : ℚ⟦X⟧) ^ (k + 1 + k) * (C c * g + X * H) =
        (X : ℚ⟦X⟧) ^ (k + 1 + k) * (C c * g + X * (w' * g)) +
        (X : ℚ⟦X⟧) ^ (k + 1 + k) *
        (X * ∑ i ∈ Finset.range d', X ^ (k * i + i) * T.coeff (i + 1 + 1) * g ^ (i + 1 + 1)) := by
      rw [hH]; ring
    rw [this, e1, e2]
    linear_combination hsum
  -- choose N
  obtain ⟨N, hN⟩ := fin_mem (insert c⁻¹ ((Finset.range (k + 1)).image (fun n => coeff n f) ∪
    (Finset.range (p.natDegree + 1)).biUnion (fun i =>
      (Finset.range ((p.coeff i).natDegree + 1)).image (fun n => (p.coeff i).coeff n))))
  refine ⟨N, ?_⟩
  have hcinv : c⁻¹ ∈ ℤAdjoinInvNat N := hN _ (Finset.mem_insert_self _ _)
  have hflow : ∀ n < k + 1, coeff n f ∈ ℤAdjoinInvNat N := fun n hn =>
    hN _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_range.2 hn))))
  have hpc : ∀ i n, (p.coeff i).coeff n ∈ ℤAdjoinInvNat N := by
    intro i n
    by_cases hi : i ≤ p.natDegree
    · by_cases hn : n ≤ (p.coeff i).natDegree
      · exact hN _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.2
          ⟨i, Finset.mem_range.2 (by omega), Finset.mem_image_of_mem _
            (Finset.mem_range.2 (by omega))⟩)))
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact zero_mem _
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega), Polynomial.coeff_zero]
      exact zero_mem _
  have hPc : ∀ i n, coeff n (P.coeff i) ∈ ℤAdjoinInvNat N := by
    intro i n; rw [hPdef, Polynomial.coeff_map, coeff_alg]; exact hpc i n
  have hAc : ∀ n, coeff n A ∈ ℤAdjoinInvNat N := by
    intro n
    rw [hA, Polynomial.coeff_coe, coeff_trunc]
    split_ifs with hn
    · exact hflow n hn
    · exact zero_mem _
  have hTc : ∀ j n, coeff n (T.coeff j) ∈ ℤAdjoinInvNat N := by
    intro j n
    rw [hT, Polynomial.taylor_coeff]
    refine Gd_eval _ _ ?_ (Gd_of _ hAc (n + 1)) n (Nat.lt_succ_self n)
    intro i m
    rw [Polynomial.hasseDeriv_coeff, ← nsmul_eq_mul, map_nsmul]
    exact nsmul_mem (hPc _ _) _
  have hwc : ∀ n, coeff n w' ∈ ℤAdjoinInvNat N := by
    intro n
    have := hTc 1 (n + 1 + k)
    rwa [ht1, coeff_X_pow_mul, hw, map_add, coeff_succ_X_mul, coeff_C,
      if_neg (by omega), add_zero] at this
  -- the recursion
  have hgc : ∀ n, coeff n g ∈ ℤAdjoinInvNat N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    have hgd : Gd (ℤAdjoinInvNat N) g n := fun i hi => ih i hi
    have hHd : Gd (ℤAdjoinInvNat N) H n := by
      rw [hH]
      refine Gd_add _ (Gd_mul _ (Gd_of _ hwc n) hgd) (Gd_sum _ _ _ fun i _ => ?_)
      exact Gd_mul _ (Gd_mul _ (Gd_Xpow _ _ _) (Gd_of _ (hTc _) n)) (Gd_pow _ hgd _)
    have hXH : coeff n (X * H) ∈ ℤAdjoinInvNat N := by
      cases n with
      | zero => rw [coeff_zero_X_mul]; exact zero_mem _
      | succ n => rw [coeff_succ_X_mul]; exact hHd n (Nat.lt_succ_self n)
    have hk := congrArg (coeff (n + (k + 1 + k))) key
    rw [coeff_X_pow_mul, map_add, coeff_C_mul, map_neg] at hk
    have hcg : c * coeff n g ∈ ℤAdjoinInvNat N := by
      have h2 : c * coeff n g = -coeff (n + (k + 1 + k)) (T.coeff 0) - coeff n (X * H) := by
        linear_combination hk
      rw [h2]; exact sub_mem (neg_mem (hTc 0 _)) hXH
    have h3 : coeff n g = c⁻¹ * (c * coeff n g) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [h3]; exact mul_mem hcinv hcg
  intro n
  by_cases hn : n < k + 1
  · exact hflow n hn
  · obtain ⟨d, rfl⟩ : ∃ d, n = d + (k + 1) := ⟨n - (k + 1), by omega⟩
    have := hgc d
    rwa [hg, coeff_mk] at this

end LamLitt

#print axioms LamLitt.lam_litt.variants.eisenstein
