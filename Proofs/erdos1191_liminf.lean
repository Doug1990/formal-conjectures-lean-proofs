import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Real

/-- Restated from FormalConjecturesForMathlib/Combinatorics/Basic.lean. -/
def IsSidon {α : Type*} [Add α] (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Erdos1191

namespace LM

open Classical

/-- Elements of `A` in `[1, X]`. -/
noncomputable def S (A : Set ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun a => a ∈ A ∧ 1 ≤ a)

lemma mem_S {A : Set ℕ} {X a : ℕ} : a ∈ S A X ↔ a ∈ A ∧ 1 ≤ a ∧ a ≤ X := by
  simp only [S, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h3, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h1, h2⟩

lemma ncard_eq (A : Set ℕ) (X : ℕ) : (A ∩ Set.Icc 1 X).ncard = (S A X).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, mem_S]

lemma S_succ_mem {A : Set ℕ} {X : ℕ} (h : X + 1 ∈ A) : S A (X + 1) = insert (X + 1) (S A X) := by
  ext a
  simp only [Finset.mem_insert, mem_S]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hx : a = X + 1
    · exact Or.inl hx
    · exact Or.inr ⟨h1, h2, by omega⟩
  · rintro (rfl | ⟨h1, h2, h3⟩)
    · exact ⟨h, by omega, le_rfl⟩
    · exact ⟨h1, h2, by omega⟩

lemma S_succ_not {A : Set ℕ} {X : ℕ} (h : X + 1 ∉ A) : S A (X + 1) = S A X := by
  ext a
  simp only [mem_S]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rcases Nat.lt_or_ge a (X + 1) with h4 | h4
    · omega
    · exact absurd (show a = X + 1 by omega ▸ h1) h
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩

lemma notMem_S_succ {A : Set ℕ} {X : ℕ} : X + 1 ∉ S A X := by
  rw [mem_S]; omega

/-- Core Sidon count: pairs with small difference. -/
lemma pairs_le {A : Set ℕ} (hA : IsSidon A) (T : Finset ℕ) (hT : ∀ a ∈ T, a ∈ A)
    (D : Finset (ℕ × ℕ)) (hD : D ⊆ T ×ˢ T) (M : ℕ)
    (hM : ∀ p ∈ D, p.1 < p.2 + M ∧ p.2 < p.1 + M) :
    D.card ≤ T.card + 2 * M := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := D) (fun p : ℕ × ℕ => p.1 = p.2)
  have h1 : (D.filter (fun p => p.1 = p.2)).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
    · intro p hp
      have := hD (Finset.mem_filter.1 hp).1
      exact (Finset.mem_product.1 this).1
    · intro p hp p' hp' h
      have e1 := (Finset.mem_filter.1 hp).2
      have e2 := (Finset.mem_filter.1 hp').2
      simp only at h
      exact Prod.ext h (by rw [← e1, ← e2, h])
  have h2 : (D.filter (fun p => ¬ p.1 = p.2)).card ≤ 2 * M := by
    have key : (D.filter (fun p => ¬ p.1 = p.2)).card ≤ (Finset.range (2 * M)).card := by
      refine Finset.card_le_card_of_injOn (fun p => p.1 + M - p.2) ?_ ?_
      · rintro ⟨a, b⟩ hp
        have hp1 := (Finset.mem_filter.1 hp).1
        have := hM _ hp1
        simp only at this
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' h
        have hp1 := (Finset.mem_filter.1 hp)
        have hp2 := (Finset.mem_filter.1 hp')
        have m1 := Finset.mem_product.1 (hD hp1.1)
        have m2 := Finset.mem_product.1 (hD hp2.1)
        have b1 := hM _ hp1.1
        have b2 := hM _ hp2.1
        simp only at h m1 m2 b1 b2 hp1 hp2
        have hs : a + b' = a' + b := by omega
        rcases hA a (hT _ m1.1) a' (hT _ m2.1) b' (hT _ m2.2) b (hT _ m1.2) hs with
          ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]
        · exact absurd e1 hp1.2
    simpa using key
  omega

lemma fib_eq (T : Finset ℕ) (M X : ℕ) (hT : ∀ a ∈ T, 1 ≤ a ∧ a ≤ X) :
    ((T ×ˢ T).filter (fun p => (p.1 - 1) / M = (p.2 - 1) / M)).card =
      ∑ s ∈ Finset.range X, ((T.filter (fun a => (a - 1) / M = s)).card) ^ 2 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p => (p.1 - 1) / M) (t := Finset.range X)]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [sq, ← Finset.card_product]
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hq⟩, hs⟩
      exact ⟨⟨ha, hs⟩, hb, hq.symm.trans hs⟩
    · rintro ⟨⟨ha, hs⟩, hb, hs'⟩
      exact ⟨⟨⟨ha, hb⟩, hs.trans hs'.symm⟩, hs⟩
  · rintro ⟨a, b⟩ hp
    have h1 := hT a (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1
    simp only [Finset.coe_range, Set.mem_Iio]
    have := Nat.div_le_self (a - 1) M
    omega

lemma sq_sum {A : Set ℕ} (hA : IsSidon A) (M X : ℕ) (hM : 0 < M) :
    ∑ s ∈ Finset.range X, (((S A X).filter (fun a => (a - 1) / M = s)).card) ^ 2
      ≤ (S A X).card + 2 * M := by
  rw [← fib_eq (S A X) M X (fun a ha => ⟨(mem_S.1 ha).2.1, (mem_S.1 ha).2.2⟩)]
  refine pairs_le hA (S A X) (fun a ha => (mem_S.1 ha).1) _ (Finset.filter_subset _ _) M ?_
  rintro ⟨a, b⟩ hp
  have hq := (Finset.mem_filter.1 hp).2
  have hab := Finset.mem_product.1 (Finset.mem_filter.1 hp).1
  have ha1 := (mem_S.1 hab.1).2.1
  have hb1 := (mem_S.1 hab.2).2.1
  simp only at hq ha1 hb1 ⊢
  have ha := Nat.div_add_mod (a - 1) M
  have hb := Nat.div_add_mod (b - 1) M
  have ra := Nat.mod_lt (a - 1) hM
  have rb := Nat.mod_lt (b - 1) hM
  rw [hq] at ha
  generalize M * ((b - 1) / M) = t at ha hb
  omega

lemma point (M a : ℕ) (hMa : M < a) :
    Real.sqrt M * (Real.sqrt a)⁻¹ ≤ Real.sqrt 2 * (Real.sqrt ((((a - 1) / M : ℕ) : ℝ) + 1))⁻¹ := by
  have hnat : M * ((a - 1) / M + 1) ≤ 2 * a := by
    have := Nat.div_mul_le_self (a - 1) M
    rw [Nat.mul_add, mul_one, mul_comm]
    generalize (a - 1) / M * M = t at this ⊢
    omega
  have hreal : (M : ℝ) * ((((a - 1) / M : ℕ) : ℝ) + 1) ≤ 2 * (a : ℝ) := by
    exact_mod_cast hnat
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity),
    ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hreal

lemma weighted (A : Set ℕ) (M X : ℕ) :
    Real.sqrt M * ∑ a ∈ (S A X).filter (fun a => M < a), (Real.sqrt a)⁻¹ ≤
      Real.sqrt 2 * ∑ s ∈ Finset.range X,
        (((S A X).filter (fun a => (a - 1) / M = s)).card : ℝ) * (Real.sqrt ((s : ℝ) + 1))⁻¹ := by
  have hfib : ∑ s ∈ Finset.range X,
        (((S A X).filter (fun a => (a - 1) / M = s)).card : ℝ) * (Real.sqrt ((s : ℝ) + 1))⁻¹
      = ∑ a ∈ S A X, (Real.sqrt ((((a - 1) / M : ℕ) : ℝ) + 1))⁻¹ := by
    have hm : ∀ a ∈ S A X, (fun a => (a - 1) / M) a ∈ Finset.range X := by
      intro a ha
      have h1 := mem_S.1 ha
      simp only [Finset.mem_range]
      have := Nat.div_le_self (a - 1) M
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.1 ha).2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [hfib, Finset.mul_sum, Finset.mul_sum]
  calc ∑ a ∈ (S A X).filter (fun a => M < a), Real.sqrt M * (Real.sqrt a)⁻¹
      ≤ ∑ a ∈ (S A X).filter (fun a => M < a),
          Real.sqrt 2 * (Real.sqrt ((((a - 1) / M : ℕ) : ℝ) + 1))⁻¹ :=
        Finset.sum_le_sum (fun a ha => point M a (Finset.mem_filter.1 ha).2)
    _ ≤ ∑ a ∈ S A X, Real.sqrt 2 * (Real.sqrt ((((a - 1) / M : ℕ) : ℝ) + 1))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)

lemma harm_eq (X : ℕ) : (harmonic X : ℝ) = ∑ s ∈ Finset.range X, ((s : ℝ) + 1)⁻¹ := by
  simp [harmonic]

lemma block {A : Set ℕ} (hA : IsSidon A) (M X : ℕ) (hM : 0 < M) :
    (M : ℝ) * (∑ a ∈ (S A X).filter (fun a => M < a), (Real.sqrt a)⁻¹) ^ 2 ≤
      2 * (((S A X).card : ℝ) + 2 * M) * (harmonic X : ℝ) := by
  set G := ∑ a ∈ (S A X).filter (fun a => M < a), (Real.sqrt a)⁻¹
  set P := ∑ s ∈ Finset.range X,
        (((S A X).filter (fun a => (a - 1) / M = s)).card : ℝ) * (Real.sqrt ((s : ℝ) + 1))⁻¹
  have hG : 0 ≤ G := Finset.sum_nonneg (fun _ _ => by positivity)
  have hw := weighted A M X
  have hsq : (Real.sqrt M * G) ^ 2 ≤ (Real.sqrt 2 * P) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hw 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hsq
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range X)
    (fun s => (((S A X).filter (fun a => (a - 1) / M = s)).card : ℝ))
    (fun s => (Real.sqrt ((s : ℝ) + 1))⁻¹)
  have hg : ∑ s ∈ Finset.range X, ((Real.sqrt ((s : ℝ) + 1))⁻¹) ^ 2 = (harmonic X : ℝ) := by
    rw [harm_eq]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [hg] at cs
  have hn : ∑ s ∈ Finset.range X, ((((S A X).filter (fun a => (a - 1) / M = s)).card : ℝ)) ^ 2
      ≤ ((S A X).card : ℝ) + 2 * M := by
    exact_mod_cast sq_sum hA M X hM
  have hH : (0 : ℝ) ≤ harmonic X := by rw [harm_eq]; positivity
  have := mul_le_mul_of_nonneg_right hn hH
  nlinarith

lemma ind (A : Set ℕ) (c L : ℝ) (y : ℕ) :
    ∀ X, y ≤ X → (∀ x, y < x → x ≤ X → x ∈ A →
      c * Real.sqrt x ≤ ((S A x).card : ℝ) * Real.sqrt L) →
    c * ((harmonic (S A X).card : ℝ) - harmonic (S A y).card) ≤
      Real.sqrt L * ∑ a ∈ (S A X).filter (fun a => y < a), (Real.sqrt a)⁻¹ := by
  intro X hX
  induction X, hX using Nat.le_induction with
  | base =>
    intro _
    have : (S A y).filter (fun a => y < a) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro a ha
      have := mem_S.1 ha
      omega
    rw [this]
    simp
  | succ X hyX ih =>
    intro hyp
    have ih' := ih (fun x h1 h2 hx => hyp x h1 (by omega) hx)
    by_cases hX1 : X + 1 ∈ A
    · have h1 := hyp (X + 1) (by omega) le_rfl hX1
      rw [S_succ_mem hX1, Finset.card_insert_of_notMem notMem_S_succ] at h1
      have key : c * (((S A X).card : ℝ) + 1)⁻¹ ≤ Real.sqrt L * (Real.sqrt ((X : ℝ) + 1))⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast at h1
        linarith
      rw [S_succ_mem hX1, Finset.card_insert_of_notMem notMem_S_succ, Finset.filter_insert,
        if_pos (by omega : y < X + 1), Finset.sum_insert (by simp [notMem_S_succ]),
        harmonic_succ]
      push_cast
      rw [mul_add]
      have e : c * ((harmonic (S A X).card : ℝ) + (((S A X).card : ℝ) + 1)⁻¹ -
          harmonic (S A y).card) = c * ((harmonic (S A X).card : ℝ) - harmonic (S A y).card) +
          c * (((S A X).card : ℝ) + 1)⁻¹ := by ring
      rw [e]
      linarith
    · rw [S_succ_not hX1]
      exact ih'

lemma log_le_half (L : ℝ) (hL : 0 < L) : Real.log L ≤ L / 2 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < L / 2 by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  rw [Real.log_div hL.ne' (by norm_num)] at h1
  linarith

lemma final_arith (K m L G H c hK hm' : ℝ) (hK1 : 1 ≤ K) (hm0 : 0 ≤ m) (hL : 0 < L)
    (_hG : 0 ≤ G) (hc : 25 ≤ c) (hlogK : 8 + L / 4 ≤ Real.log K)
    (hm : m * m ≤ m + 2 * (K + 1)) (hhK : Real.log (K + 1) ≤ hK) (hhm : hm' ≤ 1 + Real.log m)
    (hind : c * (hK - hm') ≤ Real.sqrt L * G) (hblock : K * G ^ 2 ≤ 2 * (K + 2 * K) * H)
    (hH : H ≤ 1 + L) : False := by
  have hsK : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hK1
  have hm3 : m ≤ 3 * Real.sqrt K := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_pos (sub_pos.2 hcon) (show 0 < m + 3 * Real.sqrt K - 1 by linarith),
      mul_nonneg (sub_nonneg.2 hs1) (show 0 ≤ 7 * Real.sqrt K + 4 by linarith)]
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.add_one_le_exp 2
    rw [Real.log_le_iff_le_exp (by norm_num)]
    linarith
  have hlogm : Real.log m ≤ 2 + Real.log K / 2 := by
    rcases hm0.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]
      have := Real.log_nonneg hK1
      linarith
    · have := Real.log_le_log h0 hm3
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by linarith)] at this
      linarith
  have hlogK1 : Real.log K ≤ Real.log (K + 1) := Real.log_le_log (by linarith) (by linarith)
  have hD : 1 + L / 8 ≤ hK - hm' := by linarith
  have hG2 : G ^ 2 ≤ 6 * (1 + L) := by
    have : K * G ^ 2 ≤ K * (6 * (1 + L)) := by
      nlinarith [mul_le_mul_of_nonneg_left hH (show 0 ≤ K by linarith)]
    exact le_of_mul_le_mul_left this (by linarith)
  have hsq : (c * (hK - hm')) ^ 2 ≤ (Real.sqrt L * G) ^ 2 :=
    pow_le_pow_left₀ (by nlinarith) hind 2
  have e : (Real.sqrt L * G) ^ 2 = L * G ^ 2 := by rw [mul_pow, Real.sq_sqrt hL.le]
  have h1 : c * (1 + L / 8) ≤ c * (hK - hm') := mul_le_mul_of_nonneg_left hD (by linarith)
  have h2 : (c * (1 + L / 8)) ^ 2 ≤ (c * (hK - hm')) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h3 : L * G ^ 2 ≤ L * (6 * (1 + L)) := mul_le_mul_of_nonneg_left hG2 hL.le
  have h4 : (25 * (1 + L / 8)) ^ 2 ≤ (c * (1 + L / 8)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hc (by positivity)) 2
  nlinarith

lemma conv {A : Set ℕ} {c : ℝ} {x : ℕ} (hx : 1 ≤ x)
    (h : c < (A ∩ Set.Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ)) :
    c * Real.sqrt x ≤ ((S A x).card : ℝ) * Real.sqrt (Real.log x) := by
  rw [ncard_eq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have hx' : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by exact_mod_cast hx)
  rw [div_mul_eq_mul_div, lt_div_iff₀ hx'] at h
  linarith

lemma exists_big {A : Set ℕ} (hA : A.Infinite) (N : ℕ) : ∃ X, N ≤ (S A X).card := by
  obtain ⟨t, ht, hcard⟩ := hA.exists_subset_card_eq (N + 1)
  refine ⟨t.sup id, ?_⟩
  have hsub : t.erase 0 ⊆ S A (t.sup id) := by
    intro a ha
    rw [Finset.mem_erase] at ha
    rw [mem_S]
    exact ⟨ht ha.2, Nat.one_le_iff_ne_zero.2 ha.1, Finset.le_sup (f := id) ha.2⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := t) (a := 0)
  omega

lemma card_S_le (A : Set ℕ) (X : ℕ) : (S A X).card ≤ X := by
  have hsub : S A X ⊆ Finset.Icc 1 X := fun a ha => by
    have := mem_S.1 ha
    exact Finset.mem_Icc.2 ⟨this.2.1, this.2.2⟩
  have := Finset.card_le_card hsub
  simpa using this

lemma triv {A : Set ℕ} (hA : IsSidon A) (K : ℕ) :
    (S A K).card * (S A K).card ≤ (S A K).card + 2 * (K + 1) := by
  have := pairs_le hA (S A K) (fun a ha => (mem_S.1 ha).1) (S A K ×ˢ S A K) subset_rfl (K + 1) ?_
  · rwa [Finset.card_product] at this
  · rintro ⟨a, b⟩ hp
    have hab := Finset.mem_product.1 hp
    have h1 := mem_S.1 hab.1
    have h2 := mem_S.1 hab.2
    simp only at h1 h2 ⊢
    omega

end LM

open LM in
theorem erdos_1191.variants.liminf_le {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    ∃ c > (0 : ℝ), liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop ≤
        ENNReal.ofReal c := by
  refine ⟨Real.exp 8, Real.exp_pos 8, ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hev := Filter.eventually_lt_of_lt_liminf hcon
  rw [Filter.eventually_atTop] at hev
  obtain ⟨x1, hx1⟩ := hev
  have hc25 : 25 ≤ Real.exp 8 := by
    have h4 := Real.add_one_le_exp 4
    have e8 : Real.exp 8 = Real.exp 4 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
    rw [e8]
    nlinarith
  have hlogc : Real.log (Real.exp 8) = 8 := Real.log_exp 8
  have hyp : ∀ x, max x1 1 ≤ x →
      Real.exp 8 * Real.sqrt x ≤ ((S A x).card : ℝ) * Real.sqrt (Real.log x) := by
    intro x hx
    have h := hx1 x (le_trans (le_max_left _ _) hx)
    have h' := (ENNReal.ofReal_lt_ofReal_iff'.1 h).1
    exact conv (le_trans (le_max_right _ _) hx) h'
  obtain ⟨X, hX⟩ := exists_big hAinf (max x1 1 + 2)
  have hKX : (S A X).card ≤ X := card_S_le A X
  have hm1 := le_max_right x1 1
  have hXr : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hL : 0 < Real.log X := Real.log_pos hXr
  have hK0 : 0 < (S A X).card := by omega
  have hblock := block hAsid (S A X).card X hK0
  have hind := ind A (Real.exp 8) (Real.log X) (S A X).card X hKX (fun x h1 h2 _ => by
    have hx := hyp x (by omega)
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hlog : Real.log x ≤ Real.log X := Real.log_le_log hxpos (by exact_mod_cast h2)
    have hs : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hlog
    have hk : (0 : ℝ) ≤ (S A x).card := by positivity
    linarith [mul_le_mul_of_nonneg_left hs hk])
  have htriv := triv hAsid (S A X).card
  have hfX := hyp X (by omega)
  have hK1 : (1 : ℝ) ≤ (S A X).card := by exact_mod_cast hK0
  have hlogK : 8 + Real.log X / 4 ≤ Real.log (S A X).card := by
    have hpos : 0 < Real.exp 8 * Real.sqrt X := by positivity
    have hl := Real.log_le_log hpos hfX
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by positivity), Real.log_sqrt hL.le, hlogc] at hl
    have := log_le_half (Real.log X) hL
    linarith
  have hm : ((S A (S A X).card).card : ℝ) * (S A (S A X).card).card ≤
      (S A (S A X).card).card + 2 * (((S A X).card : ℝ) + 1) := by
    exact_mod_cast htriv
  have hhK := log_add_one_le_harmonic (S A X).card
  push_cast at hhK
  exact final_arith _ _ _ _ _ _ _ _ hK1 (by positivity) hL
    (Finset.sum_nonneg (fun _ _ => by positivity)) hc25 hlogK hm hhK
    (harmonic_le_one_add_log _) hind hblock (harmonic_le_one_add_log X)

#print axioms erdos_1191.variants.liminf_le

namespace LM

lemma core {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) (x0 : ℕ) (hx0 : 1 ≤ x0)
    (hyp : ∀ x, x0 ≤ x →
      Real.exp 8 * Real.sqrt x ≤ ((S A x).card : ℝ) * Real.sqrt (Real.log x)) : False := by
  have hc25 : 25 ≤ Real.exp 8 := by
    have h4 := Real.add_one_le_exp 4
    have e8 : Real.exp 8 = Real.exp 4 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
    rw [e8]
    nlinarith
  have hlogc : Real.log (Real.exp 8) = 8 := Real.log_exp 8
  obtain ⟨X, hX⟩ := exists_big hAinf (x0 + 2)
  have hKX : (S A X).card ≤ X := card_S_le A X
  have hXr : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hL : 0 < Real.log X := Real.log_pos hXr
  have hK0 : 0 < (S A X).card := by omega
  have hblock := block hAsid (S A X).card X hK0
  have hind := ind A (Real.exp 8) (Real.log X) (S A X).card X hKX (fun x h1 h2 _ => by
    have hx := hyp x (by omega)
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hlog : Real.log x ≤ Real.log X := Real.log_le_log hxpos (by exact_mod_cast h2)
    have hs : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hlog
    have hk : (0 : ℝ) ≤ (S A x).card := by positivity
    linarith [mul_le_mul_of_nonneg_left hs hk])
  have htriv := triv hAsid (S A X).card
  have hfX := hyp X (by omega)
  have hK1 : (1 : ℝ) ≤ (S A X).card := by exact_mod_cast hK0
  have hlogK : 8 + Real.log X / 4 ≤ Real.log (S A X).card := by
    have hpos : 0 < Real.exp 8 * Real.sqrt X := by positivity
    have hl := Real.log_le_log hpos hfX
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by positivity), Real.log_sqrt hL.le, hlogc] at hl
    have := log_le_half (Real.log X) hL
    linarith
  have hm : ((S A (S A X).card).card : ℝ) * (S A (S A X).card).card ≤
      (S A (S A X).card).card + 2 * (((S A X).card : ℝ) + 1) := by
    exact_mod_cast htriv
  have hhK := log_add_one_le_harmonic (S A X).card
  push_cast at hhK
  exact final_arith _ _ _ _ _ _ _ _ hK1 (by positivity) hL
    (Finset.sum_nonneg (fun _ _ => by positivity)) hc25 hlogK hm hhK
    (harmonic_le_one_add_log _) hind hblock (harmonic_le_one_add_log X)

lemma conv158 {A : Set ℕ} {x : ℕ} (hx : 2 ≤ x)
    (h : 2 * Real.exp 8 < (A ∩ Set.Iio x).ncard * (x : ℝ) ^ (-1 / 2 : ℝ) *
      Real.log x ^ (1 / 2 : ℝ)) :
    Real.exp 8 * Real.sqrt x ≤ ((S A x).card : ℝ) * Real.sqrt (Real.log x) := by
  have hle : (A ∩ Set.Iio x).ncard ≤ (S A x).card + 1 := by
    have hsub : A ∩ Set.Iio x ⊆ insert 0 ((S A x : Finset ℕ) : Set ℕ) := by
      rintro a ⟨ha, hax⟩
      rw [Set.mem_Iio] at hax
      by_cases h0 : a = 0
      · exact Or.inl h0
      · right
        rw [Finset.mem_coe, mem_S]
        exact ⟨ha, by omega, by omega⟩
    calc (A ∩ Set.Iio x).ncard ≤ (insert 0 ((S A x : Finset ℕ) : Set ℕ)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ((S A x : Finset ℕ) : Set ℕ).ncard + 1 := Set.ncard_insert_le _ _
      _ = (S A x).card + 1 := by rw [Set.ncard_coe_finset]
  have hxr : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hxr
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hxr.le, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow] at h
  have e : ((A ∩ Set.Iio x).ncard : ℝ) * (Real.sqrt x)⁻¹ * Real.sqrt (Real.log x) =
      ((A ∩ Set.Iio x).ncard : ℝ) * Real.sqrt (Real.log x) / Real.sqrt x := by
    rw [div_eq_mul_inv]; ring
  rw [e, lt_div_iff₀ hsx] at h
  have hler : ((A ∩ Set.Iio x).ncard : ℝ) ≤ (S A x).card + 1 := by exact_mod_cast hle
  have hsL : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hler hsL
  have he : 1 ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
  rcases Nat.eq_zero_or_pos (S A x).card with hk | hk
  · exfalso
    rw [hk] at h1
    have hlogx : Real.log x ≤ x := by
      have := Real.log_le_sub_one_of_pos hxr
      linarith
    have : Real.sqrt (Real.log x) ≤ Real.sqrt x := Real.sqrt_le_sqrt hlogx
    push_cast at h1
    nlinarith
  · have hk1 : (1 : ℝ) ≤ (S A x).card := by exact_mod_cast hk
    have h2 := mul_le_mul_of_nonneg_right (show ((S A x).card : ℝ) + 1 ≤ 2 * (S A x).card by
      linarith) hsL
    nlinarith

end LM

end Erdos1191

namespace Erdos158

open Erdos1191.LM in
theorem erdos_158.variants.isSidon' {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    liminf (fun N ↦ ENNReal.ofReal ((A ∩ .Iio N).ncard * N ^ (- 1 / 2 : ℝ) * log N ^ (1 / 2 : ℝ)))
      atTop < ⊤ := by
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  have hlt := (ENNReal.ofReal_lt_top : ENNReal.ofReal (2 * Real.exp 8) < ⊤)
  rw [← hcon] at hlt
  have hev := Filter.eventually_lt_of_lt_liminf hlt
  rw [Filter.eventually_atTop] at hev
  obtain ⟨x1, hx1⟩ := hev
  refine core hAinf hAsid (max x1 2) (by omega) (fun x hx => ?_)
  have h := (ENNReal.ofReal_lt_ofReal_iff'.1 (hx1 x (le_trans (le_max_left _ _) hx))).1
  exact conv158 (le_trans (le_max_right _ _) hx) h

#print axioms erdos_158.variants.isSidon'

end Erdos158
