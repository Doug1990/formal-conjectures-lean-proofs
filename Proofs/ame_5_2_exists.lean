import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

open scoped BigOperators

namespace OpenQuantumProblem35

abbrev Config (n d : ℕ) := Fin n → Fin d

abbrev StateVector (n d : ℕ) := EuclideanSpace ℂ (Config n d)

abbrev mkStateVector {n d : ℕ} (ψ : Config n d → ℂ) : StateVector n d :=
  WithLp.toLp 2 ψ

instance {n d : ℕ} : CoeFun (StateVector n d) (fun _ => Config n d → ℂ) where
  coe ψ := ψ.ofLp

def IsNormalized {n d : ℕ} (ψ : StateVector n d) : Prop :=
  ‖ψ‖ = 1

def permuteConfig {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) : Config n d :=
  fun i => x (π i)

def permuteState {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) : StateVector n d :=
  mkStateVector fun x => ψ (permuteConfig π x)

def combineFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        omega⟩

noncomputable def reducedDensityFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n) (ψ : StateVector n d) :
    Matrix (Config m d) (Config m d) ℂ :=
  fun x y =>
    ∑ z : Config (n - m) d,
      ψ (combineFirst (n := n) (d := d) m hm x z) *
        star (ψ (combineFirst (n := n) (d := d) m hm y z))

noncomputable def maximallyMixed (m d : ℕ) :
    Matrix (Config m d) (Config m d) ℂ :=
  ((Fintype.card (Config m d) : ℂ)⁻¹) •
    (1 : Matrix (Config m d) (Config m d) ℂ)

def HasMaximallyMixedFirstReduction {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (ψ : StateVector n d) : Prop :=
  reducedDensityFirst (n := n) (d := d) m hm ψ = maximallyMixed m d

def IsAME {n d : ℕ} (ψ : StateVector n d) : Prop :=
  IsNormalized ψ ∧
    ∀ π : Equiv.Perm (Fin n),
      HasMaximallyMixedFirstReduction (n := n) (d := d)
        (n / 2) (Nat.div_le_self n 2) (permuteState π ψ)

def ExistsAME (n d : ℕ) : Prop :=
  ∃ ψ : StateVector n d, IsAME (n := n) (d := d) ψ

namespace AME52

/-- quadratic form of the pentagon graph -/
def Q (y : Fin 5 → Fin 2) : Fin 2 :=
  y 0 * y 1 + y 1 * y 2 + y 2 * y 3 + y 3 * y 4 + y 4 * y 0

def s (y : Fin 5 → Fin 2) : ℤ := if Q y = 0 then 1 else -1

def upd (p q : Fin 5) (b0 b1 : Fin 2) (y : Fin 5 → Fin 2) : Fin 5 → Fin 2 :=
  fun i => if i = p then b0 else if i = q then b1 else y i

lemma core : ∀ p q : Fin 5, p ≠ q → ∀ a0 a1 b0 b1 : Fin 2,
    (∑ y ∈ Finset.univ.filter (fun y : Fin 5 → Fin 2 => y p = a0 ∧ y q = a1),
      s y * s (upd p q b0 b1 y)) = if a0 = b0 ∧ a1 = b1 then 8 else 0 := by
  decide +kernel

noncomputable def c : ℝ := (Real.sqrt 32)⁻¹

lemma c_sq : c * c = 1 / 32 := by
  have h : Real.sqrt 32 * Real.sqrt 32 = 32 := Real.mul_self_sqrt (by norm_num)
  have hpos : Real.sqrt 32 ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  unfold c
  rw [← mul_inv, h]
  norm_num

noncomputable def psi : StateVector 5 2 :=
  mkStateVector fun y => ((c : ℝ) : ℂ) * ((s y : ℤ) : ℂ)

lemma term (w : Config 5 2) : psi w = ((c : ℝ) : ℂ) * ((s w : ℤ) : ℂ) := rfl

lemma s_sq (w : Config 5 2) : s w * s w = 1 := by
  unfold s
  split_ifs <;> norm_num

lemma term_mul (w w' : Config 5 2) :
    psi w * star (psi w') = ((1 / 32 : ℝ) : ℂ) * ((s w * s w' : ℤ) : ℂ) := by
  rw [term, term]
  have hs : star ((s w' : ℤ) : ℂ) = ((s w' : ℤ) : ℂ) := by simp
  have hc : star ((c : ℝ) : ℂ) = ((c : ℝ) : ℂ) := by simp
  rw [star_mul', hs, hc]
  have hc2 : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = ((1 / 32 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, c_sq]
  push_cast at hc2 ⊢
  linear_combination ((s w : ℂ) * (s w' : ℂ)) * hc2

lemma psi_norm : IsNormalized psi := by
  have h2 : ‖psi‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hterm : ∀ y : Config 5 2, ‖psi y‖ ^ 2 = (1 / 32 : ℝ) := by
      intro y
      rw [term, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have : ‖((s y : ℤ) : ℂ)‖ = 1 := by
        unfold s
        split_ifs <;> simp
      rw [this, pow_two, c_sq]
      norm_num
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_const, Finset.card_univ]
    simp
  unfold IsNormalized
  have hn : 0 ≤ ‖psi‖ := norm_nonneg _
  nlinarith [h2, hn]

lemma split (j : Fin 5) :
    (∃ k : Fin 2, j = ⟨k.1, by omega⟩) ∨ (∃ k : Fin 3, j = ⟨2 + k.1, by omega⟩) := by
  fin_cases j
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨1, rfl⟩
  · exact Or.inr ⟨2, rfl⟩

def L (k : Fin 2) : Fin 5 := ⟨k.1, by omega⟩
def R (k : Fin 3) : Fin 5 := ⟨2 + k.1, by omega⟩

lemma comb_left (x : Config 2 2) (z : Config 3 2) (k : Fin 2) :
    combineFirst (n := 5) (d := 2) 2 (by decide) x z (L k) = x k := by
  simp [combineFirst, L, k.2]

lemma comb_right (x : Config 2 2) (z : Config 3 2) (k : Fin 3) :
    combineFirst (n := 5) (d := 2) 2 (by decide) x z (R k) = z k := by
  have : ¬ (2 + k.1 < 2) := by omega
  simp [combineFirst, R, this]

lemma L_ne : L 0 ≠ L 1 := by decide

lemma R_ne_L (k : Fin 3) (j : Fin 2) : R k ≠ L j := by
  intro h
  have := congrArg Fin.val h
  simp [R, L] at this
  omega

lemma cover (π : Equiv.Perm (Fin 5)) (i : Fin 5) :
    i = π.symm (L 0) ∨ i = π.symm (L 1) ∨ ∃ k, i = π.symm (R k) := by
  rcases split (π i) with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hi : i = π.symm (L k) := by
      rw [show L k = ⟨k.1, by omega⟩ from rfl, ← hk]
      simp
    fin_cases k
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
  · refine Or.inr (Or.inr ⟨k, ?_⟩)
    rw [show R k = ⟨2 + k.1, by omega⟩ from rfl, ← hk]
    simp

/-- the permuted configuration -/
def W (π : Equiv.Perm (Fin 5)) (a : Config 2 2) (z : Config 3 2) : Config 5 2 :=
  permuteConfig π (combineFirst (n := 5) (d := 2) 2 (by decide) a z)

lemma W_L (π : Equiv.Perm (Fin 5)) (a : Config 2 2) (z : Config 3 2) (k : Fin 2) :
    W π a z (π.symm (L k)) = a k := by
  simp only [W, permuteConfig, Equiv.apply_symm_apply]
  exact comb_left a z k

lemma W_R (π : Equiv.Perm (Fin 5)) (a : Config 2 2) (z : Config 3 2) (k : Fin 3) :
    W π a z (π.symm (R k)) = z k := by
  simp only [W, permuteConfig, Equiv.apply_symm_apply]
  exact comb_right a z k

lemma upd_W (π : Equiv.Perm (Fin 5)) (a b : Config 2 2) (z : Config 3 2) :
    upd (π.symm (L 0)) (π.symm (L 1)) (b 0) (b 1) (W π a z) = W π b z := by
  have hpq : π.symm (L 0) ≠ π.symm (L 1) := fun h => L_ne (π.symm.injective h)
  funext i
  unfold upd
  rcases cover π i with rfl | rfl | ⟨k, rfl⟩
  · rw [if_pos rfl, W_L]
  · rw [if_neg (Ne.symm hpq), if_pos rfl, W_L]
  · have h0 : π.symm (R k) ≠ π.symm (L 0) := fun h => R_ne_L k 0 (π.symm.injective h)
    have h1 : π.symm (R k) ≠ π.symm (L 1) := fun h => R_ne_L k 1 (π.symm.injective h)
    rw [if_neg h0, if_neg h1, W_R, W_R]

lemma bridge (π : Equiv.Perm (Fin 5)) (a b : Config 2 2) :
    (∑ z : Config 3 2, s (W π a z) * s (W π b z)) =
      ∑ y ∈ Finset.univ.filter (fun y : Fin 5 → Fin 2 =>
          y (π.symm (L 0)) = a 0 ∧ y (π.symm (L 1)) = a 1),
        s y * s (upd (π.symm (L 0)) (π.symm (L 1)) (b 0) (b 1) y) := by
  refine Finset.sum_bij' (fun z _ => W π a z) (fun y _ => fun k => y (π.symm (R k)))
    ?_ ?_ ?_ ?_ ?_
  · intro z _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨W_L π a z 0, W_L π a z 1⟩
  · intro y _
    exact Finset.mem_univ _
  · intro z _
    funext k
    exact W_R π a z k
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    funext i
    rcases cover π i with rfl | rfl | ⟨k, rfl⟩
    · rw [W_L, hy.1]
    · rw [W_L, hy.2]
    · rw [W_R]
  · intro z _
    rw [upd_W]

lemma eq_iff2 (a b : Config 2 2) : a = b ↔ (a 0 = b 0 ∧ a 1 = b 1) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    funext k
    fin_cases k
    · exact h0
    · exact h1

lemma main (π : Equiv.Perm (Fin 5)) :
    HasMaximallyMixedFirstReduction (n := 5) (d := 2) 2 (by decide) (permuteState π psi) := by
  have hpq : π.symm (L 0) ≠ π.symm (L 1) := fun h => L_ne (π.symm.injective h)
  unfold HasMaximallyMixedFirstReduction
  ext a b
  have hL : reducedDensityFirst (n := 5) (d := 2) 2 (by decide) (permuteState π psi) a b =
      ((1 / 32 : ℝ) : ℂ) * (((∑ z : Config 3 2, s (W π a z) * s (W π b z) : ℤ)) : ℂ) := by
    unfold reducedDensityFirst
    rw [Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    exact term_mul _ _
  rw [hL, bridge, core _ _ hpq]
  simp only [maximallyMixed, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a 0 = b 0 ∧ a 1 = b 1
  · rw [if_pos hab, if_pos ((eq_iff2 a b).mpr hab)]
    simp
    norm_num
  · rw [if_neg hab, if_neg (fun h => hab ((eq_iff2 a b).mp h))]
    simp

end AME52

theorem ame_5_2_exists : ExistsAME 5 2 := by
  refine ⟨AME52.psi, AME52.psi_norm, fun π => ?_⟩
  exact AME52.main π

end OpenQuantumProblem35

#print axioms OpenQuantumProblem35.ame_5_2_exists
