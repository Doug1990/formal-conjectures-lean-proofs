import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
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

namespace AME62

/-- wheel graph: cycle 0-1-2-3-4-0, hub 5 -/
def G (j i : Fin 6) : Fin 2 :=
  if i ≠ j ∧ (i.1 = 5 ∨ j.1 = 5 ∨ (i.1 + 1) % 5 = j.1 ∨ (j.1 + 1) % 5 = i.1) then 1 else 0

def Q (y : Fin 6 → Fin 2) : Fin 2 :=
  y 0 * y 1 + y 1 * y 2 + y 2 * y 3 + y 3 * y 4 + y 4 * y 0 +
    y 5 * (y 0 + y 1 + y 2 + y 3 + y 4)

def N (j : Fin 6) (y : Fin 6 → Fin 2) : Fin 2 := ∑ i, G j i * y i

def flip (j : Fin 6) (y : Fin 6 → Fin 2) : Fin 6 → Fin 2 :=
  Function.update y j (y j + 1)

lemma Q_flip : ∀ j : Fin 6, ∀ y : Fin 6 → Fin 2, Q (flip j y) = Q y + N j y := by
  decide +kernel

lemma rank : ∀ p q r : Fin 6, p ≠ q → p ≠ r → q ≠ r → ∀ c0 c1 c2 : Fin 2,
    ¬ (c0 = 0 ∧ c1 = 0 ∧ c2 = 0) →
    ∃ j : Fin 6, j ≠ p ∧ j ≠ q ∧ j ≠ r ∧ G j p * c0 + G j q * c1 + G j r * c2 = 1 := by
  decide +kernel

def sg (x : Fin 2) : ℤ := if x = 0 then 1 else -1

lemma sg_add : ∀ x y : Fin 2, sg (x + y) = sg x * sg y := by decide
lemma sg_succ : ∀ x : Fin 2, sg (x + 1) = - sg x := by decide
lemma sg_sq : ∀ x : Fin 2, sg x * sg x = 1 := by decide
lemma fin2_ne : ∀ x : Fin 2, x + 1 ≠ x := by decide
lemma fin2_11 : ∀ x : Fin 2, x + 1 + 1 = x := by decide

def s (y : Fin 6 → Fin 2) : ℤ := sg (Q y)

lemma s_flip (j : Fin 6) (y : Fin 6 → Fin 2) : s (flip j y) = s y * sg (N j y) := by
  unfold s
  rw [Q_flip, sg_add]

lemma s_sq (w : Config 6 2) : s w * s w = 1 := sg_sq _

noncomputable def c : ℝ := 1 / 8

lemma c_sq : c * c = 1 / 64 := by
  unfold c
  norm_num

noncomputable def psi : StateVector 6 2 :=
  mkStateVector fun y => ((c : ℝ) : ℂ) * ((s y : ℤ) : ℂ)

lemma term (w : Config 6 2) : psi w = ((c : ℝ) : ℂ) * ((s w : ℤ) : ℂ) := rfl

lemma term_mul (w w' : Config 6 2) :
    psi w * star (psi w') = ((1 / 64 : ℝ) : ℂ) * ((s w * s w' : ℤ) : ℂ) := by
  rw [term, term]
  have hs : star ((s w' : ℤ) : ℂ) = ((s w' : ℤ) : ℂ) := by simp
  have hc : star ((c : ℝ) : ℂ) = ((c : ℝ) : ℂ) := by simp
  rw [star_mul', hs, hc]
  have hc2 : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = ((1 / 64 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, c_sq]
  push_cast at hc2 ⊢
  linear_combination ((s w : ℂ) * (s w' : ℂ)) * hc2

lemma psi_norm : IsNormalized psi := by
  have h2 : ‖psi‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hterm : ∀ y : Config 6 2, ‖psi y‖ ^ 2 = (1 / 64 : ℝ) := by
      intro y
      rw [term, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have : ‖((s y : ℤ) : ℂ)‖ = 1 := by
        unfold s sg
        split_ifs <;> simp
      rw [this, pow_two, c_sq]
      norm_num
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_const, Finset.card_univ]
    simp
  unfold IsNormalized
  have hn : 0 ≤ ‖psi‖ := norm_nonneg _
  nlinarith [h2, hn]

def L (k : Fin 3) : Fin 6 := ⟨k.1, by omega⟩
def R (k : Fin 3) : Fin 6 := ⟨3 + k.1, by omega⟩

lemma split (j : Fin 6) : (∃ m : Fin 3, j = L m) ∨ (∃ k : Fin 3, j = R k) := by
  fin_cases j
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inl ⟨2, rfl⟩
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨1, rfl⟩
  · exact Or.inr ⟨2, rfl⟩

lemma comb_left (x : Config 3 2) (z : Config 3 2) (k : Fin 3) :
    combineFirst (n := 6) (d := 2) 3 (by decide) x z (L k) = x k := by
  simp [combineFirst, L, k.2]

lemma comb_right (x : Config 3 2) (z : Config 3 2) (k : Fin 3) :
    combineFirst (n := 6) (d := 2) 3 (by decide) x z (R k) = z k := by
  have : ¬ (3 + k.1 < 3) := by omega
  simp [combineFirst, R, this]

lemma R_inj {k k' : Fin 3} (h : R k = R k') : k = k' := by
  apply Fin.ext
  have := congrArg Fin.val h
  simp [R] at this
  exact this

lemma cover (π : Equiv.Perm (Fin 6)) (i : Fin 6) :
    (∃ m, i = π.symm (L m)) ∨ ∃ k, i = π.symm (R k) := by
  rcases split (π i) with ⟨m, hm⟩ | ⟨k, hk⟩
  · exact Or.inl ⟨m, by rw [← hm]; simp⟩
  · exact Or.inr ⟨k, by rw [← hk]; simp⟩

def W (π : Equiv.Perm (Fin 6)) (a : Config 3 2) (z : Config 3 2) : Config 6 2 :=
  permuteConfig π (combineFirst (n := 6) (d := 2) 3 (by decide) a z)

lemma W_apply (π : Equiv.Perm (Fin 6)) (a : Config 3 2) (z : Config 3 2) (i : Fin 6) :
    W π a z (π.symm i) = combineFirst (n := 6) (d := 2) 3 (by decide) a z i := by
  simp only [W, permuteConfig, Equiv.apply_symm_apply]

lemma W_L (π : Equiv.Perm (Fin 6)) (a : Config 3 2) (z : Config 3 2) (k : Fin 3) :
    W π a z (π.symm (L k)) = a k := by
  rw [W_apply]; exact comb_left a z k

lemma W_R (π : Equiv.Perm (Fin 6)) (a : Config 3 2) (z : Config 3 2) (k : Fin 3) :
    W π a z (π.symm (R k)) = z k := by
  rw [W_apply]; exact comb_right a z k

lemma N_W (π : Equiv.Perm (Fin 6)) (j : Fin 6) (a z : Config 3 2) :
    N j (W π a z) = (∑ m : Fin 3, G j (π.symm (L m)) * a m) +
      ∑ k : Fin 3, G j (π.symm (R k)) * z k := by
  unfold N
  rw [← Equiv.sum_comp π.symm]
  simp only [W_apply]
  have h := Fin.sum_univ_add (a := 3) (b := 3)
    (fun i : Fin 6 => G j (π.symm i) * combineFirst (n := 6) (d := 2) 3 (by decide) a z i)
  refine h.trans ?_
  congr 1

def fl (k : Fin 3) (z : Config 3 2) : Config 3 2 := Function.update z k (z k + 1)

lemma W_fl (π : Equiv.Perm (Fin 6)) (a z : Config 3 2) (k : Fin 3) :
    W π a (fl k z) = flip (π.symm (R k)) (W π a z) := by
  funext i
  unfold flip
  rcases cover π i with ⟨m, rfl⟩ | ⟨k', rfl⟩
  · have hne : π.symm (L m) ≠ π.symm (R k) := by
      intro h
      have := congrArg Fin.val (π.symm.injective h)
      simp [L, R] at this
      omega
    rw [Function.update_of_ne hne, W_L, W_L]
  · by_cases hk : k' = k
    · subst hk
      rw [Function.update_self, W_R, W_R]
      unfold fl
      rw [Function.update_self]
    · have hne : π.symm (R k') ≠ π.symm (R k) := fun h => hk (R_inj (π.symm.injective h))
      rw [Function.update_of_ne hne, W_R, W_R]
      unfold fl
      rw [Function.update_of_ne hk]

lemma arith : ∀ g0 g1 g2 a0 a1 a2 b0 b1 b2 Z : Fin 2,
    g0 * (b0 - a0) + g1 * (b1 - a1) + g2 * (b2 - a2) = 1 →
    g0 * b0 + g1 * b1 + g2 * b2 + Z = g0 * a0 + g1 * a1 + g2 * a2 + Z + 1 := by
  decide

lemma core (π : Equiv.Perm (Fin 6)) (a b : Config 3 2) (hab : a ≠ b) :
    (∑ z : Config 3 2, s (W π a z) * s (W π b z)) = 0 := by
  have hL : ∀ m m' : Fin 3, m ≠ m' → π.symm (L m) ≠ π.symm (L m') := by
    intro m m' hm h
    apply hm
    apply Fin.ext
    have := congrArg Fin.val (π.symm.injective h)
    simpa [L] using this
  have hc : ¬ (b 0 - a 0 = 0 ∧ b 1 - a 1 = 0 ∧ b 2 - a 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    rw [sub_eq_zero] at h0 h1 h2
    apply hab
    funext m
    fin_cases m
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
  obtain ⟨j, hjp, hjq, hjr, hj⟩ := rank _ _ _ (hL 0 1 (by decide)) (hL 0 2 (by decide))
    (hL 1 2 (by decide)) _ _ _ hc
  have hN : ∀ z, N j (W π b z) = N j (W π a z) + 1 := by
    intro z
    rw [N_W, N_W]
    simp only [Fin.sum_univ_three]
    exact arith _ _ _ _ _ _ _ _ _ _ hj
  rcases cover π j with ⟨m, rfl⟩ | ⟨k, rfl⟩
  · exfalso
    fin_cases m
    · exact hjp rfl
    · exact hjq rfl
    · exact hjr rfl
  refine Finset.sum_involution (fun z _ => fl k z) ?_ ?_ (fun z _ => Finset.mem_univ _) ?_
  · intro z _
    rw [W_fl, W_fl, s_flip, s_flip, hN z, sg_succ]
    have := sg_sq (N (π.symm (R k)) (W π a z))
    linear_combination (-(s (W π a z) * s (W π b z))) * this
  · intro z _ _ h
    have := congrFun h k
    unfold fl at this
    rw [Function.update_self] at this
    exact fin2_ne _ this
  · intro z _
    funext i
    unfold fl
    by_cases hi : i = k
    · subst hi
      rw [Function.update_self, Function.update_self]
      exact fin2_11 _
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]

lemma main (π : Equiv.Perm (Fin 6)) :
    HasMaximallyMixedFirstReduction (n := 6) (d := 2) 3 (by decide) (permuteState π psi) := by
  unfold HasMaximallyMixedFirstReduction
  ext a b
  have hL : reducedDensityFirst (n := 6) (d := 2) 3 (by decide) (permuteState π psi) a b =
      ((1 / 64 : ℝ) : ℂ) * (((∑ z : Config 3 2, s (W π a z) * s (W π b z) : ℤ)) : ℂ) := by
    unfold reducedDensityFirst
    rw [Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    exact term_mul _ _
  rw [hL]
  simp only [maximallyMixed, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Finset.sum_congr rfl (fun z _ => s_sq (W π a z))]
    simp
    norm_num
  · rw [if_neg hab, core π a b hab]
    simp

end AME62

theorem ame_6_2_exists : ExistsAME 6 2 := by
  refine ⟨AME62.psi, AME62.psi_norm, fun π => ?_⟩
  exact AME62.main π

end OpenQuantumProblem35

#print axioms OpenQuantumProblem35.ame_6_2_exists
