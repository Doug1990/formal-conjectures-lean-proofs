import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

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

namespace AME43

/-- Completion criterion (copied from the source file). -/
lemma reducedDensityFirst_of_completion
    {n d m : ℕ} (hm : m ≤ n)
    (ψ : StateVector n d)
    (completion : Config m d → Config (n - m) d)
    (coeff : ℂ)
    (hψ : ∀ x z,
      ψ (combineFirst (n := n) (d := d) m hm x z) = if z = completion x then coeff else 0)
    (hinj : Function.Injective completion) :
    reducedDensityFirst (n := n) (d := d) m hm ψ =
      (coeff * star coeff) • (1 : Matrix (Config m d) (Config m d) ℂ) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst hxy
    rw [reducedDensityFirst, Finset.sum_eq_single (completion x)]
    · rw [hψ x (completion x)]
      simp
    · intro z _ hz
      rw [hψ x z]
      simp [hz]
    · simp
  · have hsum :
        (∑ z : Config (n - m) d,
          ψ (combineFirst (n := n) (d := d) m hm x z) *
            star (ψ (combineFirst (n := n) (d := d) m hm y z))) = 0 := by
      apply Finset.sum_eq_zero
      intro z _
      by_cases hxz : z = completion x
      · have hneq : completion x ≠ completion y := by
          intro hcomp
          exact hxy (hinj hcomp)
        rw [hψ x z, hψ y z]
        simp [hxz, hneq]
      · rw [hψ x z]
        simp [hxz]
    rw [reducedDensityFirst]
    simp [hxy]
    exact hsum

/-- The code word with message `v`. -/
def enc (v : Fin 3 × Fin 3) : Config 4 3 := ![v.1, v.2, v.1 + v.2, v.1 + 2 * v.2]

lemma enc0 (v : Fin 3 × Fin 3) : enc v 0 = v.1 := rfl
lemma enc1 (v : Fin 3 × Fin 3) : enc v 1 = v.2 := rfl

lemma mds_inj : ∀ p q : Fin 4, p ≠ q → ∀ v w : Fin 3 × Fin 3,
    enc v p = enc w p → enc v q = enc w q → v = w := by
  decide +kernel

lemma mds (p q : Fin 4) (hpq : p ≠ q) (a b : Fin 3) :
    ∃ v, enc v p = a ∧ enc v q = b := by
  have hinj : Function.Injective (fun v : Fin 3 × Fin 3 => (enc v p, enc v q)) := by
    intro v w h
    simp only [Prod.mk.injEq] at h
    exact mds_inj p q hpq v w h.1 h.2
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hinj) (a, b)
  simp only [Prod.mk.injEq] at hv
  exact ⟨v, hv⟩

lemma enc_inj : Function.Injective enc := by
  intro v w h
  exact mds_inj 0 1 (by decide) v w (congrFun h 0) (congrFun h 1)

noncomputable def coeff : ℂ := ((1 : ℝ) / 3 : ℝ)

noncomputable def psi : StateVector 4 3 :=
  mkStateVector fun y => if y = enc (y 0, y 1) then coeff else 0

lemma mem_code (y : Config 4 3) : y = enc (y 0, y 1) ↔ ∃ v, enc v = y := by
  constructor
  · intro h
    exact ⟨_, h.symm⟩
  · rintro ⟨v, rfl⟩
    rfl

lemma coeff_sq : coeff * star coeff = (1 / 9 : ℂ) := by
  have : star coeff = coeff := by
    simp [coeff]
  rw [this, coeff]
  push_cast
  norm_num

lemma psi_norm : IsNormalized psi := by
  classical
  have h2 : ‖psi‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hterm : ∀ y : Config 4 3, ‖psi y‖ ^ 2 =
        if y ∈ Finset.univ.image enc then (1 / 9 : ℝ) else 0 := by
      intro y
      have hm : (y ∈ Finset.univ.image enc) ↔ y = enc (y 0, y 1) := by
        rw [mem_code]
        simp
      by_cases hy : y = enc (y 0, y 1)
      · rw [if_pos (hm.mpr hy)]
        change ‖(if y = enc (y 0, y 1) then coeff else 0)‖ ^ 2 = _
        rw [if_pos hy, coeff, Complex.norm_real]
        norm_num
      · rw [if_neg (fun h => hy (hm.mp h))]
        change ‖(if y = enc (y 0, y 1) then coeff else 0)‖ ^ 2 = _
        rw [if_neg hy]
        simp
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, Finset.card_image_of_injective _ enc_inj]
    simp
  unfold IsNormalized
  have hn : 0 ≤ ‖psi‖ := norm_nonneg _
  nlinarith [h2, hn]

/-- every index of `Fin 4` is a left or a right index for the split 2 + 2. -/
lemma split (j : Fin 4) :
    (∃ k : Fin 2, j = ⟨k.1, by omega⟩) ∨ (∃ k : Fin 2, j = ⟨2 + k.1, by omega⟩) := by
  fin_cases j
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨1, rfl⟩

lemma comb_left (x z : Config 2 3) (k : Fin 2) :
    combineFirst (n := 4) (d := 3) 2 (by decide) x z ⟨k.1, by omega⟩ = x k := by
  simp [combineFirst, k.2]

lemma comb_right (x z : Config 2 3) (k : Fin 2) :
    combineFirst (n := 4) (d := 3) 2 (by decide) x z ⟨2 + k.1, by omega⟩ = z k := by
  have : ¬ (2 + k.1 < 2) := by omega
  simp [combineFirst, this]

def L (k : Fin 2) : Fin 4 := ⟨k.1, by omega⟩
def R (k : Fin 2) : Fin 4 := ⟨2 + k.1, by omega⟩

lemma L_ne : L 0 ≠ L 1 := by decide
lemma R_ne : R 0 ≠ R 1 := by decide

lemma main (π : Equiv.Perm (Fin 4)) :
    HasMaximallyMixedFirstReduction (n := 4) (d := 3) 2 (by decide) (permuteState π psi) := by
  classical
  have hpq : π.symm (L 0) ≠ π.symm (L 1) := fun h => L_ne (π.symm.injective h)
  have hrs : π.symm (R 0) ≠ π.symm (R 1) := fun h => R_ne (π.symm.injective h)
  let msg : Config 2 3 → Fin 3 × Fin 3 := fun x =>
    Classical.choose (mds _ _ hpq (x 0) (x 1))
  have msg_spec : ∀ x, enc (msg x) (π.symm (L 0)) = x 0 ∧ enc (msg x) (π.symm (L 1)) = x 1 :=
    fun x => Classical.choose_spec (mds _ _ hpq (x 0) (x 1))
  let comp : Config 2 3 → Config 2 3 := fun x k => enc (msg x) (π.symm (R k))
  have key : ∀ x z, (∃ v, enc v = permuteConfig π (combineFirst (n := 4) (d := 3) 2
      (by decide) x z)) ↔ z = comp x := by
    intro x z
    constructor
    · rintro ⟨v, hv⟩
      have hv' : ∀ j, enc v (π.symm j) = combineFirst (n := 4) (d := 3) 2 (by decide) x z j := by
        intro j
        have := congrFun hv (π.symm j)
        simpa [permuteConfig] using this
      have h0 := hv' (L 0)
      have h1 := hv' (L 1)
      rw [show L 0 = ⟨(0 : Fin 2).1, by omega⟩ from rfl, comb_left] at h0
      rw [show L 1 = ⟨(1 : Fin 2).1, by omega⟩ from rfl, comb_left] at h1
      have hvm : v = msg x :=
        mds_inj _ _ hpq v (msg x) (h0.trans (msg_spec x).1.symm) (h1.trans (msg_spec x).2.symm)
      funext k
      have := hv' (R k)
      rw [show R k = ⟨2 + k.1, by omega⟩ from rfl, comb_right] at this
      rw [← this, hvm]
      rfl
    · intro hz
      refine ⟨msg x, ?_⟩
      funext i
      simp only [permuteConfig]
      rcases split (π i) with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [hk, comb_left]
        have hi : i = π.symm (L k) := by
          rw [show L k = ⟨k.1, by omega⟩ from rfl, ← hk]
          simp
        rw [hi]
        fin_cases k
        · exact (msg_spec x).1
        · exact (msg_spec x).2
      · rw [hk, comb_right, hz]
        have hi : i = π.symm (R k) := by
          rw [show R k = ⟨2 + k.1, by omega⟩ from rfl, ← hk]
          simp
        rw [hi]
  have hψ : ∀ x z, permuteState π psi (combineFirst (n := 4) (d := 3) 2 (by decide) x z) =
      if z = comp x then coeff else 0 := by
    intro x z
    change (if _ = _ then coeff else 0) = _
    by_cases h : z = comp x
    · rw [if_pos h]
      exact if_pos ((mem_code _).mpr ((key x z).mpr h))
    · rw [if_neg h]
      exact if_neg (fun h' => h ((key x z).mp ((mem_code _).mp h')))
  have hinj : Function.Injective comp := by
    intro x y hxy
    have h0 := congrFun hxy 0
    have h1 := congrFun hxy 1
    have hv : msg x = msg y := mds_inj _ _ hrs _ _ h0 h1
    funext k
    fin_cases k
    · exact (msg_spec x).1.symm.trans (hv ▸ (msg_spec y).1)
    · exact (msg_spec x).2.symm.trans (hv ▸ (msg_spec y).2)
  unfold HasMaximallyMixedFirstReduction
  rw [reducedDensityFirst_of_completion (by decide) _ comp coeff hψ hinj, maximallyMixed,
    coeff_sq]
  congr 1
  simp

end AME43

theorem ame_4_3_exists : ExistsAME 4 3 := by
  refine ⟨AME43.psi, AME43.psi_norm, fun π => ?_⟩
  exact AME43.main π

end OpenQuantumProblem35

#print axioms OpenQuantumProblem35.ame_4_3_exists
