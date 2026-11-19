import Mathlib

noncomputable section
namespace OpenQuantumProblem23

abbrev StateVector (d : ℕ) := EuclideanSpace ℂ (Fin d)
abbrev mkStateVector {d : ℕ} (ψ : Fin d → ℂ) : StateVector d := WithLp.toLp 2 ψ
instance {d : ℕ} : CoeFun (StateVector d) (fun _ => Fin d → ℂ) where
  coe ψ := ψ.ofLp
def IsNormalized {d : ℕ} (ψ : StateVector d) : Prop := ‖ψ‖ = 1
def overlapSq {d : ℕ} (φ ψ : StateVector d) : ℝ :=
  Complex.normSq (∑ i : Fin d, star (φ i) * ψ i)
def HasConstantOverlapSq {d N : ℕ} (c : ℝ) (Φ : Fin N → StateVector d) : Prop :=
  Pairwise fun i j => overlapSq (Φ i) (Φ j) = c
def sicOverlapSq (d : ℕ) : ℝ := (d + 1 : ℝ)⁻¹
def ω : ℂ :=
  ((-(1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I
def tetraA : ℝ := Real.sqrt (1 / 3)
def tetraB : ℝ := Real.sqrt (2 / 3)
def vec2 (z₀ z₁ : ℂ) : StateVector 2 := mkStateVector ![z₀, z₁]
def qubitSICFamily : Fin 4 → StateVector 2
  | 0 => vec2 1 0
  | 1 => vec2 (tetraA : ℂ) (tetraB : ℂ)
  | 2 => vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω)
  | _ => vec2 (tetraA : ℂ) ((tetraB : ℂ) * (ω ^ 2))

lemma qubitSICFamily_pairwise :
    HasConstantOverlapSq (sicOverlapSq 2) qubitSICFamily := by
  have ha : tetraA ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hb : tetraB ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hb4 : tetraB ^ 4 = 4 / 9 := by
    have : tetraB ^ 4 = (tetraB ^ 2) ^ 2 := by ring
    rw [this, hb]; norm_num
  have ha4 : tetraA ^ 4 = 1 / 9 := by
    have : tetraA ^ 4 = (tetraA ^ 2) ^ 2 := by ring
    rw [this, ha]; norm_num
  have hs4 : Real.sqrt 3 ^ 4 = 9 := by
    have : Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
    rw [this, hs]; norm_num
  have hre : ω.re = -1 / 2 := by simp [ω]
  have him : ω.im = Real.sqrt 3 / 2 := by simp [ω]
  have hre2 : (ω ^ 2).re = -1 / 2 := by
    rw [pow_two, Complex.mul_re, hre, him]; nlinarith [hs]
  have him2 : (ω ^ 2).im = -(Real.sqrt 3 / 2) := by
    rw [pow_two, Complex.mul_im, hre, him]; ring
  have hre3 : ((starRingEnd ℂ ω) ^ 2).re = -1 / 2 := by
    rw [pow_two, Complex.mul_re, Complex.conj_re, Complex.conj_im, hre, him]; nlinarith [hs]
  have him3 : ((starRingEnd ℂ ω) ^ 2).im = Real.sqrt 3 / 2 := by
    rw [pow_two, Complex.mul_im, Complex.conj_re, Complex.conj_im, hre, him]; ring
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | skip
  all_goals
    simp [overlapSq, sicOverlapSq, qubitSICFamily, vec2, mkStateVector, Fin.sum_univ_two,
      Complex.normSq_apply, hre, him, hre2, him2, hre3, him3]
    ring_nf
    simp only [ha, hb, hb4, hs, hs4, ha4]
    try norm_num

end OpenQuantumProblem23

#print axioms OpenQuantumProblem23.qubitSICFamily_pairwise
