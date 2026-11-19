import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
namespace OpenQuantumProblem13

abbrev UMat (d : ℕ) := ↥(Matrix.unitaryGroup (Fin d) ℂ)

def relativeUnitary {d : ℕ} (U V : UMat d) : Matrix (Fin d) (Fin d) ℂ :=
  star (U : Matrix (Fin d) (Fin d) ℂ) * (V : Matrix (Fin d) (Fin d) ℂ)

def IsUnbiased {d : ℕ} (U V : UMat d) : Prop :=
  ∀ i j : Fin d, ‖relativeUnitary U V i j‖ ^ (2 : ℕ) = (d : ℝ)⁻¹

lemma IsUnbiased.symm {d : ℕ} {U V : UMat d} (hUV : IsUnbiased U V) :
    IsUnbiased V U := by
  intro i j
  have hstar : relativeUnitary V U = star (relativeUnitary U V) := by simp [relativeUnitary]
  calc
    ‖relativeUnitary V U i j‖ ^ (2 : ℕ)
        = ‖star (relativeUnitary U V) i j‖ ^ (2 : ℕ) := by simp [hstar]
    _ = ‖relativeUnitary U V j i‖ ^ (2 : ℕ) := by simp
    _ = (d : ℝ)⁻¹ := hUV j i

def IsMUBFamily {d k : ℕ} (B : Fin k → UMat d) : Prop :=
  Pairwise fun m n => IsUnbiased (B m) (B n)

def HasMUBs (d k : ℕ) : Prop :=
  ∃ B : Fin k → UMat d, IsMUBFamily B

namespace Qubit

def ω : ℂ := (1 + Complex.I) / 2

def phaseMatrix (ζ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 1;
    ζ, -ζ]

lemma omega_norm_sq : ‖ω‖ ^ (2 : ℕ) = (2 : ℝ)⁻¹ := by
  rw [RCLike.norm_sq_eq_def]
  simp [ω]
  norm_num

lemma conj_omega_mul_omega : star ω * ω = ((2 : ℝ)⁻¹ : ℂ) := by
  calc
    star ω * ω = ((‖ω‖ : ℂ) ^ (2 : ℕ)) := by
      simpa using (Complex.conj_mul' ω)
    _ = ((2 : ℝ)⁻¹ : ℂ) := by
      exact_mod_cast omega_norm_sq

lemma star_smul_mul_smul (a : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    star (a • A) * (a • B) = (star a * a) • (star A * B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf

lemma star_phaseMatrix_mul_phaseMatrix (ζ η : ℂ) :
    star (phaseMatrix ζ) * phaseMatrix η =
      !![1 + star ζ * η, 1 - star ζ * η;
         1 - star ζ * η, 1 + star ζ * η] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseMatrix, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

lemma star_phaseMatrix_mul_self_of_unit_phase {ζ : ℂ} (hζ : star ζ * ζ = 1) :
    star (phaseMatrix ζ) * phaseMatrix ζ = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [star_phaseMatrix_mul_phaseMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> rw [hζ] <;> norm_num

lemma scaled_phaseMatrix_mem_unitary {ζ : ℂ} (hζ : star ζ * ζ = 1) :
    (ω • phaseMatrix ζ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  calc
    star (ω • phaseMatrix ζ) * (ω • phaseMatrix ζ)
        = (star ω * ω) • (star (phaseMatrix ζ) * phaseMatrix ζ) := by
          simpa using (star_smul_mul_smul ω (phaseMatrix ζ) (phaseMatrix ζ))
    _ = ((star ω * ω) * (2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          rw [star_phaseMatrix_mul_self_of_unit_phase hζ, smul_smul]
    _ = 1 := by
          rw [conj_omega_mul_omega]
          norm_num

lemma star_phaseBasis_mul_phaseBasis (ζ η : ℂ) :
    star (ω • phaseMatrix ζ) * (ω • phaseMatrix η) =
      (star ω * ω) • !![1 + star ζ * η, 1 - star ζ * η;
                        1 - star ζ * η, 1 + star ζ * η] := by
  rw [star_smul_mul_smul, star_phaseMatrix_mul_phaseMatrix]

def phaseU (ζ : ℂ) (hζ : star ζ * ζ = 1) : UMat 2 :=
  ⟨ω • phaseMatrix ζ, scaled_phaseMatrix_mem_unitary hζ⟩

lemma phase_norm_sq_eq_one {ζ : ℂ} (hζ : star ζ * ζ = 1) :
    ‖ζ‖ ^ (2 : ℕ) = 1 := by
  have hzC : ((‖ζ‖ : ℂ) ^ (2 : ℕ)) = 1 := by
    calc
      ((‖ζ‖ : ℂ) ^ (2 : ℕ)) = star ζ * ζ := by
        simpa using (Complex.conj_mul' ζ).symm
      _ = 1 := hζ
  exact_mod_cast hzC

lemma omega_mul_phase_norm_sq {ζ : ℂ} (hζ : star ζ * ζ = 1) :
    ‖ω * ζ‖ ^ (2 : ℕ) = (2 : ℝ)⁻¹ := by
  rw [norm_mul, mul_pow, omega_norm_sq, phase_norm_sq_eq_one hζ]; norm_num

def ZU : UMat 2 := 1

def XU : UMat 2 := phaseU 1 (by simp)

def YU : UMat 2 := phaseU Complex.I (by simp)

lemma isUnbiased_Z_phaseU (ζ : ℂ) (hζ : star ζ * ζ = 1) :
    IsUnbiased ZU (phaseU ζ hζ) := by
  intro i j
  fin_cases i <;> fin_cases j
  · simp [relativeUnitary, ZU, phaseU, phaseMatrix, omega_norm_sq]
  · simp [relativeUnitary, ZU, phaseU, phaseMatrix, omega_norm_sq]
  all_goals simpa [relativeUnitary, ZU, phaseU, phaseMatrix, norm_mul] using
    omega_mul_phase_norm_sq (ζ := ζ) hζ

lemma relative_phaseU_phaseU_of_mul_eq_I {ζ η : ℂ}
    (hζ : star ζ * ζ = 1) (hη : star η * η = 1) (hζη : star ζ * η = Complex.I) :
    relativeUnitary (phaseU ζ hζ) (phaseU η hη) = !![ω, star ω;
                                                      star ω, ω] := by
  calc
    relativeUnitary (phaseU ζ hζ) (phaseU η hη) =
        (star ω * ω) • !![1 + star ζ * η, 1 - star ζ * η;
                          1 - star ζ * η, 1 + star ζ * η] := by
      simpa [relativeUnitary, phaseU, sub_eq_add_neg] using
        (star_phaseBasis_mul_phaseBasis ζ η)
    _ = (star ω * ω) • !![1 + Complex.I, 1 - Complex.I;
                          1 - Complex.I, 1 + Complex.I] := by
      rw [hζη]
    _ = ((2 : ℝ)⁻¹ : ℂ) • !![1 + Complex.I, 1 - Complex.I;
                              1 - Complex.I, 1 + Complex.I] := by
      rw [conj_omega_mul_omega]
    _ = !![ω, star ω;
           star ω, ω] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ω, div_eq_mul_inv, sub_eq_add_neg] <;> ring_nf

lemma isUnbiased_phaseU_phaseU_of_mul_eq_I {ζ η : ℂ}
    (hζ : star ζ * ζ = 1) (hη : star η * η = 1) (hζη : star ζ * η = Complex.I) :
    IsUnbiased (phaseU ζ hζ) (phaseU η hη) := by
  intro i j
  rw [relative_phaseU_phaseU_of_mul_eq_I hζ hη hζη]
  fin_cases i <;> fin_cases j <;> simp [omega_norm_sq]

def qubitFamily : Fin 3 → UMat 2 :=
  ![ZU, XU, YU]

lemma qubitFamily_isMUB : IsMUBFamily qubitFamily := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  · simpa [qubitFamily, XU] using isUnbiased_Z_phaseU (ζ := 1) (by simp)
  · simpa [qubitFamily, YU] using isUnbiased_Z_phaseU (ζ := Complex.I) (by simp)
  · simpa [qubitFamily, XU] using
      (IsUnbiased.symm <| isUnbiased_Z_phaseU (ζ := 1) (by simp))
  · simpa [qubitFamily, XU, YU] using
      isUnbiased_phaseU_phaseU_of_mul_eq_I
        (ζ := 1) (η := Complex.I) (by simp) (by simp) (by simp)
  · simpa [qubitFamily, YU] using
      (IsUnbiased.symm <| isUnbiased_Z_phaseU (ζ := Complex.I) (by simp))
  · simpa [qubitFamily, XU, YU] using
      (IsUnbiased.symm <|
        isUnbiased_phaseU_phaseU_of_mul_eq_I
          (ζ := 1) (η := Complex.I) (by simp) (by simp) (by simp))

end Qubit

namespace Qutrit

def s : ℝ := Real.sqrt 3

lemma hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)

def ω : ℂ := ⟨-1/2, s/2⟩
def ν : ℂ := ⟨-1/2, -s/2⟩
def c : ℂ := ((s / 3 : ℝ) : ℂ)

/-- cube roots of unity indexed by exponents -/
def r (a : Fin 3) : ℂ := ![1, ω, ν] a

lemma ωω : ω * ω = ν := by apply Complex.ext <;> simp [ω, ν] <;> nlinarith [hs]
lemma ων : ω * ν = 1 := by apply Complex.ext <;> simp [ω, ν] <;> nlinarith [hs]
lemma νω : ν * ω = 1 := by apply Complex.ext <;> simp [ω, ν] <;> nlinarith [hs]
lemma νν : ν * ν = ω := by apply Complex.ext <;> simp [ω, ν] <;> nlinarith [hs]
lemma sω : star ω = ν := by
  apply Complex.ext
  · simp [ω, ν]
  · simp [ω, ν]; ring
lemma sν : star ν = ω := by
  apply Complex.ext
  · simp [ω, ν]
  · simp [ω, ν]; ring
lemma hsum : 1 + ω + ν = 0 := by apply Complex.ext <;> simp [ω, ν] <;> ring

lemma r_add (a b : Fin 3) : r (a + b) = r a * r b := by
  fin_cases a <;> fin_cases b <;> simp [r, ωω, ων, νω, νν]

lemma r_star (a : Fin 3) : star (r a) = r (-a) := by
  fin_cases a <;> simp [r, sω, sν]

lemma normSq_r (a : Fin 3) : Complex.normSq (r a) = 1 := by
  fin_cases a <;> simp [r, Complex.normSq_apply, ω, ν] <;> nlinarith [hs]

lemma c_star : star c = c := by simp [c]

lemma cc : c * c = ((1 / 3 : ℝ) : ℂ) := by
  rw [c, ← Complex.ofReal_mul]
  congr 1
  nlinarith [hs]

lemma normSq_c : Complex.normSq c = 1 / 3 := by
  rw [c, Complex.normSq_ofReal]
  nlinarith [hs]

lemma S3_dist (a b e : Fin 3) (h1 : a ≠ b) (h2 : b ≠ e) (h3 : a ≠ e) :
    r a + r b + r e = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases e <;> simp [r] at h1 h2 h3 ⊢ <;>
    linear_combination hsum

def Two (a b e : Fin 3) : Prop := ¬(a = b ∧ b = e) ∧ ¬(a ≠ b ∧ b ≠ e ∧ a ≠ e)

instance (a b e : Fin 3) : Decidable (Two a b e) := by unfold Two; infer_instance

lemma S3_two (a b e : Fin 3) (h : Two a b e) :
    Complex.normSq (r a + r b + r e) = 3 := by
  unfold Two at h
  fin_cases a <;> fin_cases b <;> fin_cases e <;> simp at h <;>
    simp [r, Complex.normSq_apply, ω, ν] <;> nlinarith [hs]

def M (f : Fin 3 → Fin 3 → Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => c * r (f i j)

lemma rel_entry (f g : Fin 3 → Fin 3 → Fin 3) (i j : Fin 3) :
    (star (M f) * M g) i j
      = c * c * (r (g 0 j - f 0 i) + r (g 1 j - f 1 i) + r (g 2 j - f 2 i)) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, M, Matrix.of_apply,
    star_mul', c_star, r_star, sub_eq_add_neg, r_add]
  ring

lemma M_unitary (f : Fin 3 → Fin 3 → Fin 3)
    (hf : ∀ i j, i ≠ j → f 0 j - f 0 i ≠ f 1 j - f 1 i ∧ f 1 j - f 1 i ≠ f 2 j - f 2 i ∧
      f 0 j - f 0 i ≠ f 2 j - f 2 i) :
    M f ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  rw [rel_entry]
  by_cases h : i = j
  · subst h
    rw [sub_self, sub_self, sub_self, Matrix.one_apply_eq, cc]
    have : r 0 = 1 := by simp [r]
    rw [this]
    push_cast
    norm_num
  · obtain ⟨h1, h2, h3⟩ := hf i j h
    rw [S3_dist _ _ _ h1 h2 h3, Matrix.one_apply_ne h, mul_zero]

def fF : Fin 3 → Fin 3 → Fin 3 := fun k i => k * i
def fG : Fin 3 → Fin 3 → Fin 3 := fun k i => k * i + (if k = 0 then 0 else 1)

lemma hF : ∀ i j : Fin 3, i ≠ j → fF 0 j - fF 0 i ≠ fF 1 j - fF 1 i ∧
    fF 1 j - fF 1 i ≠ fF 2 j - fF 2 i ∧ fF 0 j - fF 0 i ≠ fF 2 j - fF 2 i := by
  unfold fF; decide

lemma hG : ∀ i j : Fin 3, i ≠ j → fG 0 j - fG 0 i ≠ fG 1 j - fG 1 i ∧
    fG 1 j - fG 1 i ≠ fG 2 j - fG 2 i ∧ fG 0 j - fG 0 i ≠ fG 2 j - fG 2 i := by
  unfold fG; decide

lemma hFG : ∀ i j : Fin 3, Two (fG 0 j - fF 0 i) (fG 1 j - fF 1 i) (fG 2 j - fF 2 i) := by
  unfold fF fG; decide

def UF : UMat 3 := ⟨M fF, M_unitary fF hF⟩
def UG : UMat 3 := ⟨M fG, M_unitary fG hG⟩

lemma unb_one (f : Fin 3 → Fin 3 → Fin 3) (hf) :
    IsUnbiased (1 : UMat 3) ⟨M f, M_unitary f hf⟩ := by
  intro i j
  change ‖(star (1 : Matrix (Fin 3) (Fin 3) ℂ) * M f) i j‖ ^ 2 = _
  rw [star_one, one_mul, ← Complex.normSq_eq_norm_sq]
  simp only [M, Matrix.of_apply, Complex.normSq_mul, normSq_c, normSq_r]
  norm_num

lemma unb_FG : IsUnbiased UF UG := by
  intro i j
  change ‖(star (M fF) * M fG) i j‖ ^ 2 = _
  rw [rel_entry, ← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_mul,
    normSq_c, S3_two _ _ _ (hFG i j)]
  norm_num

def fam : Fin 3 → UMat 3 := ![1, UF, UG]

lemma fam_isMUB : IsMUBFamily fam := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact unb_one fF hF
  · exact unb_one fG hG
  · exact (unb_one fF hF).symm
  · exact unb_FG
  · exact (unb_one fG hG).symm
  · exact unb_FG.symm

end Qutrit

open scoped Kronecker

def e6 : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv

def T6 (M : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  M.submatrix e6.symm e6.symm

lemma T6_rel (M N : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    star (T6 M) * T6 N = T6 (star M * N) := by
  simp only [T6, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]

lemma kron_rel (A A' : Matrix (Fin 2) (Fin 2) ℂ) (B B' : Matrix (Fin 3) (Fin 3) ℂ) :
    star (A ⊗ₖ B) * (A' ⊗ₖ B') = (star A * A') ⊗ₖ (star B * B') := by
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul]

lemma T6_mem (U : UMat 2) (V : UMat 3) :
    T6 ((U : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (V : Matrix (Fin 3) (Fin 3) ℂ))
      ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', T6_rel, kron_rel, Matrix.UnitaryGroup.star_mul_self,
    Matrix.UnitaryGroup.star_mul_self, Matrix.one_kronecker_one]
  simp [T6]

def W (U : UMat 2) (V : UMat 3) : UMat 6 := ⟨_, T6_mem U V⟩

lemma W_unb (U U' : UMat 2) (V V' : UMat 3) (h1 : IsUnbiased U U') (h2 : IsUnbiased V V') :
    IsUnbiased (W U V) (W U' V') := by
  intro i j
  have : relativeUnitary (W U V) (W U' V')
      = T6 (relativeUnitary U U' ⊗ₖ relativeUnitary V V') := by
    simp only [relativeUnitary, W]
    rw [T6_rel, kron_rel]
  rw [this]
  simp only [T6, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, norm_mul, mul_pow]
  rw [h1, h2]
  norm_num

theorem lower : HasMUBs 6 3 :=
  ⟨fun t => W (Qubit.qubitFamily t) (Qutrit.fam t), fun _ _ hab =>
    W_unb _ _ _ _ (Qubit.qubitFamily_isMUB hab) (Qutrit.fam_isMUB hab)⟩

namespace MUBUp

variable {d m : ℕ}

/-- entries of the rank-one projector onto column `x.2` of basis `x.1` -/
def P (B : Fin m → UMat d) (x : Fin m × Fin d) (a b : Fin d) : ℂ :=
  (B x.1 : Matrix (Fin d) (Fin d) ℂ) a x.2 * star ((B x.1 : Matrix (Fin d) (Fin d) ℂ) b x.2)

/-- real Hilbert–Schmidt pairing -/
def pair (A C : Fin d → Fin d → ℂ) : ℝ := ∑ p : Fin d × Fin d, (star (A p.1 p.2) * C p.1 p.2).re

lemma pair_sum (A : Fin d → Fin d → ℂ) (c : Fin m × Fin d → ℝ)
    (Q : Fin m × Fin d → Fin d → Fin d → ℂ) :
    pair A (fun a b => ∑ x, (c x : ℂ) * Q x a b) = ∑ x, c x * pair A (Q x) := by
  unfold pair
  have h : ∀ p : Fin d × Fin d, (star (A p.1 p.2) * ∑ x, (c x : ℂ) * Q x p.1 p.2).re
      = ∑ x, c x * (star (A p.1 p.2) * Q x p.1 p.2).re := by
    intro p
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_left_comm, Complex.re_ofReal_mul]
  simp_rw [h, Finset.mul_sum]
  exact Finset.sum_comm

lemma pair_P (B : Fin m → UMat d) (y x : Fin m × Fin d) :
    pair (P B y) (P B x) = ‖relativeUnitary (B y.1) (B x.1) y.2 x.2‖ ^ 2 := by
  set U := (B y.1 : Matrix (Fin d) (Fin d) ℂ)
  set V := (B x.1 : Matrix (Fin d) (Fin d) ℂ)
  have hz : relativeUnitary (B y.1) (B x.1) y.2 x.2 = ∑ a, star (U a y.2) * V a x.2 := by
    simp [relativeUnitary, Matrix.mul_apply, Matrix.star_apply, U, V]
  rw [hz, ← Complex.normSq_eq_norm_sq]
  set z := ∑ a, star (U a y.2) * V a x.2
  have h1 : Complex.normSq z = (z * star z).re := by
    rw [Complex.star_def, Complex.mul_conj]; simp
  rw [h1]
  have h2 : z * star z = ∑ p : Fin d × Fin d, star (P B y p.1 p.2) * P B x p.1 p.2 := by
    simp only [z, star_sum, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [P, star_mul', star_star, U, V]
    ring
  rw [h2, Complex.re_sum]
  rfl

lemma P_herm (B : Fin m → UMat d) (x : Fin m × Fin d) (a b : Fin d) :
    P B x b a = star (P B x a b) := by
  simp only [P, star_mul', star_star]
  ring

lemma herm_inj (A : Fin d → Fin d → ℂ) (hA : ∀ a b, A b a = star (A a b))
    (h0 : ∀ a b, (if a ≤ b then (A a b).re else (A a b).im) = 0) (a b : Fin d) :
    A a b = 0 := by
  apply Complex.ext
  · rcases le_total a b with hab | hab
    · have h := h0 a b
      rw [if_pos hab] at h
      simpa using h
    · have h := h0 b a
      rw [if_pos hab] at h
      rw [hA b a]
      simp [h]
  · rcases lt_trichotomy a b with hab | rfl | hab
    · have h := h0 b a
      rw [if_neg (not_le.2 hab)] at h
      rw [hA b a]
      simp [h]
    · have h := congrArg Complex.im (hA a a)
      simp at h
      simp
      linarith
    · have h := h0 a b
      rw [if_neg (not_le.2 hab)] at h
      simpa using h

/-- real coordinates of a Hermitian matrix -/
def F (B : Fin m → UMat d) (x : Fin m × Fin d) (p : Fin d × Fin d) : ℝ :=
  if p.1 ≤ p.2 then (P B x p.1 p.2).re else (P B x p.1 p.2).im

def L (B : Fin m → UMat d) : (Fin m × Fin d → ℝ) →ₗ[ℝ] (Fin d × Fin d → ℝ) where
  toFun c p := ∑ x, c x * F B x p
  map_add' c c' := by
    ext p
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' t c := by
    ext p
    simp [Finset.mul_sum, mul_assoc]

lemma val (B : Fin m → UMat d) (hB : IsMUBFamily B) (s : Fin m) (j : Fin d)
    (x : Fin m × Fin d) :
    pair (P B (s, j)) (P B x) = if x.1 = s then (if x.2 = j then 1 else 0) else (d : ℝ)⁻¹ := by
  rw [pair_P]
  split_ifs with h1 h2
  · have : relativeUnitary (B s) (B x.1) = 1 := by
      rw [h1, relativeUnitary]
      exact Matrix.UnitaryGroup.star_mul_self (B s)
    simp only [this, h2, Matrix.one_apply_eq]
    have := Complex.norm_natCast 1
    simp only [Nat.cast_one] at this
    rw [this]; norm_num
  · have : relativeUnitary (B s) (B x.1) = 1 := by
      rw [h1, relativeUnitary]
      exact Matrix.UnitaryGroup.star_mul_self (B s)
    simp [this, Ne.symm h2]
  · exact hB (Ne.symm h1) j x.2

lemma ker_const (B : Fin m → UMat d) (hB : IsMUBFamily B) (c : Fin m × Fin d → ℝ)
    (hc : L B c = 0) (s : Fin m) (j j0 : Fin d) : c (s, j) = c (s, j0) := by
  set A : Fin d → Fin d → ℂ := fun a b => ∑ x, (c x : ℂ) * P B x a b with hAdef
  have hA : ∀ a b, A b a = star (A a b) := by
    intro a b
    simp only [A, star_sum, star_mul', P_herm B _ a b, Complex.star_def, Complex.conj_ofReal]
  have h0 : ∀ a b, (if a ≤ b then (A a b).re else (A a b).im) = 0 := by
    intro a b
    have h := congrFun hc (a, b)
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, F, Pi.zero_apply] at h
    rw [← h]
    split_ifs
    · simp only [A, Complex.re_sum, Complex.re_ofReal_mul]
    · simp only [A, Complex.im_sum, Complex.im_ofReal_mul]
  have hA0 : A = fun _ _ => 0 := by
    funext a b
    exact herm_inj A hA h0 a b
  have e : ∀ k : Fin d, ∑ x, c x * pair (P B (s, k)) (P B x) = 0 := by
    intro k
    rw [← pair_sum, ← hAdef, hA0]
    simp [pair]
  have key : ∀ x : Fin m × Fin d, pair (P B (s, j)) (P B x) - pair (P B (s, j0)) (P B x)
      = (if x = (s, j) then 1 else 0) - (if x = (s, j0) then 1 else 0) := by
    rintro ⟨r, i⟩
    rw [val B hB, val B hB]
    by_cases hr : r = s
    · subst hr
      simp [Prod.ext_iff, eq_comm]
    · simp [hr]
  have := congrArg₂ (· - ·) (e j) (e j0)
  simp only [sub_zero, ← Finset.sum_sub_distrib, ← mul_sub, key] at this
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  linarith

/-- `m` mutually unbiased bases in dimension `d` satisfy `m (d - 1) ≤ d²`. -/
theorem upper (B : Fin m → UMat d) (hB : IsMUBFamily B) (hd : 0 < d) :
    m * d ≤ d * d + m := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (L B)
  have h1 : Module.finrank ℝ (LinearMap.range (L B)) ≤ d * d := by
    have := Submodule.finrank_le (LinearMap.range (L B))
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] using this
  have h2 : Module.finrank ℝ (LinearMap.ker (L B)) ≤ m := by
    let K0 : (Fin m × Fin d → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
      LinearMap.funLeft ℝ ℝ (fun s => (s, (⟨0, hd⟩ : Fin d)))
    have hinj : Function.Injective (K0.comp (LinearMap.ker (L B)).subtype) := by
      intro c c' hcc
      apply Subtype.ext
      funext x
      have hc := LinearMap.mem_ker.1 c.2
      have hc' := LinearMap.mem_ker.1 c'.2
      have e := congrFun hcc x.1
      simp only [K0, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        LinearMap.funLeft_apply] at e
      rw [ker_const B hB c.1 hc x.1 x.2 ⟨0, hd⟩, ker_const B hB c'.1 hc' x.1 x.2 ⟨0, hd⟩]
      exact e
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa [Module.finrank_fintype_fun_eq_card] using this
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at hrn
  omega

end MUBUp

theorem mutuallyUnbiasedBases_dim6_bounds :
    HasMUBs 6 3 ∧ ∀ m : ℕ, HasMUBs 6 m → m ≤ 7 := by
  refine ⟨lower, ?_⟩
  rintro m ⟨B, hB⟩
  have := MUBUp.upper B hB (by norm_num)
  omega

end OpenQuantumProblem13

#print axioms OpenQuantumProblem13.mutuallyUnbiasedBases_dim6_bounds
