import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Star.Real

namespace Hadamard

def IsHadamard {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    |M.det| = n ^ ((n : ℝ) / 2)

def IsHadamard' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    M.transpose * M = ↑n

namespace HE

/-- Equality case of AM-GM. -/
lemma amgm_eq (k : ℕ) (hk : 0 < k) (z : Fin k → ℝ) (hz : ∀ i, 0 ≤ z i) (a : ℝ) (ha : 0 ≤ a)
    (hs : ∑ i, z i = k * a) (hp : ∏ i, z i = a ^ k) : ∀ i, z i = a := by
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hw' : ∑ _i : Fin k, (1 / (k:ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hmean : ∑ i, (1 / (k:ℝ)) * z i = a := by
    rw [← Finset.mul_sum, hs]; field_simp
  have hgeo : ∏ i, z i ^ (1 / (k:ℝ)) = a := by
    rw [Real.finsetProd_rpow _ _ (fun i _ => hz i), hp, one_div,
      Real.pow_rpow_inv_natCast ha hk.ne']
  have hpos : (0:ℝ) < 1 / (k:ℝ) := div_pos one_pos (by exact_mod_cast hk)
  have := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos' Finset.univ (fun _ => 1 / (k:ℝ)) z
    (fun i _ => hpos) hw' (fun i _ => hz i)).1 (by rw [hgeo, hmean])
  intro i
  have h2 := this i (Finset.mem_univ _)
  beta_reduce at h2
  rw [h2, hmean]

lemma entry_sq {x : ℝ} (h : x ∈ ({1, -1} : Finset ℝ)) : x * x = 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h <;> rw [h] <;> norm_num

lemma diag_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) (i : Fin n) :
    (M.transpose * M) i i = n := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, entry_sq (h _ i)]
  simp

lemma natCast_eq (n : ℕ) :
    (↑n : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal (fun _ => (n : ℝ)) := rfl

lemma rpow_sq (n : ℕ) : ((n : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (n : ℝ) ^ n := by
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg _),
    show (n : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

lemma fwd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h2 : M.transpose * M = ↑n) :
    |M.det| = n ^ ((n : ℝ) / 2) := by
  have hdet : M.det ^ 2 = (n : ℝ) ^ n := by
    have := congrArg Matrix.det h2
    rw [Matrix.det_mul, Matrix.det_transpose, natCast_eq, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    rw [sq]; exact this
  rw [← pow_left_inj₀ (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) two_ne_zero,
    sq_abs, hdet, rpow_sq]

lemma bwd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h1 : ∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) (h2 : |M.det| = n ^ ((n : ℝ) / 2)) :
    M.transpose * M = ↑n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext i; exact i.elim0
  have hP : (M.transpose * M).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self M
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hH := hP.1
  have hdet : (M.transpose * M).det = (n : ℝ) ^ n := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← abs_mul_abs_self, h2, ← sq, rpow_sq]
  have htr : (M.transpose * M).trace = (n : ℝ) * n := by
    rw [Matrix.trace]
    simp only [Matrix.diag, diag_eq M h1]
    simp
  have hprod : ∏ i, hH.eigenvalues i = (n : ℝ) ^ n := by
    have := hH.det_eq_prod_eigenvalues
    rw [hdet] at this
    simpa using this.symm
  have hsum : ∑ i, hH.eigenvalues i = (n : ℝ) * n := by
    have := hH.trace_eq_sum_eigenvalues
    rw [htr] at this
    simpa using this.symm
  have heig := amgm_eq n hn hH.eigenvalues (fun i => hP.eigenvalues_nonneg i) n
    (Nat.cast_nonneg _) hsum hprod
  have hd : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) (n : ℝ) := by
    rw [map_natCast, natCast_eq]
    congr 1
    funext i
    simp [heig i]
  rw [hH.spectral_theorem, hd, AlgHomClass.commutes, map_natCast]

end HE

theorem isHadamard_equiv_isHadamard' (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    IsHadamard' M ↔ IsHadamard M := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, HE.fwd M h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, HE.bwd M h1 h2⟩

end Hadamard

#print axioms Hadamard.isHadamard_equiv_isHadamard'
