import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Set.Finite.Basic

open EuclideanSpace

namespace ErdosUlamProblem

namespace AE

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- Determinant of two plane vectors. -/
def det (u w : E2) : ℝ := u 0 * w 1 - u 1 * w 0

lemma inner_coord (x y : E2) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

lemma orth (u w : E2) (h : det u w ≠ 0) (X : E2) (h1 : inner ℝ X u = 0)
    (h2 : inner ℝ X w = 0) : X = 0 := by
  rw [inner_coord] at h1 h2
  have e0 : X 0 * det u w = 0 := by unfold det; linear_combination w 1 * h1 - u 1 * h2
  have e1 : X 1 * det u w = 0 := by unfold det; linear_combination u 0 * h2 - w 0 * h1
  have x0 := (mul_eq_zero.1 e0).resolve_right h
  have x1 := (mul_eq_zero.1 e1).resolve_right h
  refine PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simpa using x0
  · simpa using x1

lemma circle (P1 Z V : E2) (ρ s2 s3 : ℝ) (hs2 : s2 ≠ 0) (hs3 : s3 ≠ 0) (h23 : s2 ≠ s3)
    (h1 : ‖P1 - Z‖ ^ 2 = ρ ^ 2) (h2 : ‖P1 + s2 • V - Z‖ ^ 2 = (ρ + s2) ^ 2)
    (h3 : ‖P1 + s3 • V - Z‖ ^ 2 = (ρ + s3) ^ 2) : P1 - Z = ρ • V := by
  have e : ∀ s : ℝ, ‖P1 + s • V - Z‖ ^ 2
      = ‖P1 - Z‖ ^ 2 + 2 * s * inner ℝ (P1 - Z) V + s ^ 2 * ‖V‖ ^ 2 := by
    intro s
    rw [show P1 + s • V - Z = (P1 - Z) + s • V by abel, norm_add_sq_real,
      real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [e, h1] at h2 h3
  have k2 : s2 * (2 * inner ℝ (P1 - Z) V + s2 * ‖V‖ ^ 2 - 2 * ρ - s2) = 0 := by
    linear_combination h2
  have k3 : s3 * (2 * inner ℝ (P1 - Z) V + s3 * ‖V‖ ^ 2 - 2 * ρ - s3) = 0 := by
    linear_combination h3
  have m2 := (mul_eq_zero.1 k2).resolve_left hs2
  have m3 := (mul_eq_zero.1 k3).resolve_left hs3
  have hb : (s2 - s3) * (‖V‖ ^ 2 - 1) = 0 := by linear_combination m2 - m3
  have hβ : ‖V‖ ^ 2 = 1 := by
    have := (mul_eq_zero.1 hb).resolve_left (sub_ne_zero.2 h23)
    linarith
  have hα : inner ℝ (P1 - Z) V = ρ := by
    rw [hβ] at m2
    linarith
  have hz : ‖P1 - Z - ρ • V‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      hα, hβ, h1]
    ring
  exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hz))

lemma lin (A B C P : E2) (k l : ℝ) (hk : dist P A - dist P B = k)
    (hl : dist P B - dist P C = l) :
    2 * inner ℝ (P - B) (B - A) + ‖B - A‖ ^ 2 = k * (2 * dist P C + 2 * l + k) ∧
    2 * inner ℝ (P - C) (C - B) + ‖C - B‖ ^ 2 = l * (2 * dist P C + l) := by
  have hA : ‖P - A‖ = dist P C + l + k := by rw [← dist_eq_norm]; linarith
  have hB : ‖P - B‖ = dist P C + l := by rw [← dist_eq_norm]; linarith
  have hC : ‖P - C‖ = dist P C := (dist_eq_norm P C).symm
  constructor
  · have := norm_add_sq_real (P - B) (B - A)
    rw [show P - B + (B - A) = P - A by abel, hA, hB] at this
    linear_combination -this
  · have := norm_add_sq_real (P - C) (C - B)
    rw [show P - C + (C - B) = P - B by abel, hB, hC] at this
    linear_combination -this

lemma dif (A B C P Q : E2) (k l : ℝ) (hkP : dist P A - dist P B = k)
    (hlP : dist P B - dist P C = l) (hkQ : dist Q A - dist Q B = k)
    (hlQ : dist Q B - dist Q C = l) :
    inner ℝ (P - Q) (B - A) = k * (dist P C - dist Q C) ∧
    inner ℝ (P - Q) (C - B) = l * (dist P C - dist Q C) := by
  obtain ⟨a1, a2⟩ := lin A B C P k l hkP hlP
  obtain ⟨b1, b2⟩ := lin A B C Q k l hkQ hlQ
  constructor
  · rw [show P - Q = (P - B) - (Q - B) by abel, inner_sub_left]
    linarith
  · rw [show P - Q = (P - C) - (Q - C) by abel, inner_sub_left]
    linarith

lemma core (A B C P1 V : E2) (k l r1 s2 s3 : ℝ) (hdet : det (B - A) (C - B) ≠ 0)
    (hs2 : s2 ≠ 0) (hs3 : s3 ≠ 0) (h23 : s2 ≠ s3)
    (hA1 : dist P1 A = r1 + l + k) (hB1 : dist P1 B = r1 + l) (hC1 : dist P1 C = r1)
    (hA2 : dist (P1 + s2 • V) A = r1 + l + k + s2) (hB2 : dist (P1 + s2 • V) B = r1 + l + s2)
    (hC2 : dist (P1 + s2 • V) C = r1 + s2)
    (hA3 : dist (P1 + s3 • V) A = r1 + l + k + s3) (hB3 : dist (P1 + s3 • V) B = r1 + l + s3)
    (hC3 : dist (P1 + s3 • V) C = r1 + s3) : False := by
  have eC : P1 - C = r1 • V :=
    circle P1 C V r1 s2 s3 hs2 hs3 h23 (by rw [← dist_eq_norm, hC1])
      (by rw [← dist_eq_norm, hC2]) (by rw [← dist_eq_norm, hC3])
  have eB : P1 - B = (r1 + l) • V :=
    circle P1 B V (r1 + l) s2 s3 hs2 hs3 h23 (by rw [← dist_eq_norm, hB1])
      (by rw [← dist_eq_norm, hB2]) (by rw [← dist_eq_norm, hB3])
  have eA : P1 - A = (r1 + l + k) • V :=
    circle P1 A V (r1 + l + k) s2 s3 hs2 hs3 h23 (by rw [← dist_eq_norm, hA1])
      (by rw [← dist_eq_norm, hA2]) (by rw [← dist_eq_norm, hA3])
  have hu : B - A = k • V := by
    rw [show B - A = (P1 - A) - (P1 - B) by abel, eA, eB, ← sub_smul]
    congr 1; ring
  have hw : C - B = l • V := by
    rw [show C - B = (P1 - B) - (P1 - C) by abel, eB, eC, ← sub_smul]
    congr 1; ring
  apply hdet
  rw [hu, hw]
  unfold det
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

lemma three (A B C : E2) (hdet : det (B - A) (C - B) ≠ 0) (k l : ℝ) (P1 P2 P3 : E2)
    (h12 : P1 ≠ P2) (h13 : P1 ≠ P3) (h23 : P2 ≠ P3)
    (hk1 : dist P1 A - dist P1 B = k) (hl1 : dist P1 B - dist P1 C = l)
    (hk2 : dist P2 A - dist P2 B = k) (hl2 : dist P2 B - dist P2 C = l)
    (hk3 : dist P3 A - dist P3 B = k) (hl3 : dist P3 B - dist P3 C = l) : False := by
  obtain ⟨d2u, d2w⟩ := dif A B C P2 P1 k l hk2 hl2 hk1 hl1
  obtain ⟨d3u, d3w⟩ := dif A B C P3 P1 k l hk3 hl3 hk1 hl1
  obtain ⟨d23u, d23w⟩ := dif A B C P2 P3 k l hk2 hl2 hk3 hl3
  have hs2 : dist P2 C - dist P1 C ≠ 0 := by
    intro h
    apply h12
    have := orth _ _ hdet (P2 - P1) (by rw [d2u, h, mul_zero]) (by rw [d2w, h, mul_zero])
    exact (sub_eq_zero.1 this).symm
  have hs3 : dist P3 C - dist P1 C ≠ 0 := by
    intro h
    apply h13
    have := orth _ _ hdet (P3 - P1) (by rw [d3u, h, mul_zero]) (by rw [d3w, h, mul_zero])
    exact (sub_eq_zero.1 this).symm
  have hs23 : dist P2 C - dist P1 C ≠ dist P3 C - dist P1 C := by
    intro h
    have h' : dist P2 C - dist P3 C = 0 := by linarith
    apply h23
    have := orth _ _ hdet (P2 - P3) (by rw [d23u, h', mul_zero]) (by rw [d23w, h', mul_zero])
    exact sub_eq_zero.1 this
  have hX : (dist P3 C - dist P1 C) • (P2 - P1) - (dist P2 C - dist P1 C) • (P3 - P1) = 0 := by
    apply orth _ _ hdet
    · rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, d2u, d3u]; ring
    · rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, d2w, d3w]; ring
  have hP2 : P1 + (dist P2 C - dist P1 C) • ((dist P2 C - dist P1 C)⁻¹ • (P2 - P1)) = P2 := by
    rw [smul_inv_smul₀ hs2]; abel
  have hP3 : P1 + (dist P3 C - dist P1 C) • ((dist P2 C - dist P1 C)⁻¹ • (P2 - P1)) = P3 := by
    rw [smul_comm, sub_eq_zero.1 hX, inv_smul_smul₀ hs2]; abel
  exact core A B C P1 ((dist P2 C - dist P1 C)⁻¹ • (P2 - P1)) k l (dist P1 C)
    (dist P2 C - dist P1 C) (dist P3 C - dist P1 C) hdet hs2 hs3 hs23
    (by linarith) (by linarith) rfl
    (by rw [hP2]; linarith) (by rw [hP2]; linarith) (by rw [hP2]; ring)
    (by rw [hP3]; linarith) (by rw [hP3]; linarith) (by rw [hP3]; ring)

lemma noncol (a b c : E2) (hab : a ≠ b) (hc : ¬ ∃ t : ℝ, c = a + t • (b - a)) :
    det (b - a) (c - b) ≠ 0 := by
  intro h
  apply hc
  unfold det at h
  simp only [PiLp.sub_apply] at h
  by_cases h0 : b 0 = a 0
  · have h1 : b 1 ≠ a 1 := by
      intro h1
      apply hab
      exact PiLp.ext (Fin.forall_fin_two.2 ⟨h0.symm, h1.symm⟩)
    have hne : b 1 - a 1 ≠ 0 := sub_ne_zero.2 h1
    have hm : (b 1 - a 1) * (c 0 - b 0) = 0 := by
      linear_combination -h + (c 1 - b 1) * h0
    have hc0 : c 0 - b 0 = 0 := (mul_eq_zero.1 hm).resolve_left hne
    refine ⟨(c 1 - a 1) / (b 1 - a 1), PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [h0, sub_self, mul_zero, add_zero]
      linarith
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [div_mul_cancel₀ _ hne]
      ring
  · have hne : b 0 - a 0 ≠ 0 := sub_ne_zero.2 h0
    have key : (c 0 - a 0) / (b 0 - a 0) * (b 1 - a 1) = c 1 - a 1 := by
      rw [div_mul_eq_mul_div, div_eq_iff hne]
      linear_combination -h
    refine ⟨(c 0 - a 0) / (b 0 - a 0), PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [div_mul_cancel₀ _ hne]
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [key]
      ring

lemma intFin (M : ℝ) : {x : ℝ | ∃ n : ℤ, x = n ∧ |x| ≤ M}.Finite := by
  refine ((Set.finite_Icc (-⌈M⌉) ⌈M⌉).image (fun n : ℤ => (n : ℝ))).subset ?_
  rintro x ⟨n, rfl, h⟩
  rw [abs_le] at h
  have hc := Int.le_ceil M
  refine ⟨n, ⟨?_, ?_⟩, rfl⟩
  · exact_mod_cast (show ((-⌈M⌉ : ℤ) : ℝ) ≤ n by push_cast; linarith)
  · exact_mod_cast (show (n : ℝ) ≤ ((⌈M⌉ : ℤ) : ℝ) by linarith)

lemma no3 (T : Set E2) (h : ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T, x ≠ y → x ≠ z → y ≠ z → False) :
    T.Finite := by
  classical
  by_contra hT
  obtain ⟨t, ht, hc⟩ := Set.Infinite.exists_subset_card_eq hT 3
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hc
  exact h x (ht (by simp)) y (ht (by simp)) z (ht (by simp)) hxy hxz hyz

lemma finite_of (S : Set E2) (A B C : E2) (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S)
    (hdet : det (B - A) (C - B) ≠ 0)
    (hd : ∀ p ∈ S, ∀ q ∈ S, ∃ n : ℤ, dist p q = (n : ℝ)) : S.Finite := by
  let f : E2 → ℝ × ℝ := fun P => (dist P A - dist P B, dist P B - dist P C)
  have himg : (f '' S).Finite := by
    refine ((intFin (dist A B)).prod (intFin (dist B C))).subset ?_
    rintro _ ⟨P, hP, rfl⟩
    obtain ⟨n1, h1⟩ := hd P hP A hA
    obtain ⟨n2, h2⟩ := hd P hP B hB
    obtain ⟨n3, h3⟩ := hd P hP C hC
    refine ⟨⟨n1 - n2, by push_cast; linarith, ?_⟩, ⟨n2 - n3, by push_cast; linarith, ?_⟩⟩
    · show |dist P A - dist P B| ≤ dist A B
      rw [dist_comm P A, dist_comm P B]; exact abs_dist_sub_le A B P
    · show |dist P B - dist P C| ≤ dist B C
      rw [dist_comm P B, dist_comm P C]; exact abs_dist_sub_le B C P
  have hfib : ∀ y : ℝ × ℝ, {P | P ∈ S ∧ f P = y}.Finite := by
    intro y
    apply no3
    intro x hx y' hy z hz hxy hxz hyz
    exact three A B C hdet y.1 y.2 x y' z hxy hxz hyz
      (congrArg Prod.fst hx.2) (congrArg Prod.snd hx.2)
      (congrArg Prod.fst hy.2) (congrArg Prod.snd hy.2)
      (congrArg Prod.fst hz.2) (congrArg Prod.snd hz.2)
  refine (himg.biUnion fun y _ => hfib y).subset ?_
  intro P hP
  exact Set.mem_biUnion (Set.mem_image_of_mem f hP) ⟨hP, rfl⟩

end AE

theorem erdos_ulam_problem.variants.anning_erdos
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hinf : S.Infinite)
    (hd : ∀ p ∈ S, ∀ q ∈ S, ∃ n : ℤ, dist p q = (n : ℝ)) :
    ∃ a b : EuclideanSpace ℝ (Fin 2), a ≠ b ∧
      S ⊆ {x | ∃ t : ℝ, x = a + t • (b - a)} := by
  obtain ⟨a, ha, b, hb, hab⟩ := hinf.nontrivial
  refine ⟨a, b, hab, fun c hc => ?_⟩
  by_contra hnot
  exact hinf (AE.finite_of S a b c ha hb hc (AE.noncol a b c hab hnot) hd)

end ErdosUlamProblem

#print axioms ErdosUlamProblem.erdos_ulam_problem.variants.anning_erdos
