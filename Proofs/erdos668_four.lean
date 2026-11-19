import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped Finset

/-- Restated from FormalConjecturesForMathlib/Geometry/Metric.lean. -/
noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ :=
  #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

namespace Erdos90

/-- Restated from FormalConjectures/ErdosProblems/90.lean. -/
noncomputable def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistNum points | (points : Finset ℝ²) (_ : points.card = n)}

/-- Restated from FormalConjectures/ErdosProblems/90.lean. -/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)

end Erdos90

namespace Erdos668

open Erdos90

namespace FP

lemma dist_eq' (x y : ℝ²) : dist x y = √((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

lemma d1 (x y : ℝ²) : dist x y = 1 ↔ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = 1 := by
  rw [dist_eq', Real.sqrt_eq_one]

lemma ext2 {x y : ℝ²} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y :=
  PiLp.ext (Fin.forall_fin_two.2 ⟨h0, h1⟩)

/-- the point with coordinates (x, y) -/
noncomputable def P (x y : ℝ) : ℝ² := WithLp.toLp 2 ![x, y]

@[simp] lemma P0 (x y : ℝ) : (P x y) 0 = x := rfl
@[simp] lemma P1 (x y : ℝ) : (P x y) 1 = y := rfl

/-- no four points in the plane are pairwise at distance 1 (real form) -/
lemma noK4R (u0 u1 v0 v1 w0 w1 : ℝ) (hu : u0 ^ 2 + u1 ^ 2 = 1) (hv : v0 ^ 2 + v1 ^ 2 = 1)
    (hw : w0 ^ 2 + w1 ^ 2 = 1) (huv : (u0 - v0) ^ 2 + (u1 - v1) ^ 2 = 1)
    (huw : (u0 - w0) ^ 2 + (u1 - w1) ^ 2 = 1) (hvw : (v0 - w0) ^ 2 + (v1 - w1) ^ 2 = 1) :
    False := by
  have p : u0 * v0 + u1 * v1 = 1 / 2 := by linear_combination (hu + hv - huv) / 2
  have q : u0 * w0 + u1 * w1 = 1 / 2 := by linear_combination (hu + hw - huw) / 2
  have r : v0 * w0 + v1 * w1 = 1 / 2 := by linear_combination (hv + hw - hvw) / 2
  have G : (u0 ^ 2 + u1 ^ 2) * (v0 ^ 2 + v1 ^ 2) * (w0 ^ 2 + w1 ^ 2)
      + 2 * (u0 * v0 + u1 * v1) * (v0 * w0 + v1 * w1) * (u0 * w0 + u1 * w1)
      - (u0 ^ 2 + u1 ^ 2) * (v0 * w0 + v1 * w1) ^ 2
      - (v0 ^ 2 + v1 ^ 2) * (u0 * w0 + u1 * w1) ^ 2
      - (w0 ^ 2 + w1 ^ 2) * (u0 * v0 + u1 * v1) ^ 2 = 0 := by ring
  rw [hu, hv, hw, p, q, r] at G
  norm_num at G

lemma noK4 (a b c d : ℝ²) (hab : dist a b = 1) (hac : dist a c = 1) (had : dist a d = 1)
    (hbc : dist b c = 1) (hbd : dist b d = 1) (hcd : dist c d = 1) : False := by
  rw [d1] at hab hac had hbc hbd hcd
  exact noK4R (b 0 - a 0) (b 1 - a 1) (c 0 - a 0) (c 1 - a 1) (d 0 - a 0) (d 1 - a 1)
    (by linear_combination hab) (by linear_combination hac) (by linear_combination had)
    (by linear_combination hbc) (by linear_combination hbd) (by linear_combination hcd)

lemma perp (x0 x1 y0 y1 u0 u1 : ℝ) (hu : u0 ^ 2 + u1 ^ 2 = 1) (hxu : x0 * u0 + x1 * u1 = 0)
    (hyu : y0 * u0 + y1 * u1 = 0) (hxy : x0 * y0 + x1 * y1 = 0) (hx : x0 ≠ 0 ∨ x1 ≠ 0) :
    y0 = 0 ∧ y1 = 0 := by
  obtain ⟨cx, hcx⟩ : ∃ c, c = x0 * u1 - x1 * u0 := ⟨_, rfl⟩
  obtain ⟨cy, hcy⟩ : ∃ c, c = y0 * u1 - y1 * u0 := ⟨_, rfl⟩
  have hx0 : x0 = u1 * cx := by rw [hcx]; linear_combination u0 * hxu - x0 * hu
  have hx1 : x1 = -u0 * cx := by rw [hcx]; linear_combination u1 * hxu - x1 * hu
  have hy0 : y0 = u1 * cy := by rw [hcy]; linear_combination u0 * hyu - y0 * hu
  have hy1 : y1 = -u0 * cy := by rw [hcy]; linear_combination u1 * hyu - y1 * hu
  rw [hx0, hx1, hy0, hy1] at hxy
  have hc : cx * cy = 0 := by linear_combination hxy - cx * cy * hu
  have hcx0 : cx ≠ 0 := by
    intro h
    rw [hx0, hx1, h] at hx
    simp at hx
  have hcy0 : cy = 0 := by
    rcases mul_eq_zero.1 hc with h | h
    · exact absurd h hcx0
    · exact h
  rw [hy0, hy1, hcy0]
  simp

/-- two unit circles around b, c (with |b - c| = 1) meet in a and in b + c - a only -/
lemma circ (a b c d : ℝ²) (hbc : dist b c = 1) (hab : dist a b = 1) (hac : dist a c = 1)
    (hdb : dist d b = 1) (hdc : dist d c = 1) (hne : a ≠ d) : d = b + c - a := by
  rw [d1] at hbc hab hac hdb hdc
  have hu : (c 0 - b 0) ^ 2 + (c 1 - b 1) ^ 2 = 1 := by linear_combination hbc
  have hxu : ((a 0 - b 0) - (d 0 - b 0)) * (c 0 - b 0) + ((a 1 - b 1) - (d 1 - b 1)) * (c 1 - b 1)
      = 0 := by linear_combination (hab - hac - hdb + hdc) / 2
  have hyu : ((a 0 - b 0) + (d 0 - b 0) - (c 0 - b 0)) * (c 0 - b 0)
      + ((a 1 - b 1) + (d 1 - b 1) - (c 1 - b 1)) * (c 1 - b 1) = 0 := by
    linear_combination (hab - hac + hdb - hdc) / 2
  have hxy : ((a 0 - b 0) - (d 0 - b 0)) * ((a 0 - b 0) + (d 0 - b 0) - (c 0 - b 0))
      + ((a 1 - b 1) - (d 1 - b 1)) * ((a 1 - b 1) + (d 1 - b 1) - (c 1 - b 1)) = 0 := by
    linear_combination hab - hdb - (hab - hac - hdb + hdc) / 2
  have hx : (a 0 - b 0) - (d 0 - b 0) ≠ 0 ∨ (a 1 - b 1) - (d 1 - b 1) ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (ext2 (by linarith [h.1]) (by linarith [h.2]))
  obtain ⟨h0, h1⟩ := perp _ _ _ _ _ _ hu hxu hyu hxy hx
  apply ext2
  · simp only [PiLp.add_apply, PiLp.sub_apply]; linarith
  · simp only [PiLp.add_apply, PiLp.sub_apply]; linarith

/-- an orthonormal frame gives an isometry of the plane -/
lemma iso_gen (m0 m1 p0 p1 q0 q1 : ℝ) (hp : p0 ^ 2 + p1 ^ 2 = 1) (hq : q0 ^ 2 + q1 ^ 2 = 1)
    (hpq : p0 * q0 + p1 * q1 = 0) :
    ∃ f : ℝ² ≃ᵢ ℝ², ∀ x : ℝ², f x = P (m0 + x 0 * p0 + x 1 * q0) (m1 + x 0 * p1 + x 1 * q1) := by
  obtain ⟨c, hc⟩ : ∃ c, c = q0 * p1 - q1 * p0 := ⟨_, rfl⟩
  have hq0 : q0 = p1 * c := by rw [hc]; linear_combination p0 * hpq - q0 * hp
  have hq1 : q1 = -p0 * c := by rw [hc]; linear_combination p1 * hpq - q1 * hp
  have hcc : c ^ 2 = 1 := by rw [hq0, hq1] at hq; linear_combination hq - c ^ 2 * hp
  have c1 : p0 ^ 2 + q0 ^ 2 = 1 := by rw [hq0]; linear_combination hp + p1 ^ 2 * hcc
  have c2 : p0 * p1 + q0 * q1 = 0 := by rw [hq0, hq1]; linear_combination -p0 * p1 * hcc
  have c3 : p1 ^ 2 + q1 ^ 2 = 1 := by rw [hq1]; linear_combination hp + p0 ^ 2 * hcc
  refine ⟨IsometryEquiv.mk' (fun x => P (m0 + x 0 * p0 + x 1 * q0) (m1 + x 0 * p1 + x 1 * q1))
    (fun z => P ((z 0 - m0) * p0 + (z 1 - m1) * p1) ((z 0 - m0) * q0 + (z 1 - m1) * q1)) ?_ ?_,
    fun x => rfl⟩
  · intro z
    apply ext2
    · simp only [P0, P1]
      linear_combination (z 0 - m0) * c1 + (z 1 - m1) * c2
    · simp only [P0, P1]
      linear_combination (z 0 - m0) * c2 + (z 1 - m1) * c3
  · refine Isometry.of_dist_eq fun x y => ?_
    rw [dist_eq', dist_eq']
    congr 1
    simp only [P0, P1]
    linear_combination (x 0 - y 0) ^ 2 * hp + 2 * (x 0 - y 0) * (x 1 - y 1) * hpq
      + (x 1 - y 1) ^ 2 * hq

noncomputable def s0 : ℝ := √3 / 2

lemma hs2 : s0 ^ 2 = 3 / 4 := by
  unfold s0; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma hs0pos : 0 < s0 := by unfold s0; positivity

lemma msd (s t : ℝ) (hs : s ≠ 0) : s * (t / s) = t := by field_simp

/-- the congruence lemma: five unit distances with a ≠ d -/
lemma KL (a b c d : ℝ²) (hab : dist a b = 1) (hac : dist a c = 1) (hbc : dist b c = 1)
    (hdb : dist d b = 1) (hdc : dist d c = 1) (hne : a ≠ d) :
    ∃ f : ℝ² ≃ᵢ ℝ², f '' ({P 0 s0, P (-1/2) 0, P (1/2) 0, P 0 (-s0)} : Set ℝ²) = {a, b, c, d} := by
  have hd := circ a b c d hbc hab hac hdb hdc hne
  rw [d1] at hab hac hbc
  have hs0 : s0 ≠ 0 := hs0pos.ne'
  have hp : (c 0 - b 0) ^ 2 + (c 1 - b 1) ^ 2 = 1 := by linear_combination hbc
  have h2 : (a 0 - (b 0 + c 0) / 2) ^ 2 + (a 1 - (b 1 + c 1) / 2) ^ 2 = 3 / 4 := by
    linear_combination (hab + hac) / 2 - hbc / 4
  have hq : ((a 0 - (b 0 + c 0) / 2) / s0) ^ 2 + ((a 1 - (b 1 + c 1) / 2) / s0) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, h2, hs2]; norm_num
  have h3 : (c 0 - b 0) * (a 0 - (b 0 + c 0) / 2) + (c 1 - b 1) * (a 1 - (b 1 + c 1) / 2) = 0 := by
    linear_combination (hab - hac) / 2
  have hpq : (c 0 - b 0) * ((a 0 - (b 0 + c 0) / 2) / s0)
      + (c 1 - b 1) * ((a 1 - (b 1 + c 1) / 2) / s0) = 0 := by
    have e : (c 0 - b 0) * ((a 0 - (b 0 + c 0) / 2) / s0)
        + (c 1 - b 1) * ((a 1 - (b 1 + c 1) / 2) / s0)
        = ((c 0 - b 0) * (a 0 - (b 0 + c 0) / 2) + (c 1 - b 1) * (a 1 - (b 1 + c 1) / 2)) / s0 := by
      ring
    rw [e, h3, zero_div]
  obtain ⟨f, hf⟩ := iso_gen ((b 0 + c 0) / 2) ((b 1 + c 1) / 2) (c 0 - b 0) (c 1 - b 1)
    ((a 0 - (b 0 + c 0) / 2) / s0) ((a 1 - (b 1 + c 1) / 2) / s0) hp hq hpq
  refine ⟨f, ?_⟩
  have m0 := msd s0 (a 0 - (b 0 + c 0) / 2) hs0
  have m1 := msd s0 (a 1 - (b 1 + c 1) / 2) hs0
  have e1 : f (P 0 s0) = a := by
    rw [hf]; apply ext2
    · simp only [P0, P1]; linear_combination m0
    · simp only [P0, P1]; linear_combination m1
  have e2 : f (P (-1/2) 0) = b := by
    rw [hf]; apply ext2
    · simp only [P0, P1]; ring
    · simp only [P0, P1]; ring
  have e3 : f (P (1/2) 0) = c := by
    rw [hf]; apply ext2
    · simp only [P0, P1]; ring
    · simp only [P0, P1]; ring
  have e4 : f (P 0 (-s0)) = b + c - a := by
    rw [hf]; apply ext2
    · simp only [P0, P1, PiLp.add_apply, PiLp.sub_apply]; linear_combination (-1 : ℝ) * m0
    · simp only [P0, P1, PiLp.add_apply, PiLp.sub_apply]; linear_combination (-1 : ℝ) * m1
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    e1, e2, e3, e4, hd]

/-! ### Counting unit distances -/

open Classical in
noncomputable def D : Sym2 ℝ² → ℝ := Sym2.lift ⟨fun x y => dist x y, fun x y => dist_comm x y⟩

lemma D_mk (x y : ℝ²) : D s(x, y) = dist x y := rfl

lemma out_eq (z : Sym2 ℝ²) : dist z.out.1 z.out.2 = D z := by
  conv_rhs => rw [← Quot.out_eq z]
  rfl

lemma udn (s : Finset ℝ²) : unitDistNum s = #{z ∈ s.sym2 | D z = 1} := by
  unfold unitDistNum
  rw [Finset.filter_congr (fun z _ => by rw [out_eq])]

lemma sub6 (p q r t : ℝ²) : {z ∈ ({p, q, r, t} : Finset ℝ²).sym2 | D z = 1} ⊆
    {s(p, q), s(p, r), s(p, t), s(q, r), s(q, t), s(r, t)} := by
  intro z hz
  induction z using Sym2.ind with
  | h x y =>
    rw [Finset.mem_filter, Finset.mk_mem_sym2_iff, D_mk] at hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz1 ⊢
    rcases hz1 with ⟨rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl⟩ <;> simp_all

lemma fs_eq {B : Finset ℝ²} {p q r t x y z w : ℝ²} (hB : B = {p, q, r, t})
    (h : ∀ u : ℝ², (u = x ∨ u = y ∨ u = z ∨ u = w) ↔ (u = p ∨ u = q ∨ u = r ∨ u = t)) :
    B = {x, y, z, w} := by
  rw [hB]; ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; exact (h u).symm

lemma le4 {α : Type*} [DecidableEq α] (F T : Finset α) (e e' : α) (hF : F ⊆ T) (hT : #T ≤ 6)
    (he : e ∈ T) (he' : e' ∈ T) (hne : e' ≠ e) (hFe : e ∉ F) (hFe' : e' ∉ F) : #F ≤ 4 := by
  have h1 : F ⊆ (T.erase e).erase e' := by
    intro z hz
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨fun h => hFe' (h ▸ hz), fun h => hFe (h ▸ hz), hF hz⟩
  have h2 := Finset.card_le_card h1
  rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne, he'⟩), Finset.card_erase_of_mem he] at h2
  omega

lemma le5 (p q r t : ℝ²) : unitDistNum ({p, q, r, t} : Finset ℝ²) ≤ 5 := by
  rw [udn]
  by_contra h
  push Not at h
  have hT := Finset.card_le_six (a := s(p, q)) (b := s(p, r)) (c := s(p, t)) (d := s(q, r))
    (e := s(q, t)) (f := s(r, t))
  have heq := Finset.eq_of_subset_of_card_le (sub6 p q r t) (by omega)
  have g : ∀ x y, s(x, y) ∈ ({s(p, q), s(p, r), s(p, t), s(q, r), s(q, t), s(r, t)} :
      Finset (Sym2 ℝ²)) → dist x y = 1 := fun x y h => by
    rw [← heq, Finset.mem_filter, D_mk] at h; exact h.2
  exact noK4 p q r t (g p q (by simp)) (g p r (by simp)) (g p t (by simp)) (g q r (by simp))
    (g q t (by simp)) (g r t (by simp))

lemma ge5 (a b c d : ℝ²) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d)
    (h6 : c ≠ d) (hab : dist a b = 1) (hac : dist a c = 1) (hbc : dist b c = 1)
    (hbd : dist b d = 1) (hcd : dist c d = 1) : 5 ≤ unitDistNum ({a, b, c, d} : Finset ℝ²) := by
  rw [udn]
  have hsub : ({s(a, b), s(a, c), s(b, c), s(b, d), s(c, d)} : Finset (Sym2 ℝ²)) ⊆
      {z ∈ ({a, b, c, d} : Finset ℝ²).sym2 | D z = 1} := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;>
      rw [Finset.mem_filter, Finset.mk_mem_sym2_iff, D_mk] <;> simp [*]
  have hcard : #({s(a, b), s(a, c), s(b, c), s(b, d), s(c, d)} : Finset (Sym2 ℝ²)) = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton] <;>
      simp [h1, h2, h3, h4, h5, h6, h1.symm, h4.symm, h6.symm]
  calc 5 = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

lemma card4 (a b c d : ℝ²) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d)
    (h6 : c ≠ d) : ({a, b, c, d} : Finset ℝ²).card = 4 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h6] <;>
    simp [h1, h2, h3, h4, h5]

lemma dec4 (S : Finset ℝ²) (hS : S.card = 4) : ∃ p q r t : ℝ², p ≠ q ∧ p ≠ r ∧ p ≠ t ∧
    q ≠ r ∧ q ≠ t ∧ r ≠ t ∧ S = {p, q, r, t} := by
  have hS' : S.card = 3 + 1 := hS
  obtain ⟨p, S', hp, rfl, hS''⟩ := Finset.card_eq_succ.1 hS'
  obtain ⟨q, r, t, hqr, hqt, hrt, rfl⟩ := Finset.card_eq_three.1 hS''
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  exact ⟨p, q, r, t, hp.1, hp.2.1, hp.2.2, hqr, hqt, hrt, rfl⟩

lemma CL (B : Finset ℝ²) (x y z w : ℝ²) (hB : B = {x, y, z, w}) (h1 : x ≠ y) (h2 : x ≠ z)
    (h3 : x ≠ w) (h4 : y ≠ z) (h5 : y ≠ w) (_h6 : z ≠ w) (hxy : dist x y ≠ 1)
    (h5' : unitDistNum B = 5) :
    ∃ f : ℝ² ≃ᵢ ℝ², f '' ({P 0 s0, P (-1/2) 0, P (1/2) 0, P 0 (-s0)} : Set ℝ²) = ↑B := by
  subst hB
  rw [udn] at h5'
  have hFT := sub6 x y z w
  have hT := Finset.card_le_six (a := s(x, y)) (b := s(x, z)) (c := s(x, w)) (d := s(y, z))
    (e := s(y, w)) (f := s(z, w))
  have key : ∀ u v, s(u, v) ∈ ({s(x, y), s(x, z), s(x, w), s(y, z), s(y, w), s(z, w)} :
      Finset (Sym2 ℝ²)) → s(u, v) ≠ s(x, y) → dist u v = 1 := by
    intro u v huv hne
    by_contra h
    have := le4 _ _ (s(x, y)) (s(u, v)) hFT hT (by simp) huv hne
      (by rw [Finset.mem_filter, D_mk]; exact fun h' => hxy h'.2)
      (by rw [Finset.mem_filter, D_mk]; exact fun h' => h h'.2)
    omega
  have hxz := key x z (by simp) (by simp [h1, h4.symm])
  have hxw := key x w (by simp) (by simp [h1, h5.symm])
  have hyz := key y z (by simp) (by simp [h1.symm, h2.symm, h4.symm])
  have hyw := key y w (by simp) (by simp [h1.symm, h3.symm, h5.symm])
  have hzw := key z w (by simp) (by simp [h2.symm, h3.symm])
  obtain ⟨f, hf⟩ := KL x z w y hxz hxw hzw hyz hyw h1
  refine ⟨f, ?_⟩
  rw [hf]
  ext u
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.coe_insert, Finset.coe_singleton]
  constructor <;> rintro (h | h | h | h) <;> simp [h]

lemma neP (x y x' y' : ℝ) (h : x ≠ x' ∨ y ≠ y') : P x y ≠ P x' y' := by
  intro e
  rcases h with h | h
  · exact h (by simpa using congrArg (fun v : ℝ² => v 0) e)
  · exact h (by simpa using congrArg (fun v : ℝ² => v 1) e)

end FP

open FP in
/-- `@[category research solved, AMS 52]` in the checkout (attribute not available here). -/
theorem erdos_668.variants.four_points :
    ∃ a b c d : ℝ², dist a b = 1 ∧ dist a c = 1 ∧ dist b c = 1 ∧ dist b d = 1 ∧ dist c d = 1 ∧
      ({a, b, c, d} : Finset ℝ²).card = 4 ∧
      ∀ B : Finset ℝ², B.card = 4 →
        (unitDistNum B = maxUnitDistances 4 ↔ ∃ f : ℝ² ≃ᵢ ℝ², f '' {a, b, c, d} = B) := by
  have hs := hs2
  have hpos := hs0pos
  have n1 : P 0 s0 ≠ P (-1/2) 0 := neP _ _ _ _ (Or.inl (by norm_num))
  have n2 : P 0 s0 ≠ P (1/2) 0 := neP _ _ _ _ (Or.inl (by norm_num))
  have n3 : P 0 s0 ≠ P 0 (-s0) := neP _ _ _ _ (Or.inr (by intro h; linarith))
  have n4 : P (-1/2) 0 ≠ P (1/2) 0 := neP _ _ _ _ (Or.inl (by norm_num))
  have n5 : P (-1/2) 0 ≠ P 0 (-s0) := neP _ _ _ _ (Or.inl (by norm_num))
  have n6 : P (1/2) 0 ≠ P 0 (-s0) := neP _ _ _ _ (Or.inl (by norm_num))
  have dab : dist (P 0 s0) (P (-1/2) 0) = 1 := by
    rw [d1]; simp only [P0, P1]; linear_combination hs
  have dac : dist (P 0 s0) (P (1/2) 0) = 1 := by
    rw [d1]; simp only [P0, P1]; linear_combination hs
  have dbc : dist (P (-1/2) 0) (P (1/2) 0) = 1 := by
    rw [d1]; simp only [P0, P1]; norm_num
  have dbd : dist (P (-1/2) 0) (P 0 (-s0)) = 1 := by
    rw [d1]; simp only [P0, P1]; linear_combination hs
  have dcd : dist (P (1/2) 0) (P 0 (-s0)) = 1 := by
    rw [d1]; simp only [P0, P1]; linear_combination hs
  have hmax : maxUnitDistances 4 = 5 := by
    unfold maxUnitDistances
    apply IsGreatest.csSup_eq
    refine ⟨⟨{P 0 s0, P (-1/2) 0, P (1/2) 0, P 0 (-s0)}, card4 _ _ _ _ n1 n2 n3 n4 n5 n6,
      le_antisymm (le5 _ _ _ _) (ge5 _ _ _ _ n1 n2 n3 n4 n5 n6 dab dac dbc dbd dcd)⟩, ?_⟩
    rintro m ⟨S, hS, rfl⟩
    obtain ⟨p, q, r, t, -, -, -, -, -, -, rfl⟩ := dec4 S hS
    exact le5 p q r t
  refine ⟨P 0 s0, P (-1/2) 0, P (1/2) 0, P 0 (-s0), dab, dac, dbc, dbd, dcd,
    card4 _ _ _ _ n1 n2 n3 n4 n5 n6, fun B hB => ?_⟩
  rw [hmax]
  constructor
  · intro h5
    obtain ⟨p, q, r, t, hpq, hpr, hpt, hqr, hqt, hrt, hBe⟩ := dec4 B hB
    by_cases e1 : dist p q = 1
    · by_cases e2 : dist p r = 1
      · by_cases e3 : dist p t = 1
        · by_cases e4 : dist q r = 1
          · by_cases e5 : dist q t = 1
            · by_cases e6 : dist r t = 1
              · exact (noK4 p q r t e1 e2 e3 e4 e5 e6).elim
              · exact CL B r t p q (fs_eq hBe (fun u => by
                    constructor <;> rintro (h | h | h | h) <;> simp [h])) hrt hpr.symm hqr.symm
                  hpt.symm hqt.symm hpq e6 h5
            · exact CL B q t p r (fs_eq hBe (fun u => by
                  constructor <;> rintro (h | h | h | h) <;> simp [h])) hqt hpq.symm hqr hpt.symm
                hrt.symm hpr e5 h5
          · exact CL B q r p t (fs_eq hBe (fun u => by
                constructor <;> rintro (h | h | h | h) <;> simp [h])) hqr hpq.symm hqt hpr.symm hrt
              hpt e4 h5
        · exact CL B p t q r (fs_eq hBe (fun u => by
              constructor <;> rintro (h | h | h | h) <;> simp [h])) hpt hpq hpr hqt.symm hrt.symm hqr
            e3 h5
      · exact CL B p r q t (fs_eq hBe (fun u => by
            constructor <;> rintro (h | h | h | h) <;> simp [h])) hpr hpq hpt hqr.symm hrt hqt e2 h5
    · exact CL B p q r t hBe hpq hpr hpt hqr hqt hrt e1 h5
  · rintro ⟨f, hf⟩
    have hBf : B = {f (P 0 s0), f (P (-1/2) 0), f (P (1/2) 0), f (P 0 (-s0))} := by
      apply Finset.coe_injective
      rw [← hf]
      simp [Set.image_insert_eq]
    rw [hBf]
    exact le_antisymm (le5 _ _ _ _) (ge5 _ _ _ _ (f.injective.ne n1) (f.injective.ne n2)
      (f.injective.ne n3) (f.injective.ne n4) (f.injective.ne n5) (f.injective.ne n6)
      (by rw [f.dist_eq]; exact dab) (by rw [f.dist_eq]; exact dac) (by rw [f.dist_eq]; exact dbc)
      (by rw [f.dist_eq]; exact dbd) (by rw [f.dist_eq]; exact dcd))

/-- `@[category research solved, AMS 52]` in the checkout. Proof as in the checkout's test lemma
`four_points_implies_parts_ii`, applied to `four_points`. -/
theorem erdos_668.parts.ii :
    ¬ ∀ n : ℕ, 3 < n → ∃ A B : Finset ℝ², A.card = n ∧ B.card = n ∧
      unitDistNum A = maxUnitDistances n ∧ unitDistNum B = maxUnitDistances n ∧
      ¬ ∃ f : ℝ² ≃ᵢ ℝ², f '' A = B := by
  obtain ⟨a, b, c, d, -, -, -, -, -, -, h⟩ := erdos_668.variants.four_points
  intro H
  obtain ⟨A, B, hA, hB, hAm, hBm, hAB⟩ := H 4 (by norm_num)
  obtain ⟨f, hf⟩ := (h A hA).1 hAm
  obtain ⟨g, hg⟩ := (h B hB).1 hBm
  exact hAB ⟨f.symm.trans g, by rw [← hf, ← hg, Set.image_image]; simp⟩

end Erdos668

#print axioms Erdos668.erdos_668.variants.four_points
#print axioms Erdos668.erdos_668.parts.ii
