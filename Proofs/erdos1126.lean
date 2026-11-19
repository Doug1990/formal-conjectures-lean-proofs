import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Prod

/-! Erdős 1126 (de Bruijn / Jurkat). -/

open MeasureTheory

namespace Erdos1126

namespace AA

/-- Translates of a.e. statements. -/
lemma ae_add (a : ℝ) {P : ℝ → Prop} (h : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ y ∂volume, P (a + y) :=
  (measurePreserving_add_left volume a).quasiMeasurePreserving.tendsto_ae.eventually h

lemma ae_sub (a : ℝ) {P : ℝ → Prop} (h : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ y ∂volume, P (a - y) :=
  (quasiMeasurePreserving_sub_left (volume : Measure ℝ) a).tendsto_ae.eventually h

lemma uniq {F : ℝ → ℝ} {a b : ℝ} (ha : ∀ᵐ y ∂volume, F y = a)
    (hb : ∀ᵐ y ∂volume, F y = b) : a = b := by
  obtain ⟨y, h1, h2⟩ := (ha.and hb).exists
  rw [← h1, ← h2]

end AA

theorem erdos_1126 : ∀
    (f : ℝ → ℝ)
    (h :
      ∀ᵐ (p : ℝ × ℝ) ∂(volume.prod volume),
        f (p.1 + p.2) = f p.1 + f p.2),
    ∃ h : ℝ → ℝ,
      (∀ x y, h (x + y) = h x + h y) ∧ (∀ᵐ x ∂volume, f x = h x) := by
  intro f hf
  -- G x : f (x + y) = f x + f y for a.e. y
  have hG : ∀ᵐ x ∂volume, ∀ᵐ y ∂volume, f (x + y) = f x + f y :=
    Measure.ae_ae_of_ae_prod hf
  have hu : ∀ x : ℝ, ∃ u : ℝ, (∀ᵐ y ∂volume, f (u + y) = f u + f y) ∧
      (∀ᵐ y ∂volume, f (x - u + y) = f (x - u) + f y) :=
    fun x => (hG.and (AA.ae_sub x hG)).exists
  choose u hu1 hu2 using hu
  set g : ℝ → ℝ := fun x => f (u x) + f (x - u x) with hg
  have hC : ∀ x, ∀ᵐ y ∂volume, f (x + y) - f y = g x := by
    intro x
    filter_upwards [hu2 x, AA.ae_add (x - u x) (hu1 x)] with y h1 h2
    have e : u x + (x - u x + y) = x + y := by ring
    rw [e] at h2
    rw [hg]; simp only
    linarith
  refine ⟨g, fun x y => ?_, ?_⟩
  · apply AA.uniq (hC (x + y))
    filter_upwards [AA.ae_add y (hC x), hC y] with z h1 h2
    have e : x + (y + z) = x + y + z := by ring
    rw [e] at h1
    linarith
  · filter_upwards [hG] with x hx
    apply AA.uniq (F := fun y => f (x + y) - f y) _ (hC x)
    filter_upwards [hx] with y hy
    linarith

end Erdos1126

#print axioms Erdos1126.erdos_1126
