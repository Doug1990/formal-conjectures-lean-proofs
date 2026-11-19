import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Filter

open scoped Asymptotics Finset

namespace Erdos539

def IsCofactorLowerBound (n m : ℕ) : Prop := ∀ A : Finset ℕ, #A = n →
  m ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b)

noncomputable def cofactorThreshold (n : ℕ) : ℕ :=
  sSup {m | IsCofactorLowerBound n m}

namespace ES

lemma recover (a m : ℕ) (hm : 0 < m) : a = (a / a.gcd m) * (m / (m / m.gcd a)) := by
  rw [Nat.gcd_comm m a, Nat.div_div_self (Nat.gcd_dvd_right a m) hm.ne',
    Nat.div_mul_cancel (Nat.gcd_dvd_left a m)]

lemma card_le_sq (A : Finset ℕ) (m : ℕ) (hmA : m ∈ A) (hm : 0 < m) :
    #A ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b) *
      #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b) := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun a => (a / a.gcd m, m / m.gcd a))
  · intro a ha
    simp only [Finset.mem_coe] at ha ⊢
    rw [Finset.mem_product]
    exact ⟨Finset.mem_image.mpr ⟨(a, m), Finset.mem_product.mpr ⟨ha, hmA⟩, rfl⟩,
      Finset.mem_image.mpr ⟨(m, a), Finset.mem_product.mpr ⟨hmA, ha⟩, rfl⟩⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    rw [recover a m hm, recover b m hm, hab.1, hab.2]

lemma lb (n : ℕ) (hn : 2 ≤ n) : IsCofactorLowerBound n (Nat.sqrt n) := by
  intro A hA
  have h1 : 1 ≤ #(A.erase 0) := by
    have := Finset.pred_card_le_card_erase (s := A) (a := 0)
    omega
  obtain ⟨m, hm⟩ := Finset.card_pos.mp h1
  rw [Finset.mem_erase] at hm
  have key := card_le_sq A m hm.2 (Nat.pos_of_ne_zero hm.1)
  rw [hA] at key
  by_contra hlt
  rw [not_le] at hlt
  have hs := Nat.sqrt_le' n
  have : #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b) *
      #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b) < Nat.sqrt n ^ 2 := by
    rw [sq]; exact Nat.mul_lt_mul'' hlt hlt
  omega

lemma bdd (n : ℕ) : BddAbove {m | IsCofactorLowerBound n m} := by
  refine ⟨n * n, ?_⟩
  intro m hm
  have h := hm (Finset.range n) (Finset.card_range n)
  refine h.trans ?_
  calc #(((Finset.range n) ×ˢ (Finset.range n)).image fun (a, b) ↦ a / a.gcd b)
      ≤ #((Finset.range n) ×ˢ (Finset.range n)) := Finset.card_image_le
    _ = n * n := by rw [Finset.card_product, Finset.card_range]

lemma sqrt_le_h (n : ℕ) (hn : 2 ≤ n) : Nat.sqrt n ≤ cofactorThreshold n :=
  le_csSup (bdd n) (lb n hn)

end ES

theorem erdos_539.variants.sq_isBigO :
    (fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (cofactorThreshold n : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have h1 := ES.sqrt_le_h n hn
  have h2 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have h3 : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have h1' : (Nat.sqrt n : ℝ) ≤ cofactorThreshold n := by exact_mod_cast h1
  have h2' : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    rw [sq]; exact_mod_cast h2
  have h3' : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast h3
  have h4 : √(n : ℝ) < (Nat.sqrt n : ℝ) + 1 :=
    (Real.sqrt_lt' (by positivity)).mpr h2'
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (by positivity)]
  linarith

end Erdos539

#print axioms Erdos539.erdos_539.variants.sq_isBigO
