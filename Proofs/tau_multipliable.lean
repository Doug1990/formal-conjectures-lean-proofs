import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Data.PNat.Interval

namespace RamanujanTau

open PowerSeries PowerSeries.WithPiTopology

noncomputable def Δ : PowerSeries ℤ := X * ∏' (n : ℕ+), (1 - X ^ (n : ℕ)) ^ 24

noncomputable def τ (n : ℕ) : ℤ := PowerSeries.coeff n Δ

/-- `X ^ n` divides `(1 - X ^ n) ^ k - 1`. -/
theorem X_pow_dvd (n k : ℕ) :
    (X ^ n : PowerSeries ℤ) ∣ (1 - X ^ n) ^ k - 1 := by
  have h := sub_dvd_pow_sub_pow (1 - X ^ n : PowerSeries ℤ) 1 k
  rw [one_pow, sub_sub_cancel_left] at h
  exact neg_dvd.1 h

lemma multipliable : Multipliable fun n : ℕ+ ↦ ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ) := by
  have h := multipliable_one_add_of_tendsto_order_atTop_nhds_top (R := ℤ)
    (f := fun n : ℕ+ ↦ ((1 - X ^ (n : ℕ)) ^ 24 - 1 : PowerSeries ℤ)) ?_
  · simpa only [add_sub_cancel] using h
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr
    (fun m ↦ Filter.eventually_atTop.mpr ⟨⟨m + 1, m.succ_pos⟩, ?_⟩)
  intro n hn
  have hn' : m + 1 ≤ (n : ℕ) := (PNat.coe_le_coe _ _).2 hn
  calc ((m : ℕ) : ℕ∞) < ((n : ℕ) : ℕ∞) := by exact_mod_cast (by omega : m < (n : ℕ))
    _ ≤ _ := nat_le_order _ _ (X_pow_dvd_iff.1 (X_pow_dvd (n : ℕ) 24))

end RamanujanTau

#print axioms RamanujanTau.multipliable
