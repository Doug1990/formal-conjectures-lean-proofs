import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Nat

variable {α : Type*} [AddCommMonoid α]

def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

def ContainsMonoAPofLength {κ : Type} [Finite κ] {M : Set α}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : Set M, ((·.1) '' ap).IsAPOfLength k ∧
    ∀ m ∈ ap, coloring m = c

namespace Erdos138

def monoAP_guarantee_set (r k : ℕ) : Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k}

namespace V

open Combinatorics in
/-- Finite van der Waerden theorem, derived from Hales–Jewett. -/
theorem vdw_fin (r k : ℕ) : ∃ N, ∀ C : ℕ → Fin r, ∃ a d : ℕ, ∃ c : Fin r, 0 < d ∧
    ∀ n < k, C (a + n * d) = c ∧ 1 ≤ a + n * d ∧ a + n * d ≤ N := by
  classical
  obtain ⟨ι, _inst, hι⟩ := Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  refine ⟨1 + Fintype.card ι * k, fun C => ?_⟩
  obtain ⟨l, c, hl⟩ := hι fun v => C (1 + ∑ i, ((v i : Fin k) : ℕ))
  set s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none) with hs
  have key : ∀ x : Fin k, ∑ i, ((l x i : Fin k) : ℕ) =
      s.card * (x : ℕ) + ∑ i ∈ sᶜ, (((l.idxFun i).map Fin.val).getD 0) := by
    intro x
    rw [← Finset.sum_add_sum_compl s]
    congr 1
    · rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hs, Finset.mem_filter] at hi
      rw [l.apply_none _ _ hi.2]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.2
      rw [l.apply_some hy.symm, ← hy]
      rfl
  have bound : ∀ x : Fin k, ∑ i, ((l x i : Fin k) : ℕ) ≤ Fintype.card ι * k := by
    intro x
    calc ∑ i, ((l x i : Fin k) : ℕ) ≤ ∑ _i : ι, k :=
          Finset.sum_le_sum fun i _ => (l x i).isLt.le
      _ = Fintype.card ι * k := by simp
  refine ⟨1 + ∑ i ∈ sᶜ, (((l.idxFun i).map Fin.val).getD 0), s.card, c, ?_, ?_⟩
  · exact Finset.card_pos.mpr ⟨l.proper.choose, by
      rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, l.proper.choose_spec⟩⟩
  · intro n hn
    have e := key ⟨n, hn⟩
    have b := bound ⟨n, hn⟩
    have hc := hl ⟨n, hn⟩
    have eq : 1 + ∑ i ∈ sᶜ, (((l.idxFun i).map Fin.val).getD 0) + n * s.card =
        1 + ∑ i, ((l ⟨n, hn⟩ i : Fin k) : ℕ) := by
      rw [e]; ring
    rw [eq]
    exact ⟨hc, Nat.le_add_right _ _, Nat.add_le_add_left b 1⟩

end V

theorem monoAP_guarantee_set_nonempty (r k) : (monoAP_guarantee_set r k).Nonempty := by
  obtain ⟨N, hN⟩ := V.vdw_fin r k
  refine ⟨N + 1, fun coloring => ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact (coloring ⟨1, by simp⟩).elim0
  classical
  let C : ℕ → Fin r := fun n =>
    if h : n ∈ Finset.Icc 1 (N + 1) then coloring ⟨n, h⟩ else ⟨0, hr⟩
  obtain ⟨a, d, c, hd, h⟩ := hN C
  have mem : ∀ n < k, a + n * d ∈ Finset.Icc 1 (N + 1) := fun n hn => by
    obtain ⟨-, h1, h2⟩ := h n hn
    exact Finset.mem_Icc.mpr ⟨h1, Nat.le_succ_of_le h2⟩
  have inj : Function.Injective (fun n : ℕ => a + n * d) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hxy)
  have himg : ((fun x : ((Finset.Icc 1 (N + 1) : Finset ℕ) : Set ℕ) => x.1) ''
      {m : ((Finset.Icc 1 (N + 1) : Finset ℕ) : Set ℕ) | ∃ n < k, m.1 = a + n * d}) =
      (((Finset.range k).image (fun n => a + n * d) : Finset ℕ) : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨m, ⟨n, hn, hm⟩, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, hm.symm⟩)
    · intro hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact ⟨⟨_, mem n (Finset.mem_range.mp hn)⟩, ⟨n, Finset.mem_range.mp hn, rfl⟩, rfl⟩
  refine ⟨c, {m | ∃ n < k, m.1 = a + n * d}, ⟨a, d, ?_, ?_⟩, ?_⟩
  · show Set.encard _ = _
    rw [himg, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ inj,
      Finset.card_range]
  · rw [himg]
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact ⟨n, by exact_mod_cast Finset.mem_range.mp hn, by rw [smul_eq_mul]⟩
    · rintro ⟨n, hn, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨n, Finset.mem_range.mpr (by exact_mod_cast hn), by rw [smul_eq_mul]⟩)
  · rintro ⟨m, hm⟩ ⟨n, hn, e⟩
    obtain ⟨hc, -, -⟩ := h n hn
    simp only at e
    subst e
    rw [← hc]
    simp only [C]
    rw [dif_pos (Finset.mem_coe.mp hm)]

end Erdos138

#print axioms Erdos138.monoAP_guarantee_set_nonempty
