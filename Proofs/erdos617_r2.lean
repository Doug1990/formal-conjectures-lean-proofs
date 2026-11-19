import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination

namespace Erdos617

namespace R2

variable {q : ℕ} [Fact q.Prime]

/-- colour of a difference vector: its slope (vertical merged into slope 0). -/
def c (d : ZMod q × ZMod q) : Fin q :=
  ⟨(if d.1 = 0 then 0 else d.2 / d.1).val, ZMod.val_lt _⟩

lemma c_neg (d : ZMod q × ZMod q) : c (-d) = c d := by
  unfold c
  simp only [Prod.fst_neg, Prod.snd_neg, neg_eq_zero, neg_div_neg_eq]

def col : Sym2 (ZMod q × ZMod q) → Fin q :=
  Sym2.lift ⟨fun u v => c (v - u), fun u v => by
    show c (v - u) = c (u - v)
    rw [← c_neg (u - v), neg_sub]⟩

lemma col_mk (u v : ZMod q × ZMod q) : col s(u, v) = c (v - u) := rfl

lemma key (S : Finset (ZMod q × ZMod q)) (hS : S.card = q + 1) (k : Fin q) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ col s(u, v) = k := by
  set s : ZMod q := (k.val : ZMod q) with hs
  have hlt : (Finset.univ : Finset (ZMod q)).card < S.card := by
    rw [Finset.card_univ, ZMod.card, hS]; omega
  obtain ⟨u, hu, v, hv, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (f := fun x : ZMod q × ZMod q => x.2 - s * x.1) (fun _ _ => Finset.mem_univ _)
  refine ⟨u, hu, v, hv, hne, ?_⟩
  rw [col_mk]
  have h1 : (v - u).1 ≠ 0 := by
    intro h0
    apply hne
    have e1 : u.1 = v.1 := by
      have : v.1 - u.1 = 0 := h0
      exact (sub_eq_zero.mp this).symm
    have e2 : u.2 = v.2 := by
      have : u.2 - s * u.1 = v.2 - s * v.1 := heq
      rw [e1] at this
      exact sub_left_injective this
    exact Prod.ext e1 e2
  have h2 : (v - u).2 = s * (v - u).1 := by
    have : u.2 - s * u.1 = v.2 - s * v.1 := heq
    simp only [Prod.fst_sub, Prod.snd_sub]
    linear_combination (-1 : ZMod q) * this
  have h3 : (if (v - u).1 = 0 then 0 else (v - u).2 / (v - u).1) = s := by
    rw [if_neg h1, h2, mul_div_assoc, div_self h1, mul_one]
  apply Fin.ext
  show (if (v - u).1 = 0 then 0 else (v - u).2 / (v - u).1).val = k.val
  rw [h3, hs]
  exact ZMod.val_cast_of_lt k.isLt

end R2

theorem erdos_617.variants.r2 :
    {r : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V), Fintype.card V = r^2 ∧
      ∃ (coloring : Sym2 V → Fin r),
        ∀ (S : Finset V), S.card = r + 1 →
          ∀ (k : Fin r), ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k}.Infinite := by
  apply Nat.infinite_setOfPred_prime.mono
  intro q hq
  have : Fact q.Prime := ⟨hq⟩
  refine ⟨ZMod q × ZMod q, inferInstance, inferInstance, ?_, R2.col, R2.key⟩
  rw [Fintype.card_prod, ZMod.card, sq]

end Erdos617

#print axioms Erdos617.erdos_617.variants.r2
