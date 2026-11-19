import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset

namespace SuffixPrefixAvoidance

variable {n q : ℕ}

/-- The suffix of a word `w : Fin n → Fin q` of length `k + 1` (the last `k + 1` characters). -/
def wordSuffix (w : Fin n → Fin q) (k : Fin n) : Fin (k + 1) → Fin q :=
  fun i => w ⟨n - k - 1 + i, by omega⟩

/-- The prefix of a word `w : Fin n → Fin q` of length `k + 1` (the first `k + 1` characters). -/
def wordPrefix (w : Fin n → Fin q) (k : Fin n) : Fin (k + 1) → Fin q :=
  fun i => w ⟨i, by omega⟩

def IsSuffixPrefixAvoiding (A B : Finset (Fin n → Fin q)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ k : Fin n, wordSuffix a k ≠ wordPrefix b k

/-- Cyclic left shift by `k` of the concatenation `a ++ b`. -/
def rot (k : Fin n) (a b : Fin n → Fin q) : Fin (2 * n) → Fin q :=
  fun i => if h1 : i.1 + k.1 < n then a ⟨i.1 + k.1, h1⟩
    else if h2 : i.1 + k.1 < 2 * n then b ⟨i.1 + k.1 - n, by omega⟩
    else a ⟨i.1 + k.1 - 2 * n, by have := i.2; have := k.2; omega⟩

lemma rot_a (k : Fin n) (a b : Fin n → Fin q) (i : Fin (2 * n)) (m : Fin n)
    (hm : i.1 + k.1 = m.1) : rot k a b i = a m := by
  have := m.2
  unfold rot
  rw [dif_pos (show i.1 + k.1 < n by omega)]
  exact congrArg a (Fin.ext (by dsimp only; omega))

lemma rot_b (k : Fin n) (a b : Fin n → Fin q) (i : Fin (2 * n)) (m : Fin n)
    (hm : i.1 + k.1 = n + m.1) : rot k a b i = b m := by
  have := m.2
  unfold rot
  rw [dif_neg (show ¬ (i.1 + k.1 < n) by omega), dif_pos (show i.1 + k.1 < 2 * n by omega)]
  exact congrArg b (Fin.ext (by dsimp only; omega))

lemma rot_c (k : Fin n) (a b : Fin n → Fin q) (i : Fin (2 * n)) (m : Fin n)
    (hm : i.1 + k.1 = 2 * n + m.1) : rot k a b i = a m := by
  have := m.2
  unfold rot
  rw [dif_neg (show ¬ (i.1 + k.1 < n) by omega), dif_neg (show ¬ (i.1 + k.1 < 2 * n) by omega)]
  exact congrArg a (Fin.ext (by dsimp only; omega))

lemma rot_inj (k : Fin n) (a b a' b' : Fin n → Fin q) (h : rot k a b = rot k a' b') :
    a = a' ∧ b = b' := by
  have hk := k.2
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · have hj := j.2
    by_cases hjk : k.1 ≤ j.1
    · have e := congrFun h ⟨j.1 - k.1, by omega⟩
      rwa [rot_a k a b _ j (by dsimp only; omega), rot_a k a' b' _ j (by dsimp only; omega)] at e
    · have e := congrFun h ⟨j.1 + 2 * n - k.1, by omega⟩
      rwa [rot_c k a b _ j (by dsimp only; omega), rot_c k a' b' _ j (by dsimp only; omega)] at e
  · have hj := j.2
    have e := congrFun h ⟨n + j.1 - k.1, by omega⟩
    rwa [rot_b k a b _ j (by dsimp only; omega), rot_b k a' b' _ j (by dsimp only; omega)] at e

lemma rot_disj {A B : Finset (Fin n → Fin q)} (h : IsSuffixPrefixAvoiding A B)
    (k k' : Fin n) (hlt : k.1 < k'.1) (a b a' b' : Fin n → Fin q) (ha : a ∈ A) (hb' : b' ∈ B)
    (hEq : rot k a b = rot k' a' b') : False := by
  have hk := k'.2
  apply h a ha b' hb' ⟨k'.1 - k.1 - 1, by omega⟩
  funext t
  have ht : t.1 < k'.1 - k.1 := by have := t.2; dsimp only at this; omega
  have e1 := rot_a k a b ⟨n - k'.1 + t.1, by omega⟩ ⟨n - (k'.1 - k.1 - 1) - 1 + t.1, by omega⟩
    (by dsimp only; omega)
  have e2 := rot_b k' a' b' ⟨n - k'.1 + t.1, by omega⟩ ⟨t.1, by omega⟩ (by dsimp only; omega)
  have e3 := congrFun hEq ⟨n - k'.1 + t.1, by omega⟩
  exact e1.symm.trans (e3.trans e2)

theorem suffix_prefix_avoidance_weaker_bound
    (A B : Finset (Fin n → Fin q))
    (_hq : 0 < q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (A.card : ℚ) * B.card ≤ (q : ℚ) ^ (2 * n) / n := by
  have hinj : Set.InjOn (fun x : Fin n × (Fin n → Fin q) × (Fin n → Fin q) =>
      rot x.1 x.2.1 x.2.2)
      (↑((univ : Finset (Fin n)) ×ˢ (A ×ˢ B)) :
        Set (Fin n × (Fin n → Fin q) × (Fin n → Fin q))) := by
    rintro ⟨k, a, b⟩ hx ⟨k', a', b'⟩ hy hF
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product] at hx hy
    obtain ⟨-, ha, hb⟩ := hx
    obtain ⟨-, ha', hb'⟩ := hy
    have hF' : rot k a b = rot k' a' b' := hF
    rcases lt_trichotomy k.1 k'.1 with hlt | heq | hgt
    · exact (rot_disj h k k' hlt a b a' b' ha hb' hF').elim
    · have : k = k' := Fin.ext heq
      subst this
      obtain ⟨rfl, rfl⟩ := rot_inj k a b a' b' hF'
      rfl
    · exact (rot_disj h k' k hgt a' b' a b ha' hb hF'.symm).elim
  have key : n * (A.card * B.card) ≤ q ^ (2 * n) := by
    calc n * (A.card * B.card) = (univ ×ˢ (A ×ˢ B)).card := by
          simp [card_product]
      _ = ((univ ×ˢ (A ×ˢ B)).image (fun x : Fin n × (Fin n → Fin q) × (Fin n → Fin q) =>
            rot x.1 x.2.1 x.2.2)).card := (card_image_of_injOn hinj).symm
      _ ≤ (univ : Finset (Fin (2 * n) → Fin q)).card := card_le_univ _
      _ = q ^ (2 * n) := by simp
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  calc (A.card : ℚ) * B.card * n = ((n * (A.card * B.card) : ℕ) : ℚ) := by push_cast; ring
    _ ≤ ((q ^ (2 * n) : ℕ) : ℚ) := by exact_mod_cast key
    _ = (q : ℚ) ^ (2 * n) := by push_cast; rfl

end SuffixPrefixAvoidance

#print axioms SuffixPrefixAvoidance.suffix_prefix_avoidance_weaker_bound
