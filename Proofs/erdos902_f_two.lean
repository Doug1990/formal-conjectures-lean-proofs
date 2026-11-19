import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

/-- Local restatement of `Digraph.IsTournament` (FormalConjecturesForMathlib). -/
def Digraph.IsTournament {V : Type*} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ (∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u))

namespace Erdos902

def HasPropertyS {V : Type*} (G : Digraph V) (n : ℕ) : Prop :=
  ∀ E : Finset V, E.card = n → ∃ x ∉ E, ∀ e ∈ E, G.Adj x e

noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n}

namespace F2

open Finset

/-- In a tournament the in-degrees sum to `m(m-1)/2`. -/
theorem sum_in {V : Type*} [Fintype V] (G : Digraph V) (hG : G.IsTournament) [DecidableEq V]
    [DecidableRel G.Adj] :
    2 * ∑ v, (univ.filter fun x => G.Adj x v).card = Fintype.card V * (Fintype.card V - 1) := by
  have h1 : ∑ v, (univ.filter fun x => G.Adj x v).card
      = ∑ v, ∑ x, (if G.Adj x v then 1 else 0) := by
    simp [Finset.card_filter]
  have h2 : ∑ v : V, ∑ x : V, (if G.Adj x v then 1 else 0)
      = ∑ v : V, ∑ x : V, (if G.Adj v x then 1 else 0) := Finset.sum_comm
  have h3 : ∀ v x : V, (if G.Adj x v then 1 else 0) + (if G.Adj v x then 1 else 0)
      = (if x = v then 0 else 1) := by
    intro v x
    by_cases hxv : x = v
    · subst hxv; simp [hG.1 x]
    · have := hG.2 x v hxv
      by_cases h : G.Adj x v
      · simp [h, this.1 h, hxv]
      · have h' : G.Adj v x := by
          by_contra h''
          exact h (this.2 h'')
        simp [h, h', hxv]
  have h4 : ∀ v : V, ∑ x : V, (if x = v then 0 else 1) = Fintype.card V - 1 := by
    intro v
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const_nat (fun _ _ => rfl),
      mul_one]
    rw [Finset.filter_ne' univ v, Finset.card_erase_of_mem (mem_univ v), Finset.card_univ]
  rw [two_mul, h1]
  conv_lhs => arg 2; rw [h2]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, h3, h4]
  rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]

theorem main (n : ℕ) : ∀ (V : Type) [Fintype V] (G : Digraph V), G.IsTournament →
    HasPropertyS G n → n ≤ Fintype.card V → 2 ^ (n + 1) - 1 ≤ Fintype.card V := by
  induction n with
  | zero =>
    intro V _ G _ hS _
    obtain ⟨x, -, -⟩ := hS ∅ rfl
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
    show 1 ≤ Fintype.card V
    omega
  | succ n ih =>
    intro V _ G hG hS hn
    classical
    -- every in-neighbourhood has at least `2^(n+1) - 1` vertices
    have hin : ∀ v, 2 ^ (n + 1) - 1 ≤ (univ.filter fun x => G.Adj x v).card := by
      intro v
      set A := univ.filter fun x => G.Adj x v with hA
      -- |A| ≥ n
      have hAn : n ≤ A.card := by
        by_contra hlt
        push Not at hlt
        have hs : (insert v A).card ≤ n + 1 := by
          have := Finset.card_insert_le v A
          omega
        obtain ⟨E, hsE, hE⟩ := Finset.exists_superset_card_eq hs hn
        obtain ⟨x, hxE, hx⟩ := hS E hE
        have hxv : G.Adj x v := hx v (hsE (mem_insert_self v A))
        exact hxE (hsE (mem_insert_of_mem (by simp [hA, hxv])))
      let G' : Digraph {x // G.Adj x v} := ⟨fun a b => G.Adj a.1 b.1⟩
      have hG' : G'.IsTournament := by
        refine ⟨fun a => hG.1 a.1, fun a b hab => hG.2 a.1 b.1 ?_⟩
        intro h; exact hab (Subtype.ext h)
      have hS' : HasPropertyS G' n := by
        intro E' hE'
        let E : Finset V := insert v (E'.map (Function.Embedding.subtype _))
        have hvE : v ∉ E'.map (Function.Embedding.subtype _) := by
          simp only [mem_map, Function.Embedding.coe_subtype, not_exists, not_and]
          intro a _ hav
          have ha2 := a.2
          rw [hav] at ha2
          exact hG.1 v ha2
        have hEc : E.card = n + 1 := by
          rw [Finset.card_insert_of_notMem hvE, Finset.card_map, hE']
        obtain ⟨x, hxE, hx⟩ := hS E hEc
        have hxv : G.Adj x v := hx v (mem_insert_self _ _)
        refine ⟨⟨x, hxv⟩, ?_, ?_⟩
        · intro hm
          exact hxE (mem_insert_of_mem (mem_map_of_mem _ hm))
        · intro e he
          exact hx e.1 (mem_insert_of_mem (mem_map_of_mem (Function.Embedding.subtype _) he))
      have hcard : Fintype.card {x // G.Adj x v} = A.card := Fintype.card_subtype _
      have := ih {x // G.Adj x v} G' hG' hS' (by omega)
      omega
    have hsum := sum_in G hG
    have hle : Fintype.card V * (2 ^ (n + 1) - 1)
        ≤ ∑ v, (univ.filter fun x => G.Adj x v).card := by
      have := Finset.sum_le_sum (s := univ) (fun v _ => hin v)
      simpa [Finset.sum_const, Finset.card_univ] using this
    set m := Fintype.card V
    set k := 2 ^ (n + 1) with hk
    have hk1 : 1 ≤ k := Nat.one_le_two_pow
    have hpow : 2 ^ (n + 1 + 1) = 2 * k := by rw [pow_succ, hk, mul_comm]
    have hm : 0 < m := by omega
    have h2 : m * (2 * (k - 1)) ≤ m * (m - 1) := by
      rw [← hsum]
      calc m * (2 * (k - 1)) = 2 * (m * (k - 1)) := by ring
        _ ≤ _ := Nat.mul_le_mul_left 2 hle
    have h3 := Nat.le_of_mul_le_mul_left h2 hm
    rw [hpow]
    omega

end F2

theorem erdos_902.variants.f_two : f 2 = 7 := by
  apply le_antisymm
  · refine Nat.sInf_le ⟨by omega, ⟨fun a b => b - a ∈ ({1, 2, 4} : Finset (Fin 7))⟩,
      ⟨by decide, by decide⟩, ?_⟩
    intro E hE
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hE
    have key : ∀ a b : Fin 7, a ≠ b → ∃ x, x ≠ a ∧ x ≠ b ∧
        a - x ∈ ({1, 2, 4} : Finset (Fin 7)) ∧ b - x ∈ ({1, 2, 4} : Finset (Fin 7)) := by
      decide
    obtain ⟨x, hxa, hxb, ha, hb⟩ := key a b hab
    refine ⟨x, by simp [hxa, hxb], fun e he => ?_⟩
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ha
    · rw [Finset.mem_singleton.1 he]
      exact hb
  · refine le_csInf ⟨7, ?_⟩ ?_
    · refine ⟨by omega, ⟨fun a b => b - a ∈ ({1, 2, 4} : Finset (Fin 7))⟩,
        ⟨by decide, by decide⟩, ?_⟩
      intro E hE
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hE
      have key : ∀ a b : Fin 7, a ≠ b → ∃ x, x ≠ a ∧ x ≠ b ∧
          a - x ∈ ({1, 2, 4} : Finset (Fin 7)) ∧ b - x ∈ ({1, 2, 4} : Finset (Fin 7)) := by
        decide
      obtain ⟨x, hxa, hxb, ha, hb⟩ := key a b hab
      refine ⟨x, by simp [hxa, hxb], fun e he => ?_⟩
      rcases Finset.mem_insert.1 he with rfl | he
      · exact ha
      · rw [Finset.mem_singleton.1 he]
        exact hb
    · rintro m ⟨hm, G, hG, hS⟩
      have := F2.main 2 (Fin m) G hG hS (by simpa using hm)
      simpa using this

end Erdos902

#print axioms Erdos902.erdos_902.variants.f_two
