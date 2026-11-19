import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecificLimits.Normed

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
      = ∑ v, ∑ x, (if G.Adj x v then 1 else 0) :=
    Finset.sum_congr rfl (fun v _ => Finset.card_filter _ _)
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
    have hin : ∀ v, 2 ^ (n + 1) - 1 ≤ (univ.filter fun x => G.Adj x v).card := by
      intro v
      set A := univ.filter fun x => G.Adj x v with hA
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

namespace F3

open Finset Filter Topology

/-- Counting functions through an injective restriction. -/
theorem count {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (φ : β → α)
    (hφ : Function.Injective φ) (P : (β → Bool) → Prop) [DecidablePred P] :
    (univ.filter fun σ : α → Bool => P (σ ∘ φ)).card * 2 ^ Fintype.card β
      = (univ.filter P).card * 2 ^ Fintype.card α := by
  classical
  let e1 := Equiv.piEquivPiSubtypeProd (fun a => a ∈ Set.range φ) (fun _ => Bool)
  let e2 : (Set.range φ → Bool) ≃ (β → Bool) :=
    Equiv.arrowCongr (Equiv.ofInjective φ hφ).symm (Equiv.refl Bool)
  let e := e1.trans (Equiv.prodCongr e2 (Equiv.refl _))
  have he : ∀ σ, (e σ).1 = σ ∘ φ := fun σ => rfl
  have h1 : (univ.filter fun σ : α → Bool => P (σ ∘ φ)).card
      = (univ.filter fun q : (β → Bool) × ({a // a ∉ Set.range φ} → Bool) => P q.1).card := by
    apply Finset.card_equiv e
    intro σ
    simp only [mem_filter, mem_univ, true_and, he]
  have h2 : (univ.filter fun q : (β → Bool) × ({a // a ∉ Set.range φ} → Bool) => P q.1)
      = (univ.filter P) ×ˢ (univ : Finset ({a // a ∉ Set.range φ} → Bool)) := by
    ext q; simp
  have h3 : 2 ^ Fintype.card α
      = 2 ^ Fintype.card β * Fintype.card ({a // a ∉ Set.range φ} → Bool) := by
    have := Fintype.card_congr e
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool] at this
    rw [this, Fintype.card_fun, Fintype.card_bool]
  rw [h1, h2, card_product, card_univ, h3]
  ring

/-- Number of `g` such that every row differs from a forbidden row. -/
theorem countP {O E' : Type} [Fintype O] [Fintype E'] [DecidableEq O] [DecidableEq E']
    (c : O → E' → Bool) :
    (univ.filter fun g : O × E' → Bool => ∀ x, ∃ e, g (x, e) ≠ c x e).card
      = (2 ^ Fintype.card E' - 1) ^ Fintype.card O := by
  classical
  have h1 : (univ.filter fun g : O × E' → Bool => ∀ x, ∃ e, g (x, e) ≠ c x e).card
      = (Fintype.piFinset fun x => (univ : Finset (E' → Bool)).erase (c x)).card := by
    apply Finset.card_equiv (Equiv.curry O E' Bool)
    intro g
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, mem_erase, and_true,
      ne_eq, funext_iff, not_forall]
    rfl
  rw [h1, Fintype.card_piFinset]
  rw [Finset.prod_congr rfl (fun x _ => by
    rw [Finset.card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun, Fintype.card_bool])]
  rw [Finset.prod_const, card_univ]

/-- The tournament encoded by `σ`. -/
def T (m : ℕ) (σ : Fin m × Fin m → Bool) : Digraph (Fin m) :=
  ⟨fun x y => x ≠ y ∧ (if x < y then σ (x, y) = true else σ (y, x) = false)⟩

instance (m : ℕ) (σ : Fin m × Fin m → Bool) : DecidableRel (T m σ).Adj := fun x y =>
  show Decidable (x ≠ y ∧ (if x < y then σ (x, y) = true else σ (y, x) = false)) from
    inferInstance

theorem T_tour (m : ℕ) (σ : Fin m × Fin m → Bool) : (T m σ).IsTournament := by
  refine ⟨fun v h => h.1 rfl, fun u v huv => ?_⟩
  rcases lt_or_gt_of_ne huv with h | h
  · have h' : ¬ v < u := not_lt_of_gt h
    simp only [T, ne_eq, huv, not_false_eq_true, true_and, if_pos h, Ne.symm huv, if_neg h']
    cases σ (u, v) <;> simp
  · have h' : ¬ u < v := not_lt_of_gt h
    simp only [T, ne_eq, huv, not_false_eq_true, true_and, if_pos h, Ne.symm huv, if_neg h']
    cases σ (v, u) <;> simp

def pos {m : ℕ} (x e : Fin m) : Fin m × Fin m := if x < e then (x, e) else (e, x)

theorem adj_iff {m : ℕ} (σ : Fin m × Fin m → Bool) (x e : Fin m) (h : x ≠ e) :
    (T m σ).Adj x e ↔ σ (pos x e) = decide (x < e) := by
  by_cases hxe : x < e
  · simp [T, pos, hxe, h]
  · simp [T, pos, hxe, h]

theorem pos_inj {m : ℕ} (E : Finset (Fin m)) :
    Function.Injective (fun p : {x // x ∈ Eᶜ} × {e // e ∈ E} => pos p.1.1 p.2.1) := by
  rintro ⟨⟨x, hx⟩, ⟨e, he⟩⟩ ⟨⟨x', hx'⟩, ⟨e', he'⟩⟩ h
  rw [mem_compl] at hx hx'
  simp only [pos] at h
  split_ifs at h with h1 h2 h2
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact absurd he' hx
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact absurd he hx'
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl

/-- The set of `σ` for which `E` is not dominated. -/
theorem bad_count (m n : ℕ) (E : Finset (Fin m)) (hE : E.card = n) :
    (univ.filter fun σ : Fin m × Fin m → Bool =>
        ∀ x ∉ E, ¬ ∀ e ∈ E, (T m σ).Adj x e).card * 2 ^ ((m - n) * n)
      = (2 ^ n - 1) ^ (m - n) * 2 ^ (m * m) := by
  classical
  have hO : Fintype.card {x // x ∈ Eᶜ} = m - n := by
    rw [Fintype.card_coe, card_compl, Fintype.card_fin, hE]
  have hE' : Fintype.card {e // e ∈ E} = n := by rw [Fintype.card_coe, hE]
  have hfilt : (univ.filter fun σ : Fin m × Fin m → Bool =>
        ∀ x ∉ E, ¬ ∀ e ∈ E, (T m σ).Adj x e)
      = univ.filter fun σ : Fin m × Fin m → Bool =>
        (fun g : {x // x ∈ Eᶜ} × {e // e ∈ E} → Bool =>
          ∀ x, ∃ e, g (x, e) ≠ (fun x e => decide (x.1 < e.1)) x e)
        (σ ∘ fun p => pos p.1.1 p.2.1) := by
    apply Finset.filter_congr
    intro σ _
    constructor
    · rintro h ⟨x, hx⟩
      have hx' : x ∉ E := mem_compl.1 hx
      have := h x hx'
      push Not at this
      obtain ⟨e, he, hne⟩ := this
      refine ⟨⟨e, he⟩, ?_⟩
      have hxe : x ≠ e := fun h => hx' (h ▸ he)
      rw [adj_iff σ x e hxe] at hne
      exact hne
    · intro h x hx hall
      obtain ⟨⟨e, he⟩, hne⟩ := h ⟨x, mem_compl.2 hx⟩
      have hxe : x ≠ e := fun h => hx (h ▸ he)
      exact hne ((adj_iff σ x e hxe).1 (hall e he))
  rw [hfilt]
  have := count (fun p : {x // x ∈ Eᶜ} × {e // e ∈ E} => pos p.1.1 p.2.1) (pos_inj E)
    (fun g => ∀ x, ∃ e, g (x, e) ≠ (fun x e => decide (x.1 < e.1)) x e)
  rw [Fintype.card_prod, hO, hE', Fintype.card_prod, Fintype.card_fin, countP, hO, hE'] at this
  exact this

/-- Polynomial vs exponential. -/
theorem exists_t (n : ℕ) (hn : 1 ≤ n) :
    ∃ t, n ≤ t ∧ (2 * t) ^ n * (2 ^ n - 1) ^ t < (2 ^ n) ^ t := by
  have hq : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have ha : ((2 ^ n - 1 : ℕ) : ℝ) = 2 ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  set a : ℝ := 2 ^ n - 1 with ha_def
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  set r : ℝ := 2 ^ n / a with hr_def
  have hr : 1 < r := by rw [hr_def, lt_div_iff₀ ha0]; linarith
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt n hr
  have hpos : (0 : ℝ) < 1 / 2 ^ n := by positivity
  have hev := (tendsto_order.1 hlim).2 _ hpos
  obtain ⟨t, ht2, ht1⟩ := (hev.and (eventually_ge_atTop n)).exists
  refine ⟨t, ht1, ?_⟩
  have hrt : 0 < r ^ t := by positivity
  have key : (t : ℝ) ^ n * 2 ^ n < r ^ t := by
    rw [div_lt_iff₀ hrt] at ht2
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    calc (t : ℝ) ^ n * 2 ^ n < 1 / 2 ^ n * r ^ t * 2 ^ n := by
          exact mul_lt_mul_of_pos_right ht2 h2
      _ = r ^ t := by field_simp
  have key2 : ((2 * t) ^ n * (2 ^ n - 1) ^ t : ℕ) < (((2 ^ n) ^ t : ℕ) : ℝ) := by
    have hat : (0 : ℝ) < a ^ t := by positivity
    rw [hr_def, div_pow, lt_div_iff₀ hat] at key
    push_cast
    rw [ha, mul_pow]
    calc (2 : ℝ) ^ n * (t : ℝ) ^ n * a ^ t = (t : ℝ) ^ n * 2 ^ n * a ^ t := by ring
      _ < _ := key
  exact_mod_cast key2

theorem exists_S (n : ℕ) :
    ∃ m, n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, by omega, T 1 (fun _ => true), T_tour 1 _, ?_⟩
    intro E hE
    rw [Finset.card_eq_zero] at hE
    subst hE
    exact ⟨0, by simp, by simp⟩
  obtain ⟨t, htn, ht⟩ := exists_t n hn
  refine ⟨n + t, by omega, ?_⟩
  by_contra hno
  push Not at hno
  set m := n + t with hm
  have hall : ∀ σ : Fin m × Fin m → Bool, ∃ E ∈ powersetCard n (univ : Finset (Fin m)),
      σ ∈ univ.filter fun σ : Fin m × Fin m → Bool => ∀ x ∉ E, ¬ ∀ e ∈ E, (T m σ).Adj x e := by
    intro σ
    have h := hno (T m σ) (T_tour m σ)
    unfold HasPropertyS at h
    push Not at h
    obtain ⟨E, hE, hbad⟩ := h
    refine ⟨E, mem_powersetCard.2 ⟨subset_univ _, hE⟩, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    intro x hx hall
    obtain ⟨e, he, hne⟩ := hbad x hx
    exact hne (hall e he)
  have hsub : (univ : Finset (Fin m × Fin m → Bool)) ⊆ (powersetCard n univ).biUnion
      (fun E => univ.filter fun σ : Fin m × Fin m → Bool =>
        ∀ x ∉ E, ¬ ∀ e ∈ E, (T m σ).Adj x e) := by
    intro σ _
    obtain ⟨E, hE, h⟩ := hall σ
    exact mem_biUnion.2 ⟨E, hE, h⟩
  have hcard := (card_le_card hsub).trans card_biUnion_le
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_prod, Fintype.card_fin] at hcard
  have hmul := Nat.mul_le_mul_right (2 ^ ((m - n) * n)) hcard
  rw [Finset.sum_mul, Finset.sum_congr rfl (fun E hE => bad_count m n E
    (mem_powersetCard.1 hE).2), Finset.sum_const, card_powersetCard, card_univ,
    Fintype.card_fin, smul_eq_mul] at hmul
  have hmt : m - n = t := by omega
  rw [hmt] at hmul
  -- hmul : 2^(m*m) * 2^(t*n) ≤ C(m,n) * ((2^n-1)^t * 2^(m*m))
  have h2 : 2 ^ (t * n) ≤ m.choose n * (2 ^ n - 1) ^ t := by
    have hp : 0 < 2 ^ (m * m) := by positivity
    have : 2 ^ (m * m) * 2 ^ (t * n) ≤ 2 ^ (m * m) * (m.choose n * (2 ^ n - 1) ^ t) := by
      calc 2 ^ (m * m) * 2 ^ (t * n) ≤ m.choose n * ((2 ^ n - 1) ^ t * 2 ^ (m * m)) := hmul
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hp
  have h3 : m.choose n ≤ (2 * t) ^ n :=
    (Nat.choose_le_pow m n).trans (Nat.pow_le_pow_left (by omega) n)
  have h4 : 2 ^ (t * n) = (2 ^ n) ^ t := by rw [← pow_mul, mul_comm]
  have h5 := Nat.mul_le_mul_right ((2 ^ n - 1) ^ t) h3
  have h6 := lt_of_le_of_lt (h2.trans h5) ht
  rw [h4] at h6
  exact lt_irrefl _ h6

end F3

theorem erdos_902.variants.erdos_lower (n : ℕ) : 2 ^ (n + 1) - 1 ≤ f n := by
  have hne : {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n}.Nonempty :=
    F3.exists_S n
  obtain ⟨hn, G, hG, hS⟩ : f n ∈
      {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n} :=
    Nat.sInf_mem hne
  have := F2.main n (Fin (f n)) G hG hS (by simpa using hn)
  simpa using this

end Erdos902

#print axioms Erdos902.erdos_902.variants.erdos_lower
