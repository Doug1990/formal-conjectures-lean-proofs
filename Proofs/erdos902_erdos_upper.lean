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
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-- Local restatement of `Digraph.IsTournament` (FormalConjecturesForMathlib). -/
def Digraph.IsTournament {V : Type*} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ (∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u))

open Filter Asymptotics

namespace Erdos902

def HasPropertyS {V : Type*} (G : Digraph V) (n : ℕ) : Prop :=
  ∀ E : Finset V, E.card = n → ∃ x ∉ E, ∀ e ∈ E, G.Adj x e

noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n}

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

/-- Erdős's counting criterion for the existence of an `S_n` tournament on `m` vertices. -/
theorem exists_of (m n : ℕ)
    (h : m.choose n * (2 ^ n - 1) ^ (m - n) < (2 ^ n) ^ (m - n)) :
    ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n := by
  classical
  by_contra hno
  push Not at hno
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
  have h2 : 2 ^ ((m - n) * n) ≤ m.choose n * (2 ^ n - 1) ^ (m - n) := by
    have hp : 0 < 2 ^ (m * m) := by positivity
    have : 2 ^ (m * m) * 2 ^ ((m - n) * n)
        ≤ 2 ^ (m * m) * (m.choose n * (2 ^ n - 1) ^ (m - n)) := by
      calc 2 ^ (m * m) * 2 ^ ((m - n) * n)
          ≤ m.choose n * ((2 ^ n - 1) ^ (m - n) * 2 ^ (m * m)) := hmul
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hp
  have h4 : 2 ^ ((m - n) * n) = (2 ^ n) ^ (m - n) := by rw [← pow_mul, mul_comm]
  rw [h4] at h2
  exact absurd h (not_lt.2 h2)

end F3

namespace F4

open Filter Topology

/-- Real-analytic form of the counting criterion. -/
theorem ineq_nat (m n : ℕ) (hnm : n ≤ m) (hm : 0 < m)
    (h : (n : ℝ) * Real.log m < ((m : ℝ) - n) / 2 ^ n) :
    m.choose n * (2 ^ n - 1) ^ (m - n) < (2 ^ n) ^ (m - n) := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hN1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hk : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := Nat.cast_sub hnm
  have hc : ((2 ^ n - 1 : ℕ) : ℝ) = (2 : ℝ) ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : 0 ≤ 1 - 1 / (2 : ℝ) ^ n := by
    rw [sub_nonneg, div_le_one hN]; exact hN1
  have h2 : (1 - 1 / (2 : ℝ) ^ n) ^ (m - n) ≤ Real.exp (-(((m : ℝ) - n) / 2 ^ n)) := by
    have := Real.add_one_le_exp (-(1 / (2 : ℝ) ^ n))
    calc (1 - 1 / (2 : ℝ) ^ n) ^ (m - n) ≤ Real.exp (-(1 / (2 : ℝ) ^ n)) ^ (m - n) :=
          pow_le_pow_left₀ h1 (by linarith) _
      _ = Real.exp (((m - n : ℕ) : ℝ) * (-(1 / (2 : ℝ) ^ n))) := (Real.exp_nat_mul _ _).symm
      _ = _ := by rw [hk]; congr 1; ring
  have h3 : (m : ℝ) ^ n = Real.exp (n * Real.log m) := by
    rw [Real.exp_nat_mul, Real.exp_log hmR]
  have h4 : Real.exp (n * Real.log m) * Real.exp (-(((m : ℝ) - n) / 2 ^ n)) < 1 := by
    rw [← Real.exp_add, Real.exp_lt_one_iff]; linarith
  have h5 : ((2 : ℝ) ^ n - 1) ^ (m - n)
      = ((2 : ℝ) ^ n) ^ (m - n) * (1 - 1 / (2 : ℝ) ^ n) ^ (m - n) := by
    rw [← mul_pow, mul_sub, mul_one, mul_one_div_cancel hN.ne']
  have hch : (m.choose n : ℝ) ≤ (m : ℝ) ^ n := by exact_mod_cast Nat.choose_le_pow m n
  have key : (m.choose n : ℝ) * ((2 : ℝ) ^ n - 1) ^ (m - n) < ((2 : ℝ) ^ n) ^ (m - n) := by
    rw [h5]
    have hP : 0 < ((2 : ℝ) ^ n) ^ (m - n) := by positivity
    have hq : 0 ≤ (1 - 1 / (2 : ℝ) ^ n) ^ (m - n) := pow_nonneg h1 _
    calc (m.choose n : ℝ) * (((2 : ℝ) ^ n) ^ (m - n) * (1 - 1 / (2 : ℝ) ^ n) ^ (m - n))
        ≤ (m : ℝ) ^ n * (((2 : ℝ) ^ n) ^ (m - n) * Real.exp (-(((m : ℝ) - n) / 2 ^ n))) := by
          apply mul_le_mul hch (mul_le_mul_of_nonneg_left h2 hP.le) (by positivity)
            (by positivity)
      _ = ((2 : ℝ) ^ n) ^ (m - n)
          * (Real.exp (n * Real.log m) * Real.exp (-(((m : ℝ) - n) / 2 ^ n))) := by
          rw [h3]; ring
      _ < ((2 : ℝ) ^ n) ^ (m - n) * 1 := mul_lt_mul_of_pos_left h4 hP
      _ = _ := mul_one _
  rw [← hc] at key
  exact_mod_cast key

/-- The asymptotic inequality needed for the upper bound. -/
theorem ev_ineq (ε : ℝ) (hε : 0 < ε) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 5 ≤ ε * (n : ℝ) ^ 2 ∧
      (n : ℝ) * c + 2 * n * Real.log n + 1 < ε * (n : ℝ) ^ 2 := by
  have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ 1 / (1 * (n : ℝ) + 0)) atTop (𝓝 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have h2 := (tendsto_order.1 h1).2 (ε / 5) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (c * 5 / ε) (5 / ε))
  filter_upwards [h2, eventually_ge_atTop (N + 1)] with n hn hnN
  have hnN' : (N : ℝ) + 1 ≤ n := by exact_mod_cast hnN
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hgt1 : c * 5 / ε < n := lt_of_le_of_lt (le_max_left _ _) (by linarith)
  have hgt2 : 5 / ε < n := lt_of_le_of_lt (le_max_right _ _) (by linarith)
  rw [div_lt_iff₀ hε] at hgt1 hgt2
  simp only [pow_one, one_mul, add_zero] at hn
  rw [div_lt_iff₀ hn0] at hn
  have h5 : 5 ≤ ε * (n : ℝ) ^ 2 := by nlinarith
  refine ⟨by omega, h5, ?_⟩
  have e1 := mul_lt_mul_of_pos_left hgt1 hn0
  have e2 := mul_lt_mul_of_pos_left hn hn0
  nlinarith

theorem step (n : ℕ) (c ε : ℝ) (hc : c = Real.log 2 + ε) (hl2 : 0 < Real.log 2)
    (hε : 0 < ε) (hn1 : 1 ≤ n) (hn5 : 5 ≤ ε * (n : ℝ) ^ 2)
    (hineq : (n : ℝ) * Real.log c + 2 * n * Real.log n + 1 < ε * (n : ℝ) ^ 2) :
    (f n : ℝ) ≤ c * n ^ 2 * 2 ^ n := by
  have hc0 : 0 < c := by rw [hc]; linarith
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hnN : (n : ℝ) + 1 ≤ 2 ^ n := by
    have h : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    exact_mod_cast h
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hεc : ε ≤ c := by rw [hc]; linarith
  have hx5 : 5 * (2 : ℝ) ^ n ≤ c * n ^ 2 * 2 ^ n := by
    apply mul_le_mul_of_nonneg_right _ hN.le
    nlinarith [sq_nonneg (n : ℝ)]
  have hx0 : 0 ≤ c * (n : ℝ) ^ 2 * 2 ^ n := by positivity
  have hnx : (n : ℝ) ≤ c * n ^ 2 * 2 ^ n := by linarith
  obtain ⟨m, hnm, hmx, hxm⟩ : ∃ m : ℕ, n ≤ m ∧ (m : ℝ) ≤ c * n ^ 2 * 2 ^ n ∧
      c * n ^ 2 * 2 ^ n < (m : ℝ) + 1 :=
    ⟨_, Nat.le_floor hnx, Nat.floor_le hx0, Nat.lt_floor_add_one _⟩
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : Real.log m ≤ Real.log c + 2 * Real.log n + n * Real.log 2 := by
    calc Real.log m ≤ Real.log (c * n ^ 2 * 2 ^ n) := Real.log_le_log hmR hmx
      _ = _ := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        push_cast; ring
  have hA' : (n : ℝ) * Real.log m
      ≤ n * Real.log c + 2 * n * Real.log n + n ^ 2 * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hlog hn0.le
    calc _ ≤ _ := this
      _ = _ := by ring
  have hcn : c * (n : ℝ) ^ 2 = Real.log 2 * n ^ 2 + ε * n ^ 2 := by rw [hc]; ring
  have hA : (n : ℝ) * Real.log m < c * n ^ 2 - 1 := by linarith
  have key : (n : ℝ) * Real.log m < ((m : ℝ) - n) / 2 ^ n := by
    rw [lt_div_iff₀ hN]
    have hB : (c * n ^ 2 - 1) * 2 ^ n ≤ (m : ℝ) - n := by
      have : (c * (n : ℝ) ^ 2 - 1) * 2 ^ n = c * n ^ 2 * 2 ^ n - 2 ^ n := by ring
      rw [this]; linarith
    calc (n : ℝ) * Real.log m * 2 ^ n < (c * n ^ 2 - 1) * 2 ^ n :=
          mul_lt_mul_of_pos_right hA hN
      _ ≤ _ := hB
  have hlt := ineq_nat m n hnm hm0 key
  have hf : f n ≤ m := Nat.sInf_le ⟨hnm, F3.exists_of m n hlt⟩
  have : (f n : ℝ) ≤ m := by exact_mod_cast hf
  linarith

end F4

theorem erdos_902.variants.erdos_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (Real.log 2 + ε) * n ^ 2 * 2 ^ n := by
  intro ε hε
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [F4.ev_ineq ε hε (Real.log (Real.log 2 + ε))] with n hn
  obtain ⟨hn1, hn5, hineq⟩ := hn
  exact F4.step n _ ε rfl hl2 hε hn1 hn5 hineq

end Erdos902

#print axioms Erdos902.erdos_902.variants.erdos_upper
