import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FinCases

-- Hand-written copy of the verified file work/sidtree_a.lean (see sidorenko_tree.md).

set_option linter.unusedSectionVars false

open Finset SimpleGraph

namespace SidorenkoConjecture
namespace ST

/-- Concavity of log (weighted AM–GM). -/
lemma jensen {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 < w i → 0 < x i) (hS : 0 < ∑ i ∈ s, w i) :
    ∑ i ∈ s, w i * Real.log (x i) ≤
      (∑ i ∈ s, w i) * Real.log ((∑ i ∈ s, w i * x i) / ∑ i ∈ s, w i) := by
  have hterm : ∀ i ∈ s, 0 ≤ w i * x i := by
    intro i hi
    rcases (hw i hi).eq_or_lt with h | h
    · rw [← h, zero_mul]
    · exact (mul_pos h (hx i hi h)).le
  have hT : 0 < ∑ i ∈ s, w i * x i := by
    obtain ⟨i, hi, hwi⟩ : ∃ i ∈ s, 0 < w i := by
      by_contra h
      push Not at h
      have : ∑ i ∈ s, w i ≤ 0 := Finset.sum_nonpos h
      linarith
    calc 0 < w i * x i := mul_pos hwi (hx i hi hwi)
      _ ≤ ∑ i ∈ s, w i * x i := Finset.single_le_sum (f := fun i => w i * x i) hterm hi
  generalize hSdef : ∑ i ∈ s, w i = S at hS ⊢
  generalize hTdef : ∑ i ∈ s, w i * x i = T at hT ⊢
  have hA : 0 < T / S := div_pos hT hS
  have key : ∀ i ∈ s, w i * Real.log (x i) ≤
      w i * Real.log (T / S) + (w i * x i / (T / S) - w i) := by
    intro i hi
    rcases (hw i hi).eq_or_lt with h | h
    · rw [← h]; simp
    · have hxi := hx i hi h
      have h1 : Real.log (x i / (T / S)) ≤ x i / (T / S) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hxi hA)
      rw [Real.log_div hxi.ne' hA.ne'] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 h.le
      have e : w i * (x i / (T / S) - 1) = w i * x i / (T / S) - w i := by ring
      nlinarith [h2, e]
  calc ∑ i ∈ s, w i * Real.log (x i)
      ≤ ∑ i ∈ s, (w i * Real.log (T / S) + (w i * x i / (T / S) - w i)) :=
        Finset.sum_le_sum key
    _ = S * Real.log (T / S) + (T / (T / S) - S) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div,
          hSdef, hTdef]
    _ = S * Real.log (T / S) := by
        have : T / (T / S) = S := by field_simp
        rw [this]; ring

/-- Lower Jensen bound for `x log x`. -/
lemma jensen_low {ι : Type*} (s : Finset ι) (d : ι → ℝ) (hd : ∀ i ∈ s, 0 ≤ d i)
    (hD : 0 < ∑ i ∈ s, d i) :
    (∑ i ∈ s, d i) * Real.log ((∑ i ∈ s, d i) / s.card) ≤ ∑ i ∈ s, d i * Real.log (d i) := by
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hD
    exact lt_irrefl _ hD
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hne.card_pos
  generalize hDdef : ∑ i ∈ s, d i = D at hD ⊢
  have hc : 0 < D / s.card := div_pos hD hN
  have key : ∀ i ∈ s, d i * Real.log (D / s.card) + (d i - D / s.card) ≤
      d i * Real.log (d i) := by
    intro i hi
    rcases (hd i hi).eq_or_lt with h | h
    · rw [← h]; simp; exact hc.le
    · have h1 : 1 - (d i / (D / s.card))⁻¹ ≤ Real.log (d i / (D / s.card)) :=
        Real.one_sub_inv_le_log_of_pos (div_pos h hc)
      rw [Real.log_div h.ne' hc.ne', inv_div] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 h.le
      have e : d i * (1 - D / s.card / d i) = d i - D / s.card := by
        field_simp
      nlinarith [h2, e]
  calc D * Real.log (D / s.card)
      = ∑ i ∈ s, (d i * Real.log (D / s.card) + (d i - D / s.card)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hDdef,
          Finset.sum_const, nsmul_eq_mul]
        field_simp
        ring
    _ ≤ ∑ i ∈ s, d i * Real.log (d i) := Finset.sum_le_sum key

variable {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]

noncomputable def d (x : W) : ℝ := (G.degree x : ℝ)
noncomputable def a (x y : W) : ℝ := if G.Adj x y then 1 else 0
noncomputable def DD : ℝ := ∑ x, d G x

lemma row (x : W) : ∑ y, a G x y = d G x := by
  unfold a d
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter (G := G)]
  simp [Finset.sum_boole]

lemma a_nonneg (x y : W) : 0 ≤ a G x y := by unfold a; split_ifs <;> norm_num

lemma a_symm (x y : W) : a G x y = a G y x := by unfold a; simp [G.adj_comm]

lemma d_nonneg (x : W) : 0 ≤ d G x := Nat.cast_nonneg _

lemma col (y : W) : ∑ x, a G x y = d G y := by
  rw [← row G y]; exact Finset.sum_congr rfl fun x _ => a_symm G x y

lemma a_zero_of_d (x y : W) (h : d G x = 0) : a G x y = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => a_nonneg G x y)).1 ((row G x).trans h) y
    (mem_univ y)

lemma d_pos_of_a (x y : W) (h : a G x y ≠ 0) : 0 < d G y := by
  rw [← col G y]
  calc 0 < a G x y := lt_of_le_of_ne (a_nonneg G x y) (Ne.symm h)
    _ ≤ ∑ x', a G x' y := Finset.single_le_sum (f := fun x' => a G x' y)
        (fun x' _ => a_nonneg G x' y) (mem_univ x)

lemma sum_split {k : ℕ} (F : (Fin (k + 2) → W) → ℝ) :
    ∑ f, F f = ∑ g : Fin (k + 1) → W, ∑ y, F (Fin.snoc g y) := by
  rw [← (Fin.snocEquiv (fun _ => W)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- Markov-chain weight of a tuple: root distributed like `d / D`, each new vertex a
uniform neighbour of its parent. -/
noncomputable def P (G : SimpleGraph W) [DecidableRel G.Adj] (par : (k : ℕ) → Fin (k + 1)) :
    (k : ℕ) → (Fin (k + 1) → W) → ℝ
  | 0, f => d G (f 0) / DD G
  | k + 1, f => P G par k (Fin.init f) * a G (Fin.init f (par k)) (f (Fin.last (k + 1))) /
      d G (Fin.init f (par k))

noncomputable def Q (G : SimpleGraph W) [DecidableRel G.Adj] (par : (k : ℕ) → Fin (k + 1)) :
    (k : ℕ) → (Fin (k + 1) → W) → ℝ
  | 0, f => Real.log (DD G) - Real.log (d G (f 0))
  | k + 1, f => Q G par k (Fin.init f) + Real.log (d G (Fin.init f (par k)))

def Ok (G : SimpleGraph W) (par : (k : ℕ) → Fin (k + 1)) :
    (k : ℕ) → (Fin (k + 1) → W) → Prop
  | 0, _ => True
  | k + 1, f => Ok G par k (Fin.init f) ∧ G.Adj (Fin.init f (par k)) (f (Fin.last (k + 1)))

variable (par : (k : ℕ) → Fin (k + 1))

lemma P_zero (f : Fin 1 → W) : P G par 0 f = d G (f 0) / DD G := rfl

lemma P_succ (k : ℕ) (f : Fin (k + 2) → W) : P G par (k + 1) f =
    P G par k (Fin.init f) * a G (Fin.init f (par k)) (f (Fin.last (k + 1))) /
      d G (Fin.init f (par k)) := rfl

lemma Q_zero (f : Fin 1 → W) : Q G par 0 f = Real.log (DD G) - Real.log (d G (f 0)) := rfl

lemma Q_succ (k : ℕ) (f : Fin (k + 2) → W) : Q G par (k + 1) f =
    Q G par k (Fin.init f) + Real.log (d G (Fin.init f (par k))) := rfl

lemma P_nonneg (hD : 0 < DD G) : ∀ (k : ℕ) (f : Fin (k + 1) → W), 0 ≤ P G par k f
  | 0, f => by rw [P_zero]; exact div_nonneg (d_nonneg G _) hD.le
  | k + 1, f => by
    rw [P_succ]
    exact div_nonneg (mul_nonneg (P_nonneg hD k _) (a_nonneg G _ _)) (d_nonneg G _)

lemma P_pos_deg : ∀ (k : ℕ) (f : Fin (k + 1) → W), P G par k f ≠ 0 → ∀ i, 0 < d G (f i)
  | 0, f, h, i => by
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    subst hi
    have : d G (f 0) ≠ 0 := by
      intro h0; apply h; rw [P_zero, h0, zero_div]
    exact lt_of_le_of_ne (d_nonneg G _) (Ne.symm this)
  | k + 1, f, h, i => by
    rw [P_succ] at h
    have h1 : P G par k (Fin.init f) ≠ 0 := by
      intro h0; apply h; rw [h0, zero_mul, zero_div]
    have h2 : a G (Fin.init f (par k)) (f (Fin.last (k + 1))) ≠ 0 := by
      intro h0; apply h; rw [h0, mul_zero, zero_div]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact d_pos_of_a G _ _ h2
    · exact P_pos_deg k (Fin.init f) h1 j

lemma sum_init (k : ℕ) (F : (Fin (k + 1) → W) → ℝ) :
    ∑ f : Fin (k + 2) → W, P G par (k + 1) f * F (Fin.init f) = ∑ g, P G par k g * F g := by
  rw [sum_split]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [P_succ, Fin.init_snoc, Fin.snoc_last]
  by_cases hP : P G par k g = 0
  · simp [hP]
  · have hd := P_pos_deg G par k g hP (par k)
    rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum, row, mul_div_assoc,
      div_self hd.ne', mul_one]

lemma marg : ∀ (k : ℕ) (i : Fin (k + 1)) (g : W → ℝ),
    ∑ f, P G par k f * g (f i) = (∑ x, d G x * g x) / DD G
  | 0, i, g => by
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    subst hi
    rw [← (Equiv.funUnique (Fin 1) W).symm.sum_comp, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [P_zero, Equiv.funUnique_symm_apply]
    simp only [uniqueElim_const]
    ring
  | k + 1, i, g => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have e : ∀ h : Fin (k + 1) → W, ∑ y, P G par (k + 1) (Fin.snoc h y) *
            g ((Fin.snoc h y : Fin (k + 2) → W) (Fin.last (k + 1))) =
          P G par k h * ((∑ y, a G (h (par k)) y * g y) / d G (h (par k))) := by
        intro h
        simp only [P_succ, Fin.init_snoc, Fin.snoc_last]
        rw [Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      rw [sum_split]
      rw [Finset.sum_congr rfl fun h _ => e h]
      rw [marg k (par k) (fun x => (∑ y, a G x y * g y) / d G x)]
      congr 1
      have e2 : ∀ x, d G x * ((∑ y, a G x y * g y) / d G x) = ∑ y, a G x y * g y := by
        intro x
        by_cases hx : d G x = 0
        · rw [hx, zero_mul]; symm
          exact Finset.sum_eq_zero fun y _ => by rw [a_zero_of_d G x y hx, zero_mul]
        · field_simp
      simp only [e2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_mul, col]
    · exact (sum_init G par k (fun h => g (h j))).trans (marg k j g)

lemma mass (hD : 0 < DD G) (k : ℕ) : ∑ f, P G par k f = 1 := by
  have := marg G par k 0 (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  exact div_self hD.ne'

/-- Average of `log d` under the stationary distribution. -/
noncomputable def S : ℝ := (∑ x, d G x * Real.log (d G x)) / DD G

lemma ent (hD : 0 < DD G) : ∀ k : ℕ,
    ∑ f, P G par k f * Q G par k f = Real.log (DD G) + ((k : ℝ) - 1) * S G
  | 0 => by
    have := marg G par 0 0 (fun x => Real.log (DD G) - Real.log (d G x))
    simp only [Q_zero]
    rw [this]
    unfold S
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    have e : DD G * Real.log (DD G) / DD G = Real.log (DD G) := by
      field_simp
    rw [sub_div, show (∑ x, d G x) = DD G from rfl, e]
    push_cast
    ring
  | k + 1 => by
    simp only [Q_succ, mul_add, Finset.sum_add_distrib]
    rw [sum_init G par k (fun h => Q G par k h), ent hD k]
    have := marg G par (k + 1) (Fin.castSucc (par k)) (fun x => Real.log (d G x))
    rw [show (∑ f : Fin (k + 2) → W, P G par (k + 1) f * Real.log (d G (Fin.init f (par k)))) =
      ∑ f : Fin (k + 2) → W, P G par (k + 1) f * Real.log (d G (f (Fin.castSucc (par k)))) from rfl,
      this]
    unfold S
    push_cast
    ring

lemma Q_eq (hD : 0 < DD G) : ∀ (k : ℕ) (f : Fin (k + 1) → W), P G par k f ≠ 0 →
    -Real.log (P G par k f) = Q G par k f
  | 0, f, h => by
    have hd : d G (f 0) ≠ 0 := by
      intro h0; apply h; rw [P_zero, h0, zero_div]
    rw [P_zero, Q_zero, Real.log_div hd hD.ne']
    ring
  | k + 1, f, h => by
    rw [P_succ] at h ⊢
    have h1 : P G par k (Fin.init f) ≠ 0 := by
      intro h0; apply h; rw [h0, zero_mul, zero_div]
    have h2 : a G (Fin.init f (par k)) (f (Fin.last (k + 1))) ≠ 0 := by
      intro h0; apply h; rw [h0, mul_zero, zero_div]
    have ha : a G (Fin.init f (par k)) (f (Fin.last (k + 1))) = 1 := by
      unfold a at h2 ⊢
      split_ifs at h2 ⊢ with hh
      · rfl
      · exact absurd rfl h2
    have hd := P_pos_deg G par k (Fin.init f) h1 (par k)
    rw [ha, mul_one, Real.log_div h1 hd.ne', Q_succ, ← Q_eq hD k (Fin.init f) h1]
    ring

lemma gibbs (hD : 0 < DD G) (k : ℕ) :
    ∑ f, P G par k f * Q G par k f ≤ Real.log (#(univ.filter fun f => P G par k f ≠ 0)) := by
  set s := univ.filter fun f => P G par k f ≠ 0 with hs
  have h1 : ∑ f, P G par k f * Q G par k f =
      ∑ f ∈ s, P G par k f * Real.log ((P G par k f)⁻¹) := by
    rw [hs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with h
    · rw [Real.log_inv, Q_eq G par hD k f h]
    · push Not at h; rw [h, zero_mul]
  have hmass : ∑ f ∈ s, P G par k f = 1 := by
    rw [hs, Finset.sum_filter_ne_zero]; exact mass G par hD k
  have hj := jensen s (P G par k) (fun f => (P G par k f)⁻¹)
    (fun f _ => P_nonneg G par hD k f) (fun f _ hf => inv_pos.2 hf) (by rw [hmass]; exact one_pos)
  have hc : ∑ f ∈ s, P G par k f * (P G par k f)⁻¹ = (#s : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [mul_inv_cancel₀ (mem_filter.1 hf).2]
    simp
  rw [hmass, hc, div_one, one_mul] at hj
  rw [h1]
  exact hj

lemma card_pos (hD : 0 < DD G) (k : ℕ) : 0 < #(univ.filter fun f => P G par k f ≠ 0) := by
  rw [Finset.card_pos]
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have := mass G par hD k
  rw [← Finset.sum_filter_ne_zero, h, Finset.sum_empty] at this
  exact zero_ne_one this

lemma main_a [Nonempty W] (hD : 0 < DD G) (n : ℕ) :
    DD G * (DD G / Fintype.card W) ^ n ≤ #(univ.filter fun f => P G par (n + 1) f ≠ 0) := by
  have hN : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have he : ∑ f, P G par (n + 1) f * Q G par (n + 1) f = Real.log (DD G) + n * S G := by
    rw [ent G par hD (n + 1)]; push_cast; ring
  have hg := gibbs G par hD (n + 1)
  have hl := jensen_low univ (d G) (fun x _ => d_nonneg G x) hD
  rw [card_univ] at hl
  change DD G * Real.log (DD G / Fintype.card W) ≤ _ at hl
  have hS : Real.log (DD G / Fintype.card W) ≤ S G := by
    unfold S; rw [le_div_iff₀ hD]; linarith [hl]
  have hc : (0 : ℝ) < #(univ.filter fun f => P G par (n + 1) f ≠ 0) := by
    exact_mod_cast card_pos G par hD (n + 1)
  have hq : 0 < DD G / Fintype.card W := div_pos hD hN
  have hpos : 0 < DD G * (DD G / Fintype.card W) ^ n := mul_pos hD (pow_pos hq n)
  rw [← Real.log_le_log_iff hpos hc, Real.log_mul hD.ne' (pow_pos hq n).ne', Real.log_pow]
  have := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  linarith

lemma Ok_succ (k : ℕ) (f : Fin (k + 2) → W) : Ok G par (k + 1) f ↔
    (Ok G par k (Fin.init f) ∧ G.Adj (Fin.init f (par k)) (f (Fin.last (k + 1)))) := Iff.rfl

lemma Ok_of_P : ∀ (k : ℕ) (f : Fin (k + 1) → W), P G par k f ≠ 0 → Ok G par k f
  | 0, _, _ => trivial
  | k + 1, f, h => by
    rw [P_succ] at h
    have h1 : P G par k (Fin.init f) ≠ 0 := by
      intro h0; apply h; rw [h0, zero_mul, zero_div]
    have h2 : a G (Fin.init f (par k)) (f (Fin.last (k + 1))) ≠ 0 := by
      intro h0; apply h; rw [h0, mul_zero, zero_div]
    refine (Ok_succ G par k f).2 ⟨Ok_of_P k _ h1, ?_⟩
    unfold a at h2
    split_ifs at h2 with hh
    · exact hh
    · exact absurd rfl h2

lemma OkAll : ∀ (n : ℕ) (f : Fin (n + 1) → W), Ok G par n f → ∀ (j : ℕ) (hj : j < n),
    G.Adj (f ⟨(par j).val, by have := (par j).isLt; omega⟩) (f ⟨j + 1, by omega⟩)
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, f, h, j, hj => by
    rw [Ok_succ] at h
    by_cases hj' : j < n
    · exact OkAll n (Fin.init f) h.1 j hj'
    · have : j = n := by omega
      subst this
      exact h.2

end ST

namespace TR

variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (r : V)

lemma path_eq (hT : H.IsTree) {u v : V} (p q : H.Walk u v) (hp : p.IsPath) (hq : q.IsPath) :
    p = q :=
  congrArg Subtype.val ((hT.isAcyclic.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩)

lemma edge (hT : H.IsTree) {u v : V} (huv : H.Adj u v) :
    H.dist r v = H.dist r u + 1 ∨ H.dist r u = H.dist r v + 1 := by
  obtain ⟨p, hp, hpl⟩ := hT.connected.exists_path_of_dist r u
  have hd := huv.diff_dist_adj (u := r)
  by_cases hv : v ∈ p.support
  · have h1 := Walk.length_takeUntil_lt_length hv huv.ne.symm
    have h2 := H.dist_le (p.takeUntil v hv)
    omega
  · obtain ⟨q, hq, hql⟩ := hT.connected.exists_path_of_dist r v
    have := path_eq H hT q (p.concat huv) hq (hp.concat hv huv)
    rw [this, Walk.length_concat] at hql
    omega

lemma par_uniq (hT : H.IsTree) {w1 w2 v : V} (h1 : H.Adj w1 v) (h2 : H.Adj w2 v)
    (e1 : H.dist r w1 + 1 = H.dist r v) (e2 : H.dist r w2 + 1 = H.dist r v) : w1 = w2 := by
  have notin : ∀ (w : V) (p : H.Walk r w), p.length = H.dist r w → H.dist r w + 1 = H.dist r v →
      v ∉ p.support := by
    intro w p hl he hv
    have a1 := Walk.length_takeUntil_le_length p hv
    have a2 := H.dist_le (p.takeUntil v hv)
    omega
  obtain ⟨p1, hp1, hl1⟩ := hT.connected.exists_path_of_dist r w1
  obtain ⟨p2, hp2, hl2⟩ := hT.connected.exists_path_of_dist r w2
  have e := path_eq H hT (p1.concat h1) (p2.concat h2) (hp1.concat (notin w1 p1 hl1 e1) h1)
    (hp2.concat (notin w2 p2 hl2 e2) h2)
  have := congrArg (fun q => q.reverse.getVert 1) e
  simpa [Walk.reverse_concat] using this

open Classical in
noncomputable def pa (v : V) : V :=
  if h : ∃ u, H.Adj v u ∧ H.dist r u + 1 = H.dist r v then h.choose else v

lemma pa_eq (hT : H.IsTree) {u v : V} (huv : H.Adj u v) (he : H.dist r v = H.dist r u + 1) :
    pa H r v = u := by
  have h : ∃ u, H.Adj v u ∧ H.dist r u + 1 = H.dist r v := ⟨u, huv.symm, he.symm⟩
  unfold pa
  rw [dif_pos h]
  exact par_uniq H r hT h.choose_spec.1.symm huv h.choose_spec.2 he.symm

noncomputable def ord (f : V → ℕ) : Fin (Fintype.card V) ≃ V :=
  (Tuple.sort (fun i => f ((Fintype.equivFin V).symm i))).trans (Fintype.equivFin V).symm

lemma ord_mono (f : V → ℕ) : Monotone (fun i => f (ord f i)) := by
  intro a b h
  exact Tuple.monotone_sort (fun i => f ((Fintype.equivFin V).symm i)) h

variable {n : ℕ} (E : Fin (n + 2) ≃ V)

noncomputable def par (j : ℕ) : Fin (j + 1) :=
  if h : j + 1 < n + 2 then
    (if h2 : (E.symm (pa H r (E ⟨j + 1, h⟩))).val < j + 1 then ⟨_, h2⟩ else 0)
  else 0

lemma par_val (j : ℕ) (h : j + 1 < n + 2) (h2 : (E.symm (pa H r (E ⟨j + 1, h⟩))).val < j + 1) :
    (par H r E j).val = (E.symm (pa H r (E ⟨j + 1, h⟩))).val := by
  unfold par
  rw [dif_pos h, dif_pos h2]

variable {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]

lemma key (hT : H.IsTree) (hmono : ∀ i j : Fin (n + 2), i ≤ j → H.dist r (E i) ≤ H.dist r (E j))
    (f : Fin (n + 2) → W) (hOk : ST.Ok G (par H r E) (n + 1) f) {u v : V} (huv : H.Adj u v)
    (he : H.dist r v = H.dist r u + 1) : G.Adj (f (E.symm u)) (f (E.symm v)) := by
  have hab : (E.symm u).val < (E.symm v).val := by
    by_contra hc
    push Not at hc
    have := hmono (E.symm v) (E.symm u) hc
    rw [E.apply_symm_apply, E.apply_symm_apply] at this
    omega
  set j := (E.symm v).val - 1 with hj
  have h1 : j + 1 < n + 2 := by have := (E.symm v).isLt; omega
  have hb : (⟨j + 1, h1⟩ : Fin (n + 2)) = E.symm v := Fin.ext (by simp only; omega)
  have hpa : E.symm (pa H r (E ⟨j + 1, h1⟩)) = E.symm u := by
    rw [hb, E.apply_symm_apply, pa_eq H r hT huv he]
  have h2 : (E.symm (pa H r (E ⟨j + 1, h1⟩))).val < j + 1 := by rw [hpa]; omega
  have hpar := par_val H r E j h1 h2
  rw [hpa] at hpar
  have k := ST.OkAll G (par H r E) (n + 1) f hOk j (by omega)
  convert k using 2
  · exact Fin.ext (by simp only; omega)
  · exact Fin.ext (by simp only; omega)

lemma key2 (hT : H.IsTree) (hmono : ∀ i j : Fin (n + 2), i ≤ j → H.dist r (E i) ≤ H.dist r (E j))
    (f : Fin (n + 2) → W) (hOk : ST.Ok G (par H r E) (n + 1) f) {u v : V} (huv : H.Adj u v) :
    G.Adj (f (E.symm u)) (f (E.symm v)) := by
  rcases edge H r hT huv with he | he
  · exact key H r E G hT hmono f hOk huv he
  · exact (key H r E G hT hmono f hOk huv.symm he).symm

def toHom (hT : H.IsTree) (hmono : ∀ i j : Fin (n + 2), i ≤ j → H.dist r (E i) ≤ H.dist r (E j))
    (f : Fin (n + 2) → W) (hOk : ST.Ok G (par H r E) (n + 1) f) : H →g G where
  toFun v := f (E.symm v)
  map_rel' huv := key2 H r E G hT hmono f hOk huv

lemma count (hT : H.IsTree) (hmono : ∀ i j : Fin (n + 2), i ≤ j → H.dist r (E i) ≤ H.dist r (E j))
    [DecidableRel H.Adj] :
    #(univ.filter fun f => ST.P G (par H r E) (n + 1) f ≠ 0) ≤ Fintype.card (H →g G) := by
  have := Fintype.card_le_of_injective
    (fun x : {x // x ∈ univ.filter fun f => ST.P G (par H r E) (n + 1) f ≠ 0} =>
      toHom H r E G hT hmono x.1 (ST.Ok_of_P G _ (n + 1) x.1 (mem_filter.1 x.2).2)) ?_
  · rwa [Fintype.card_coe] at this
  · intro x y hxy
    apply Subtype.ext
    funext i
    have := DFunLike.congr_fun hxy (E i)
    simpa [toHom] using this

end TR

end SidorenkoConjecture

namespace SimpleGraph

variable {V W : Type*}

noncomputable def homCount [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] : ℕ :=
  Fintype.card (H →g G)

noncomputable def homDensity [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] : ℝ :=
  (homCount H G : ℝ) / (Fintype.card W : ℝ) ^ (Fintype.card V)

end SimpleGraph

namespace SidorenkoConjecture

lemma edgeCount_eq_zero_of_subsingleton {V : Type*} [Fintype V] [Subsingleton V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : H.edgeFinset.card = 0 := by
  rw [Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_edgeFinset] at he
  induction e with
  | h u v =>
    rw [mem_edgeSet] at he
    exact H.ne_of_adj he (Subsingleton.elim u v)

lemma homCount_eq_of_subsingleton {V W : Type*} [Fintype V] [Fintype W]
    [Subsingleton V] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel G.Adj] :
    homCount H G = (Fintype.card W) ^ (Fintype.card V) := by
  unfold homCount
  rw [← Fintype.card_fun]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun f => (f : V → W)
      invFun := fun f =>
        { toFun := f
          map_rel' := fun {u v} huv => (H.ne_of_adj huv (Subsingleton.elim u v)).elim }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem sidorenko_tree_subsingleton {V W : Type} [Fintype V] [Fintype W]
    [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W]
    (H : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G := by
  rw [edgeCount_eq_zero_of_subsingleton H, pow_zero]
  have hWpos : 0 < Fintype.card W := Fintype.card_pos
  have hWpow : (0 : ℝ) < (Fintype.card W : ℝ) ^ Fintype.card V :=
    pow_pos (by exact_mod_cast hWpos) _
  rw [homDensity, homCount_eq_of_subsingleton H G]
  push_cast
  rw [div_self (ne_of_gt hWpow)]

lemma homCount_K2 {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] : homCount (completeGraph (Fin 2)) G = 2 * #G.edgeFinset := by
  unfold homCount
  rw [← G.dart_card_eq_twice_card_edges]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun f =>
        ⟨(f 0, f 1), f.map_adj (by decide : (completeGraph (Fin 2)).Adj 0 1)⟩
      invFun := fun d =>
        { toFun := fun i => if i = 0 then d.fst else d.snd
          map_rel' := fun {a b} hab => by
            simp only [completeGraph, top_adj] at hab
            fin_cases a <;> fin_cases b
            · simp at hab
            · exact d.adj
            · exact d.adj.symm
            · simp at hab }
      left_inv := fun f => by
        ext i
        fin_cases i <;> simp
      right_inv := fun d => by
        cases d
        rfl }

theorem sidorenko_tree {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] [Nonempty W]
    (H : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hTree : H.IsTree) :
    homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G := by
  have hne : Nonempty V := hTree.connected.nonempty
  by_cases hSub : Subsingleton V
  · exact sidorenko_tree_subsingleton H G
  rw [not_subsingleton_iff_nontrivial] at hSub
  have hV2 : 2 ≤ Fintype.card V := Fintype.one_lt_card
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n + 2 := ⟨Fintype.card V - 2, by omega⟩
  have hE : H.edgeFinset.card = n + 1 := by
    have := hTree.card_edgeFinset
    omega
  have hN : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hL : homDensity (completeGraph (Fin 2)) G = ST.DD G / (Fintype.card W : ℝ) ^ 2 := by
    unfold homDensity
    rw [homCount_K2, ← G.sum_degrees_eq_twice_card_edges, Fintype.card_fin]
    push_cast
    rfl
  have hR0 : 0 ≤ homDensity H G := by unfold homDensity; positivity
  rw [hL, hE]
  have hD0 : 0 ≤ ST.DD G := Finset.sum_nonneg fun x _ => ST.d_nonneg G x
  rcases hD0.eq_or_lt with hD | hD
  · rw [← hD, zero_div, zero_pow (Nat.succ_ne_zero n)]
    exact hR0
  -- the ordering
  obtain ⟨r⟩ := hne
  have hN' : (Fintype.card W : ℝ) ≠ 0 := hN.ne'
  let E : Fin (n + 2) ≃ V := (finCongr hn.symm).trans (TR.ord (fun v => H.dist r v))
  have hmono : ∀ i j : Fin (n + 2), i ≤ j → H.dist r (E i) ≤ H.dist r (E j) := by
    intro i j hij
    have h' : finCongr hn.symm i ≤ finCongr hn.symm j := by
      rw [Fin.le_iff_val_le_val] at hij ⊢
      simpa using hij
    exact TR.ord_mono (fun v => H.dist r v) h'
  have hA := ST.main_a G (TR.par H r E) hD n
  have hC := TR.count H r E G hTree hmono
  have hC' : (#(univ.filter fun f => ST.P G (TR.par H r E) (n + 1) f ≠ 0) : ℝ) ≤
      (homCount H G : ℝ) := by
    unfold homCount; exact_mod_cast hC
  unfold homDensity
  rw [hn]
  rw [le_div_iff₀ (by positivity)]
  calc (ST.DD G / (Fintype.card W : ℝ) ^ 2) ^ (n + 1) * (Fintype.card W : ℝ) ^ (n + 2)
      = ((ST.DD G / (Fintype.card W : ℝ) ^ 2) * Fintype.card W) ^ (n + 1) *
          Fintype.card W := by ring
    _ = (ST.DD G / Fintype.card W) ^ (n + 1) * Fintype.card W := by
        rw [sq, ← div_div, div_mul_cancel₀ _ hN']
    _ = ST.DD G * (ST.DD G / Fintype.card W) ^ n := by
        rw [pow_succ, mul_assoc, div_mul_cancel₀ _ hN']
        ring
    _ ≤ _ := hA.trans hC'

end SidorenkoConjecture

#print axioms SidorenkoConjecture.sidorenko_tree
