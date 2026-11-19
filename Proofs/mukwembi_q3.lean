import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Definitions restated from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean -/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

def IsDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

def IsConnectedDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  G.IsDominating D ∧ (G.induce D).Connected

noncomputable def connectedDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsConnectedDominating (D : Set α) ∧ D.card = n}

end SimpleGraph

namespace SizeOrderConnectedDomination

open SimpleGraph

/-- adjacency of the 3-cube on `Fin 8`: indices differ in exactly one bit -/
def qa (i j : Fin 8) : Bool :=
  (i.val ^^^ j.val == 1) || (i.val ^^^ j.val == 2) || (i.val ^^^ j.val == 4)

lemma qa_symm : ∀ i j : Fin 8, qa i j = true → qa j i = true := by decide

lemma qa_irrefl : ∀ i : Fin 8, ¬ qa i i = true := by decide

def Q3 : SimpleGraph (Fin 8) where
  Adj i j := qa i j = true
  symm := ⟨qa_symm⟩
  loopless := ⟨qa_irrefl⟩

instance : DecidableRel Q3.Adj := fun i j => inferInstanceAs (Decidable (qa i j = true))

lemma step : ∀ v : Fin 8, v ≠ 0 → ∃ w : Fin 8, w < v ∧ Q3.Adj v w := by decide

lemma reach0 (n : ℕ) : ∀ v : Fin 8, v.val = n → Q3.Reachable 0 v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    by_cases h0 : v = 0
    · subst h0; exact Reachable.refl _
    · obtain ⟨w, hw, hadj⟩ := step v h0
      have hwn : w.val < n := by rw [← hv]; exact hw
      exact (ih w.val hwn w rfl).trans hadj.symm.reachable

lemma conn : Q3.Connected :=
  (connected_iff _).2 ⟨fun u v => (reach0 _ u rfl).symm.trans (reach0 _ v rfl), ⟨0⟩⟩

def par (i : Fin 8) : Bool :=
  (i.val == 1) || (i.val == 2) || (i.val == 4) || (i.val == 7)

lemma par_ne : ∀ i j : Fin 8, Q3.Adj i j → par i ≠ par j := by decide

lemma cf : Q3.CliqueFree 3 := by
  intro t ht
  rw [is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
  have h1 := par_ne _ _ hab
  have h2 := par_ne _ _ hac
  have h3 := par_ne _ _ hbc
  revert h1 h2 h3
  cases par a <;> cases par b <;> cases par c <;> decide

lemma deg3 : ∀ v : Fin 8, Q3.degree v = 3 := by
  intro v
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  revert v
  decide

lemma edges : Q3.edgeFinset.card = 12 := by
  have := Q3.sum_degrees_eq_twice_card_edges
  simp only [deg3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

lemma single : ∀ d : Fin 8, ∃ v : Fin 8, v ≠ d ∧ ¬ Q3.Adj v d := by decide

def Far (d e f v : Fin 8) : Prop :=
  v ≠ d ∧ v ≠ e ∧ v ≠ f ∧ ¬ Q3.Adj v d ∧ ¬ Q3.Adj v e ∧ ¬ Q3.Adj v f

instance (d e f v : Fin 8) : Decidable (Far d e f v) := by unfold Far; infer_instance

def Cond (d e f : Fin 8) : Prop := f = d ∨ Q3.Adj f d ∨ Q3.Adj f e

instance (d e f : Fin 8) : Decidable (Cond d e f) := by unfold Cond; infer_instance

lemma triple : ∀ d e f : Fin 8, Q3.Adj d e → Cond d e f → ∃ v : Fin 8, Far d e f v := by
  decide

lemma walk_nbr (D : Finset (Fin 8)) :
    ∀ (u v : ↥(D : Set (Fin 8))) (_ : (Q3.induce (D : Set (Fin 8))).Walk u v), u ≠ v →
      ∃ z ∈ D, Q3.Adj u.1 z := by
  intro u v p huv
  cases p with
  | nil => exact absurd rfl huv
  | cons h q =>
    rename_i w
    exact ⟨w.1, w.2, h⟩

lemma nbr_in (D : Finset (Fin 8)) (hc : (Q3.induce (D : Set (Fin 8))).Connected)
    (x y : Fin 8) (hx : x ∈ D) (hy : y ∈ D) (hxy : x ≠ y) : ∃ z ∈ D, Q3.Adj x z := by
  obtain ⟨p⟩ := hc.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  exact walk_nbr D ⟨x, hx⟩ ⟨y, hy⟩ p (fun h => hxy (congrArg Subtype.val h))

lemma no_small (D : Finset (Fin 8)) (hD : Q3.IsConnectedDominating (D : Set (Fin 8))) :
    4 ≤ D.card := by
  by_contra hlt
  have hlt : D.card < 4 := by omega
  obtain ⟨hdom, hcon⟩ := hD
  obtain ⟨⟨d, hd⟩⟩ := hcon.nonempty
  have hd : d ∈ D := hd
  by_cases hy : ∃ y ∈ D, y ≠ d
  · obtain ⟨y, hyD, hyd⟩ := hy
    obtain ⟨e, he, hde⟩ := nbr_in D hcon d y hd hyD (Ne.symm hyd)
    have hed : e ≠ d := fun h => Q3.loopless.irrefl d (h ▸ hde)
    -- find the third point
    obtain ⟨f, hf, hfadj, hmem⟩ : ∃ f ∈ D, (f = d ∨ Q3.Adj f d ∨ Q3.Adj f e) ∧
        ∀ x ∈ D, x = d ∨ x = e ∨ x = f := by
      by_cases hz : ∃ f ∈ D, f ≠ d ∧ f ≠ e
      · obtain ⟨f, hf, hfd, hfe⟩ := hz
        have hmem : ∀ x ∈ D, x = d ∨ x = e ∨ x = f := by
          intro x hx
          by_contra hne
          push Not at hne
          obtain ⟨hxd, hxe, hxf⟩ := hne
          have hsub : ({x, d, e, f} : Finset (Fin 8)) ⊆ D := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl | rfl <;> assumption
          have hc4 : ({x, d, e, f} : Finset (Fin 8)).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [hxd, hxe, hxf]),
              Finset.card_insert_of_notMem (by simp [Ne.symm hed, Ne.symm hfd]),
              Finset.card_pair (Ne.symm hfe)]
          have := Finset.card_le_card hsub
          omega
        obtain ⟨z, hz, hfz⟩ := nbr_in D hcon f d hf hd hfd
        refine ⟨f, hf, ?_, hmem⟩
        rcases hmem z hz with rfl | rfl | rfl
        · exact Or.inr (Or.inl hfz)
        · exact Or.inr (Or.inr hfz)
        · exact absurd hfz (Q3.loopless.irrefl _)
      · refine ⟨d, hd, Or.inl rfl, ?_⟩
        intro x hx
        by_contra hne
        push Not at hne
        exact hz ⟨x, hx, hne.1, hne.2.1⟩
    obtain ⟨v, hv⟩ := triple d e f hde hfadj
    unfold Far at hv
    obtain ⟨hvd, hve, hvf, hnd, hne, hnf⟩ := hv
    rcases hdom v with hv | ⟨w, hw, hvw⟩
    · rcases hmem v hv with h | h | h
      · exact hvd h
      · exact hve h
      · exact hvf h
    · rcases hmem w hw with rfl | rfl | rfl
      · exact hnd hvw
      · exact hne hvw
      · exact hnf hvw
  · push Not at hy
    obtain ⟨v, hvd, hnd⟩ := single d
    rcases hdom v with hv | ⟨w, hw, hvw⟩
    · exact hvd (hy v hv)
    · rw [hy w hw] at hvw
      exact hnd hvw

lemma univ_conn : (Q3.induce ((Finset.univ : Finset (Fin 8)) : Set (Fin 8))).Connected := by
  rw [Finset.coe_univ]
  exact (induceUnivIso Q3).connected_iff.2 conn

theorem mukwembi_theorem_2_1 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj],
      G.Connected → G.CliqueFree 3 →
      (G.edgeFinset.card : ℝ) ≤
        ((Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ)) ^ 2 / 4
          + (Fintype.card α : ℝ) - 1 := by
  intro h
  have hγ := h (Fin 8) Q3 conn cf
  have hne : {n | ∃ D : Finset (Fin 8), Q3.IsConnectedDominating (D : Set (Fin 8)) ∧
      D.card = n}.Nonempty :=
    ⟨8, Finset.univ, ⟨fun v => Or.inl (by simp), univ_conn⟩, by simp⟩
  obtain ⟨D, hD, hcard⟩ := Nat.sInf_mem hne
  have h4 := no_small D hD
  have h8 : D.card ≤ 8 := by simpa using Finset.card_le_univ D
  have hcd : Q3.connectedDominationNumber = D.card := hcard.symm
  rw [edges, hcd, Fintype.card_fin] at hγ
  have hx4 : (4 : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast h4
  have hx8 : (D.card : ℝ) ≤ 8 := by exact_mod_cast h8
  push_cast at hγ
  nlinarith [mul_nonneg (sub_nonneg.2 hx4) (sub_nonneg.2 hx8)]

end SizeOrderConnectedDomination

#print axioms SizeOrderConnectedDomination.mukwembi_theorem_2_1
