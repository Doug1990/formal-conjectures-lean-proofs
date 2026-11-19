import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Local copy of the definitions from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean (unchanged). -/

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α} [Fintype α] [DecidableEq α]

def IsDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

@[mk_iff]
structure IsNDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isDominating : G.IsDominating D
  card_eq : D.card = n

noncomputable def dominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsNDominatingSet n D}

omit [DecidableEq α] in
lemma exists_isNDominatingSet_dominationNumber
    (G : SimpleGraph α) :
    ∃ D : Finset α, G.IsNDominatingSet G.dominationNumber D := by
  have hne : {n | ∃ D : Finset α, G.IsNDominatingSet n D}.Nonempty :=
    ⟨_, Finset.univ, ⟨fun v => Or.inl (Finset.mem_univ v), rfl⟩⟩
  exact Nat.sInf_mem hne

omit [Fintype α] [DecidableEq α] in
lemma dominationNumber_le_of_isDominating
    (G : SimpleGraph α) (D : Finset α) (hD : G.IsDominating D) :
    G.dominationNumber ≤ D.card :=
  Nat.sInf_le ⟨D, hD, rfl⟩

end SimpleGraph

open SimpleGraph

namespace VizingConjecture

namespace CS

/-- Second coordinates of the part of `D` lying over the cell `f⁻¹(u)`. -/
def P {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → α) (D : Finset (α × β)) (u : α) : Finset β :=
  (D.filter (fun x : α × β => f x.1 = u)).image Prod.snd

lemma mem_P {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → α) (D : Finset (α × β))
    (x : α × β) (u : α) (hx : x ∈ D) (hu : f x.1 = u) : x.2 ∈ P f D u :=
  Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hx, hu⟩, rfl⟩

lemma card_P {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → α) (D : Finset (α × β))
    (u : α) : (P f D u).card ≤ (D.filter (fun x : α × β => f x.1 = u)).card :=
  Finset.card_image_le

/-- The cell `(u, h)` is vertically dominated. -/
def VD {α β : Type*} [DecidableEq α] [DecidableEq β] (H : SimpleGraph β) (f : α → α) (D : Finset (α × β)) (u : α) (h : β) :
    Prop :=
  h ∈ P f D u ∨ ∃ h' ∈ P f D u, H.Adj h h'

theorem key {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β) (U : Finset α) (hU : G.IsDominating U)
    (hmin : ∀ S : Finset α, G.IsDominating S → U.card ≤ S.card)
    (D : Finset (α × β)) (hD : (G □ H).IsDominating D) :
    U.card * H.dominationNumber ≤ 2 * D.card := by
  classical
  have hf : ∀ g, ∃ u ∈ U, g = u ∨ G.Adj g u := by
    intro g
    rcases hU g with h | ⟨w, hw, h⟩
    · exact ⟨g, h, Or.inl rfl⟩
    · exact ⟨w, hw, Or.inr h⟩
  choose f hfU hfg using hf
  -- claim 1: each cell row gives a dominating set of `H`
  have c1 : ∀ u, H.dominationNumber ≤ (D.filter (fun x => f x.1 = u)).card +
      (Finset.univ.filter (fun h => ¬ VD H f D u h)).card := by
    intro u
    refine le_trans (dominationNumber_le_of_isDominating H
      (P f D u ∪ Finset.univ.filter (fun h => ¬ VD H f D u h)) ?_) ?_
    · intro h
      by_cases hv : VD H f D u h
      · rcases hv with hv | ⟨h', hh', hadj⟩
        · exact Or.inl (Finset.mem_coe.2 (Finset.mem_union_left _ hv))
        · exact Or.inr ⟨h', Finset.mem_coe.2 (Finset.mem_union_left _ hh'), hadj⟩
      · exact Or.inl (Finset.mem_coe.2 (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩)))
    · exact le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (card_P f D u) _)
  -- claim 2: each `G`-fibre controls the non-vertically-dominated cells
  have c2 : ∀ h, (U.filter (fun u => ¬ VD H f D u h)).card ≤
      (D.filter (fun x => x.2 = h)).card := by
    intro h
    have hdom : G.IsDominating ↑((D.filter (fun x => x.2 = h)).image Prod.fst ∪
        U.filter (fun u => VD H f D u h)) := by
      intro g
      by_cases hv : VD H f D (f g) h
      · have hm : f g ∈ (D.filter (fun x => x.2 = h)).image Prod.fst ∪
            U.filter (fun u => VD H f D u h) :=
          Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hfU g, hv⟩)
        rcases hfg g with e | e
        · exact Or.inl (by rw [Finset.mem_coe, e]; exact hm)
        · exact Or.inr ⟨f g, Finset.mem_coe.2 hm, e⟩
      · rcases hD (g, h) with hin | ⟨⟨g', h'⟩, hin, hadj⟩
        · exact (hv (Or.inl (mem_P f D (g, h) (f g) (Finset.mem_coe.1 hin) rfl))).elim
        · simp only [boxProd_adj] at hadj
          rcases hadj with ⟨hg, hh⟩ | ⟨hh, hg⟩
          · exact Or.inr ⟨g', Finset.mem_coe.2 (Finset.mem_union_left _
              (Finset.mem_image.2 ⟨(g', h'),
                Finset.mem_filter.2 ⟨Finset.mem_coe.1 hin, hh.symm⟩, rfl⟩)), hg⟩
          · have hfx : f (g', h').1 = f g := by
              show f g' = f g
              rw [hg]
            exact (hv (Or.inr ⟨h', mem_P f D (g', h') (f g) (Finset.mem_coe.1 hin) hfx,
              hh⟩)).elim
    have h1 := hmin _ hdom
    have h2 := Finset.card_union_le ((D.filter (fun x => x.2 = h)).image Prod.fst)
      (U.filter (fun u => VD H f D u h))
    have h3 : ((D.filter (fun x => x.2 = h)).image Prod.fst).card ≤
        (D.filter (fun x => x.2 = h)).card := Finset.card_image_le
    have h4 := Finset.card_filter_add_card_filter_not (s := U) (fun u => VD H f D u h)
    omega
  have e1 : ∑ u ∈ U, (D.filter (fun x => f x.1 = u)).card = D.card :=
    (Finset.card_eq_sum_card_fiberwise (f := fun x : α × β => f x.1)
      (by intro x _; exact Finset.mem_coe.2 (hfU x.1))).symm
  have e2 : ∑ h : β, (D.filter (fun x => x.2 = h)).card = D.card :=
    (Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
      (by intro x _; exact Finset.mem_coe.2 (Finset.mem_univ _))).symm
  have b2 : ∑ h : β, (U.filter (fun u => ¬ VD H f D u h)).card ≤ D.card :=
    le_trans (Finset.sum_le_sum fun h _ => c2 h) e2.le
  have swap : ∑ u ∈ U, (Finset.univ.filter (fun h => ¬ VD H f D u h)).card =
      ∑ h : β, (U.filter (fun u => ¬ VD H f D u h)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  calc U.card * H.dominationNumber = ∑ _u ∈ U, H.dominationNumber := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ u ∈ U, ((D.filter (fun x => f x.1 = u)).card +
          (Finset.univ.filter (fun h => ¬ VD H f D u h)).card) :=
        Finset.sum_le_sum fun u _ => c1 u
    _ = D.card + ∑ h : β, (U.filter (fun u => ¬ VD H f D u h)).card := by
        rw [Finset.sum_add_distrib, e1, swap]
    _ ≤ 2 * D.card := by omega

end CS

theorem vizing_conjecture.variants.clark_suen
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber := by
  obtain ⟨U, hU, hUc⟩ := exists_isNDominatingSet_dominationNumber G
  obtain ⟨D, hD, hDc⟩ := exists_isNDominatingSet_dominationNumber (G □ H)
  rw [← hUc, ← hDc]
  exact CS.key G H U hU (fun S hS => hUc ▸ dominationNumber_le_of_isDominating G S hS) D hD

end VizingConjecture

#print axioms VizingConjecture.vizing_conjecture.variants.clark_suen
