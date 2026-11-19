import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Fin.Basic

/-! Definitions restated from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Petersen.lean -/

namespace SimpleGraph

abbrev PetersenVertex : Type := {s : Finset (Fin 5) // s.card = 2}

def petersenGraph : SimpleGraph PetersenVertex where
  Adj s t := Disjoint s.1 t.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun s h => by
    have hc := s.2
    rw [disjoint_self.mp h] at hc
    simp at hc⟩

instance : DecidableRel petersenGraph.Adj := fun s t =>
  inferInstanceAs (Decidable (Disjoint s.1 t.1))

def petersenVertex01 : PetersenVertex := ⟨{0, 1}, by decide⟩

theorem petersenGraph_degree (v : PetersenVertex) : petersenGraph.degree v = 3 := by
  revert v; decide

end SimpleGraph

open SimpleGraph Finset

namespace PetersenColoringConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsPetersenColoring (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : Sym2 V → Sym2 PetersenVertex) : Prop :=
  ∀ v : V, ∃ w : PetersenVertex,
    (G.incidenceFinset v).image φ = petersenGraph.incidenceFinset w ∧
      Set.InjOn φ (G.incidenceFinset v : Set (Sym2 V))

namespace PC

abbrev PV := PetersenVertex

def mk2 (s : Finset (Fin 5)) : PV := if h : s.card = 2 then ⟨s, h⟩ else petersenVertex01

lemma mk2_val (s : Finset (Fin 5)) (h : s.card = 2) : (mk2 s).1 = s := by
  simp [mk2, h]

def nb (w : PV) (i : Fin 5) : PV := mk2 (univ \ insert i w.1)

def colP : Sym2 PV → Fin 5 :=
  Sym2.lift ⟨fun a b => ∑ i ∈ univ \ (a.1 ∪ b.1), i, fun a b => by
    show (∑ i ∈ univ \ (a.1 ∪ b.1), i) = ∑ i ∈ univ \ (b.1 ∪ a.1), i
    rw [Finset.union_comm]⟩

lemma F3 : ∀ w : PV, ∀ i : Fin 5, i ∉ w.1 → Disjoint w.1 (nb w i).1 ∧ colP s(w, nb w i) = i := by
  decide +kernel

lemma F5 : ∀ w w' : PV, (w = w' ∨ Disjoint w.1 w'.1) →
    ((univ \ w.1) ∪ (univ \ w'.1)).card = 3 ∨ ((univ \ w.1) ∪ (univ \ w'.1)).card = 5 := by
  decide +kernel

lemma mem_inc {α : Type*} [DecidableEq α] {H : SimpleGraph α} {v : α} [Fintype (H.neighborSet v)]
    {e : Sym2 α} : e ∈ H.incidenceFinset v ↔ e ∈ H.edgeSet ∧ v ∈ e := by
  rw [mem_incidenceFinset]; exact Iff.rfl

lemma inc_card (w : PV) : (petersenGraph.incidenceFinset w).card = 3 := by
  rw [card_incidenceFinset_eq_degree]; exact petersenGraph_degree w

lemma mem_incP (w : PV) (i : Fin 5) (hi : i ∉ w.1) :
    s(w, nb w i) ∈ petersenGraph.incidenceFinset w := by
  rw [mem_incidenceFinset, mem_incidenceSet]; exact (F3 w i hi).1

lemma card_compl2 (w : PV) : (univ \ w.1).card = 3 := by
  rw [card_univ_sdiff, Fintype.card_fin, w.2]

lemma F1 (w : PV) : (petersenGraph.incidenceFinset w).image colP = univ \ w.1 := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    have hi' : i ∉ w.1 := (mem_sdiff.1 hi).2
    exact mem_image.2 ⟨_, mem_incP w i hi', (F3 w i hi').2⟩
  · have h1 := card_image_le (s := petersenGraph.incidenceFinset w) (f := colP)
    rw [inc_card] at h1
    rw [card_compl2]; exact h1

lemma F2 (w : PV) : Set.InjOn colP (petersenGraph.incidenceFinset w : Set _) := by
  rw [← Finset.card_image_iff, F1, inc_card, card_compl2]

lemma F4 {w w' : PV} {g : Sym2 PV} (h1 : g ∈ petersenGraph.incidenceFinset w)
    (h2 : g ∈ petersenGraph.incidenceFinset w') : w = w' ∨ petersenGraph.Adj w w' := by
  by_cases h : w = w'
  · exact Or.inl h
  right
  obtain ⟨h1e, h1w⟩ := mem_inc.1 h1
  obtain ⟨_, h2w⟩ := mem_inc.1 h2
  have : g = s(w, w') := (Sym2.mem_and_mem_iff h).1 ⟨h1w, h2w⟩
  rw [this] at h1e
  exact h1e

lemma L4 (A B : Finset (Fin 5)) (i : Fin 5) (hA : A.card = 3) (hB : B.card = 3)
    (hAB : A ∩ B = {i}) : univ \ insert i (univ \ A) = univ \ B := by
  have hu : A ∪ B = univ := by
    apply eq_univ_of_card
    have := card_union_add_card_inter A B
    rw [hAB, card_singleton, hA, hB] at this
    rw [Fintype.card_fin]; omega
  have hi : i ∈ A ∩ B := by rw [hAB]; exact mem_singleton_self i
  ext x
  simp only [mem_sdiff, mem_univ, mem_insert, true_and, not_or, not_not]
  constructor
  · rintro ⟨hxi, hxA⟩ hxB
    have : x ∈ A ∩ B := mem_inter.2 ⟨hxA, hxB⟩
    rw [hAB, mem_singleton] at this; exact hxi this
  · intro hxB
    refine ⟨fun h => by subst h; exact hxB (mem_inter.1 hi).2, ?_⟩
    have : x ∈ A ∪ B := hu ▸ mem_univ x
    rcases mem_union.1 this with h | h
    · exact h
    · exact absurd h hxB

variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma filt_eq {u v : V} :
    G.edgeFinset.filter (fun f => ∃ x, x ∈ s(u, v) ∧ x ∈ f) =
      G.incidenceFinset u ∪ G.incidenceFinset v := by
  ext f
  rw [mem_filter, mem_union, mem_inc, mem_inc, mem_edgeFinset]
  constructor
  · rintro ⟨hf, x, hx, hxf⟩
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact Or.inl ⟨hf, hxf⟩
    · exact Or.inr ⟨hf, hxf⟩
  · rintro (⟨hf, hu⟩ | ⟨hf, hv⟩)
    · exact ⟨hf, u, Sym2.mem_mk_left u v, hu⟩
    · exact ⟨hf, v, Sym2.mem_mk_right u v, hv⟩

def Proper (c : Sym2 V → Fin 5) : Prop :=
  ∀ e ∈ G.edgeFinset, ∀ f ∈ G.edgeFinset, e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → c e ≠ c f

def Normal (c : Sym2 V → Fin 5) : Prop :=
  ∀ e ∈ G.edgeFinset,
    ((G.edgeFinset.filter fun f => ∃ v, v ∈ e ∧ v ∈ f).image c).card = 3 ∨
    ((G.edgeFinset.filter fun f => ∃ v, v ∈ e ∧ v ∈ f).image c).card = 5

def S (c : Sym2 V → Fin 5) (v : V) : Finset (Fin 5) := (G.incidenceFinset v).image c

def W (c : Sym2 V → Fin 5) (v : V) : PV := mk2 (univ \ S G c v)

open Classical in
noncomputable def Φ (c : Sym2 V → Fin 5) (e : Sym2 V) : Sym2 PV :=
  if h : ∃ x, x ∈ e then s(W G c h.choose, nb (W G c h.choose) (c e))
  else s(petersenVertex01, petersenVertex01)

variable {G} {c : Sym2 V → Fin 5}

lemma L1 (hp : Proper G c) (v : V) : Set.InjOn c (G.incidenceFinset v : Set (Sym2 V)) := by
  intro e he f hf hef
  have he' := mem_inc.1 (Finset.mem_coe.1 he)
  have hf' := mem_inc.1 (Finset.mem_coe.1 hf)
  by_contra hne
  exact hp e (mem_edgeFinset.2 he'.1) f (mem_edgeFinset.2 hf'.1) hne ⟨v, he'.2, hf'.2⟩ hef

lemma L2 (hp : Proper G c) (hcubic : ∀ v, G.degree v = 3) (v : V) : (S G c v).card = 3 := by
  unfold S
  rw [card_image_of_injOn (L1 hp v), card_incidenceFinset_eq_degree, hcubic]

lemma W_val (hp : Proper G c) (hcubic : ∀ v, G.degree v = 3) (v : V) :
    (W G c v).1 = univ \ S G c v :=
  mk2_val _ (by rw [card_univ_sdiff, Fintype.card_fin, L2 hp hcubic])

lemma notin_W (hp : Proper G c) (hcubic : ∀ v, G.degree v = 3) {v : V} {e : Sym2 V}
    (he : e ∈ G.incidenceFinset v) : c e ∉ (W G c v).1 := by
  rw [W_val hp hcubic]
  intro h
  exact (mem_sdiff.1 h).2 (mem_image_of_mem c he)

lemma dichot (hp : Proper G c) (hn : Normal G c) (hcubic : ∀ v, G.degree v = 3) {u v : V}
    (h : G.Adj u v) : S G c u = S G c v ∨ S G c u ∩ S G c v = {c s(u, v)} := by
  have he : s(u, v) ∈ G.edgeFinset := mem_edgeFinset.2 h
  have h3 := hn _ he
  rw [filt_eq G, image_union] at h3
  change (S G c u ∪ S G c v).card = 3 ∨ (S G c u ∪ S G c v).card = 5 at h3
  have hiu : c s(u, v) ∈ S G c u := mem_image_of_mem c (mem_inc.2 ⟨h, Sym2.mem_mk_left u v⟩)
  have hiv : c s(u, v) ∈ S G c v := mem_image_of_mem c (mem_inc.2 ⟨h, Sym2.mem_mk_right u v⟩)
  have hsum := card_union_add_card_inter (S G c u) (S G c v)
  have hu3 := L2 hp hcubic u
  have hv3 := L2 hp hcubic v
  rcases h3 with h3 | h3
  · left
    have hi : S G c u ∩ S G c v = S G c u :=
      eq_of_subset_of_card_le inter_subset_left (by omega)
    have hi2 : S G c u ∩ S G c v = S G c v :=
      eq_of_subset_of_card_le inter_subset_right (by omega)
    rw [← hi, hi2]
  · right
    obtain ⟨a, ha⟩ := card_eq_one.1 (by omega : (S G c u ∩ S G c v).card = 1)
    have : c s(u, v) ∈ S G c u ∩ S G c v := mem_inter.2 ⟨hiu, hiv⟩
    rw [ha, mem_singleton] at this
    rw [ha, this]

lemma sym (hp : Proper G c) (hn : Normal G c) (hcubic : ∀ v, G.degree v = 3) {u v : V}
    (h : G.Adj u v) :
    s(W G c u, nb (W G c u) (c s(u, v))) = s(W G c v, nb (W G c v) (c s(u, v))) := by
  rcases dichot hp hn hcubic h with heq | hint
  · have : W G c u = W G c v := by unfold W; rw [heq]
    rw [this]
  · have h1 : nb (W G c u) (c s(u, v)) = W G c v := by
      unfold nb; rw [W_val hp hcubic]
      show mk2 _ = mk2 _
      congr 1
      exact L4 _ _ _ (L2 hp hcubic u) (L2 hp hcubic v) hint
    have h2 : nb (W G c v) (c s(u, v)) = W G c u := by
      unfold nb; rw [W_val hp hcubic]
      show mk2 _ = mk2 _
      congr 1
      rw [inter_comm] at hint
      exact L4 _ _ _ (L2 hp hcubic v) (L2 hp hcubic u) hint
    rw [h1, h2, Sym2.eq_swap]

lemma Φ_eq (hp : Proper G c) (hn : Normal G c) (hcubic : ∀ v, G.degree v = 3) (e : Sym2 V)
    (he : e ∈ G.edgeSet) (x : V) (hx : x ∈ e) :
    Φ G c e = s(W G c x, nb (W G c x) (c e)) := by
  obtain ⟨x', rfl⟩ := Sym2.mem_iff_exists.1 hx
  have hadj : G.Adj x x' := he
  have hex : ∃ y, y ∈ s(x, x') := ⟨x, hx⟩
  unfold Φ
  rw [dif_pos hex]
  have hy : hex.choose ∈ s(x, x') := hex.choose_spec
  generalize hex.choose = y at hy ⊢
  rcases Sym2.mem_iff.1 hy with rfl | rfl
  · rfl
  · exact (sym hp hn hcubic hadj).symm

lemma bwd (hp : Proper G c) (hn : Normal G c) (hcubic : ∀ v, G.degree v = 3) :
    IsPetersenColoring G (Φ G c) := by
  intro v
  have hinj : Set.InjOn (Φ G c) (G.incidenceFinset v : Set (Sym2 V)) := by
    intro e he f hf hef
    have he0 := Finset.mem_coe.1 he
    have hf0 := Finset.mem_coe.1 hf
    have he' := mem_inc.1 he0
    have hf' := mem_inc.1 hf0
    rw [Φ_eq hp hn hcubic e he'.1 v he'.2, Φ_eq hp hn hcubic f hf'.1 v hf'.2] at hef
    have := congrArg colP hef
    rw [(F3 _ _ (notin_W hp hcubic he0)).2, (F3 _ _ (notin_W hp hcubic hf0)).2] at this
    exact L1 hp v he hf this
  refine ⟨W G c v, ?_, hinj⟩
  apply eq_of_subset_of_card_le
  · intro g hg
    obtain ⟨e, he, rfl⟩ := mem_image.1 hg
    have he' := mem_inc.1 he
    rw [Φ_eq hp hn hcubic e he'.1 v he'.2]
    exact mem_incP _ _ (notin_W hp hcubic he)
  · have h1 := inc_card (W G c v)
    have h2 : ((G.incidenceFinset v).image (Φ G c)).card = 3 := by
      rw [card_image_of_injOn hinj, card_incidenceFinset_eq_degree, hcubic]
    omega

lemma fwd (φ : Sym2 V → Sym2 PetersenVertex) (hφ : IsPetersenColoring G φ) :
    Proper G (fun e => colP (φ e)) ∧ Normal G (fun e => colP (φ e)) := by
  choose W hW hinj using hφ
  have himg : ∀ v, (G.incidenceFinset v).image (fun e => colP (φ e)) = univ \ (W v).1 := by
    intro v
    have : (fun e => colP (φ e)) = colP ∘ φ := rfl
    rw [this, ← image_image, hW v, F1]
  have hmem : ∀ v e, e ∈ G.incidenceFinset v → φ e ∈ petersenGraph.incidenceFinset (W v) := by
    intro v e he
    rw [← hW v]; exact mem_image_of_mem φ he
  refine ⟨?_, ?_⟩
  · intro e he f hf hne ⟨v, hve, hvf⟩ hc
    have he' : e ∈ G.incidenceFinset v := mem_inc.2 ⟨mem_edgeFinset.1 he, hve⟩
    have hf' : f ∈ G.incidenceFinset v := mem_inc.2 ⟨mem_edgeFinset.1 hf, hvf⟩
    exact hne (hinj v he' hf' (F2 (W v) (hmem v e he') (hmem v f hf') hc))
  · intro e he
    induction e using Sym2.ind with
    | h u v =>
      have hadj : G.Adj u v := mem_edgeFinset.1 he
      rw [filt_eq G, image_union, himg u, himg v]
      have h1 := hmem u _ (mem_inc.2 ⟨hadj, Sym2.mem_mk_left u v⟩)
      have h2 := hmem v _ (mem_inc.2 ⟨hadj, Sym2.mem_mk_right u v⟩)
      exact F5 _ _ (F4 h1 h2)

end PC

open PC in
theorem petersen_coloring_conjecture.variants.normal_five_edge_coloring
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v, G.degree v = 3) :
    (∃ φ : Sym2 V → Sym2 PetersenVertex, IsPetersenColoring G φ) ↔
    ∃ c : Sym2 V → Fin 5,
      (∀ e ∈ G.edgeFinset, ∀ f ∈ G.edgeFinset, e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → c e ≠ c f) ∧
      ∀ e ∈ G.edgeFinset,
        ((G.edgeFinset.filter fun f => ∃ v, v ∈ e ∧ v ∈ f).image c).card = 3 ∨
        ((G.edgeFinset.filter fun f => ∃ v, v ∈ e ∧ v ∈ f).image c).card = 5 := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨_, fwd φ hφ⟩
  · rintro ⟨c, hp, hn⟩
    exact ⟨_, bwd hp hn hcubic⟩

end PetersenColoringConjecture

#print axioms PetersenColoringConjecture.petersen_coloring_conjecture.variants.normal_five_edge_coloring
