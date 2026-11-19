import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Sym

namespace Erdos1111

/-- Restated from the checkout (ErdosProblems/1111.lean). -/
def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

namespace WG

theorem rep {V : Type*} (p : Sym2 V) : ∃ a b, p = s(a, b) :=
  Sym2.ind (f := fun p => ∃ a b, p = s(a, b)) (fun a b => ⟨a, b, rfl⟩) p

end WG

theorem erdos_1111.variants.wagon (t : ℕ) :
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      ((t.choose 2 + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
        ∃ A B : Set V, Anticomplete G A B ∧
          2 ≤ (G.induce A).chromaticNumber ∧ 2 ≤ (G.induce B).chromaticNumber := by
  intro V _ G hχ hcf
  classical
  have := Fintype.ofFinite V
  by_contra hne
  have hno : ∀ a b x y : V, G.Adj a b → G.Adj x y → ¬G.Adj x a → ¬G.Adj x b →
      ¬G.Adj y a → ¬G.Adj y b → x ≠ a → x ≠ b → y ≠ a → y ≠ b → False := by
    intro a b x y hab hxy hxa hxb hya hyb h1 h2 h3 h4
    apply hne
    refine ⟨{a, b}, {x, y}, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro v hv hv'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hv'
      rcases hv with rfl | rfl <;> rcases hv' with h | h
      · exact h1 h.symm
      · exact h3 h.symm
      · exact h2 h.symm
      · exact h4 h.symm
    · intro u hu v hv huv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact hxa huv.symm
      · exact hya huv.symm
      · exact hxb huv.symm
      · exact hyb huv.symm
    · exact SimpleGraph.two_le_chromaticNumber_of_adj (G := G.induce {a, b})
        (u := ⟨a, by simp⟩) (v := ⟨b, by simp⟩) hab
    · exact SimpleGraph.two_le_chromaticNumber_of_adj (G := G.induce {x, y})
        (u := ⟨x, by simp⟩) (v := ⟨y, by simp⟩) hxy
  obtain ⟨K, hKmem, hKmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun L : Finset V => G.IsClique (L : Set V))) Finset.card
    ⟨∅, by simp⟩
  have hK : G.IsClique (K : Set V) := (Finset.mem_filter.mp hKmem).2
  have hmax : ∀ L : Finset V, G.IsClique (L : Set V) → L.card ≤ K.card := fun L hL =>
    hKmax L (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL⟩)
  have hkt : K.card + 1 ≤ t := by
    by_contra h
    exact (hcf.mono (by omega : t ≤ K.card)) K ⟨hK, rfl⟩
  set M : V → Finset V := fun w => K.filter (fun v => ¬G.Adj w v) with hMdef
  have hMsub : ∀ w, M w ⊆ K := fun w => Finset.filter_subset _ _
  have hMne : ∀ w, (M w).Nonempty := by
    intro w
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    have hw : w ∉ K := fun hw => h hw (G.irrefl)
    have hcl : G.IsClique ((insert w K : Finset V) : Set V) := by
      rw [Finset.coe_insert, SimpleGraph.isClique_insert]
      exact ⟨hK, fun b hb _ => not_not.mp (h hb)⟩
    have := hmax _ hcl
    rw [Finset.card_insert_of_notMem hw] at this
    omega
  have hP : ∀ w, ∃ p ∈ K.sym2, (∀ v ∈ p, v ∈ M w) ∧ (p.IsDiag → ∀ v ∈ M w, v ∈ p) := by
    intro w
    by_cases h2 : ∃ a ∈ M w, ∃ b ∈ M w, a ≠ b
    · obtain ⟨a, ha, b, hb, hab⟩ := h2
      refine ⟨s(a, b), Finset.mk_mem_sym2_iff.mpr ⟨hMsub w ha, hMsub w hb⟩, ?_, ?_⟩
      · intro v hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
      · intro hd
        exact absurd (Sym2.mk_isDiag_iff.mp hd) hab
    · obtain ⟨a, ha⟩ := hMne w
      refine ⟨s(a, a), Finset.mk_mem_sym2_iff.mpr ⟨hMsub w ha, hMsub w ha⟩, ?_, ?_⟩
      · intro v hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
      · intro _ v hv
        have hva : v = a := by
          by_contra hva
          exact h2 ⟨v, hv, a, ha, hva⟩
        rw [hva]
        exact Sym2.mem_mk_left a a
  choose c hcK hc1 hc2 using hP
  have hvalid : ∀ x y, G.Adj x y → c x ≠ c y := by
    intro x y hxy hc
    obtain ⟨a, b, hp⟩ := WG.rep (c x)
    have h1x := hc1 x
    have h1y := hc1 y
    have h2x := hc2 x
    have h2y := hc2 y
    rw [hp] at h1x h2x
    rw [← hc, hp] at h1y h2y
    have hax : a ∈ M x := h1x a (Sym2.mem_mk_left a b)
    have hbx : b ∈ M x := h1x b (Sym2.mem_mk_right a b)
    have hay : a ∈ M y := h1y a (Sym2.mem_mk_left a b)
    have hby : b ∈ M y := h1y b (Sym2.mem_mk_right a b)
    have aK : a ∈ K := hMsub x hax
    have bK : b ∈ K := hMsub x hbx
    by_cases hab : a = b
    · subst hab
      have hd : (s(a, a) : Sym2 V).IsDiag := Sym2.mk_isDiag_iff.mpr rfl
      have hMx : ∀ v ∈ M x, v = a := fun v hv =>
        (Sym2.mem_iff.mp (h2x hd v hv)).elim id id
      have hMy : ∀ v ∈ M y, v = a := fun v hv =>
        (Sym2.mem_iff.mp (h2y hd v hv)).elim id id
      have hadjX : ∀ v ∈ K.erase a, G.Adj x v := by
        intro v hv
        by_contra hn
        exact Finset.ne_of_mem_erase hv
          (hMx v (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hv, hn⟩))
      have hadjY : ∀ v ∈ K.erase a, G.Adj y v := by
        intro v hv
        by_contra hn
        exact Finset.ne_of_mem_erase hv
          (hMy v (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hv, hn⟩))
      have hxE : x ∉ K.erase a := fun hx => G.irrefl (hadjX x hx)
      have hyE : y ∉ K.erase a := fun hy => G.irrefl (hadjY y hy)
      have hxL : x ∉ insert y (K.erase a) := by
        rw [Finset.mem_insert]
        rintro (h | h)
        · exact G.ne_of_adj hxy h
        · exact hxE h
      have hcl : G.IsClique ((insert x (insert y (K.erase a)) : Finset V) : Set V) := by
        rw [Finset.coe_insert, Finset.coe_insert, SimpleGraph.isClique_insert,
          SimpleGraph.isClique_insert]
        refine ⟨⟨hK.subset (Finset.coe_subset.mpr (Finset.erase_subset a K)), ?_⟩, ?_⟩
        · intro v hv _
          exact hadjY v (Finset.mem_coe.mp hv)
        · intro v hv _
          rcases Set.mem_insert_iff.mp hv with rfl | hv'
          · exact hxy
          · exact hadjX v (Finset.mem_coe.mp hv')
      have hcard := hmax _ hcl
      rw [Finset.card_insert_of_notMem hxL, Finset.card_insert_of_notMem hyE,
        Finset.card_erase_of_mem aK] at hcard
      have hpos : 0 < K.card := Finset.card_pos.mpr ⟨a, aK⟩
      omega
    · have hAdj : G.Adj a b := hK (Finset.mem_coe.mpr aK) (Finset.mem_coe.mpr bK) hab
      have nxa : ¬G.Adj x a := (Finset.mem_filter.mp hax).2
      have nxb : ¬G.Adj x b := (Finset.mem_filter.mp hbx).2
      have nya : ¬G.Adj y a := (Finset.mem_filter.mp hay).2
      have nyb : ¬G.Adj y b := (Finset.mem_filter.mp hby).2
      refine hno a b x y hAdj hxy nxa nxb nya nyb ?_ ?_ ?_ ?_
      · rintro rfl
        exact nxb hAdj
      · rintro rfl
        exact nxa hAdj.symm
      · rintro rfl
        exact nyb hAdj
      · rintro rfl
        exact nya hAdj.symm
  let C : G.Coloring {p // p ∈ K.sym2} :=
    SimpleGraph.Coloring.mk (fun w => ⟨c w, hcK w⟩)
      (fun {x y} h heq => hvalid x y h (congrArg Subtype.val heq))
  have hle := C.colorable.chromaticNumber_le
  rw [Fintype.card_coe, Finset.card_sym2] at hle
  have hch : (K.card + 1).choose 2 ≤ t.choose 2 := Nat.choose_le_choose 2 hkt
  have h' : t.choose 2 + 1 ≤ (K.card + 1).choose 2 := by
    exact_mod_cast hχ.trans hle
  omega

#print axioms erdos_1111.variants.wagon

end Erdos1111
