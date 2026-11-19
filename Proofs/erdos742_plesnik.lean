import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open SimpleGraph Finset

set_option linter.unusedSectionVars false

namespace Erdos742

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restated from the checkout (ErdosProblems/742.lean). -/
def IsDiameter2Critical (G : SimpleGraph V) : Prop :=
  G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2

namespace PB

lemma d2_iff (H : SimpleGraph V) (x y : V) :
    H.edist x y ≤ 2 ↔ (x = y ∨ H.Adj x y ∨ ∃ w, H.Adj x w ∧ H.Adj w y) := by
  constructor
  · intro h
    have hne : H.edist x y ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hne
    have hl : p.length ≤ 2 := by rw [← hp] at h; exact_mod_cast h
    cases p with
    | nil => exact Or.inl rfl
    | cons h1 q =>
      cases q with
      | nil => exact Or.inr (Or.inl h1)
      | cons h2 r =>
        cases r with
        | nil => exact Or.inr (Or.inr ⟨_, h1, h2⟩)
        | cons h3 s => simp only [Walk.length_cons] at hl; omega
  · rintro (rfl | h | ⟨w, h1, h2⟩)
    · simp
    · calc H.edist x y ≤ (Walk.cons h Walk.nil).length := edist_le _
        _ ≤ 2 := by simp
    · calc H.edist x y ≤ (Walk.cons h1 (Walk.cons h2 Walk.nil)).length := edist_le _
        _ ≤ 2 := by simp

variable (G : SimpleGraph V)

abbrev TF (u v : V) : Prop := G.Adj u v ∧ ∀ w, ¬(G.Adj u w ∧ G.Adj w v)
abbrev Wit (a b : V) : Prop :=
  ∃ y, y ≠ a ∧ ¬G.Adj a y ∧ ∀ w, (G.Adj a w ∧ G.Adj w y) ↔ w = b
abbrev OU (u v : V) : Prop := G.Adj u v ∧ ¬TF G u v ∧ Wit G u v

lemma tf_symm {u v : V} (h : TF G u v) : TF G v u :=
  ⟨h.1.symm, fun w hw => h.2 w ⟨hw.2.symm, hw.1.symm⟩⟩

lemma ediam2 (hG : IsDiameter2Critical G) : G.ediam = 2 := by
  have hne : G.ediam ≠ ⊤ := ediam_ne_top_of_diam_ne_zero (by rw [hG.1]; decide)
  rw [← ENat.natCast_toNat hne]
  show ((G.diam : ℕ) : ℕ∞) = 2
  rw [hG.1]; simp

lemma key {x y w0 : V} (hxy : x ≠ y) (hna : ¬G.Adj x y) (h1 : G.Adj x w0) (h2 : G.Adj w0 y)
    (e : Sym2 V) (hall : ∀ w, G.Adj x w → G.Adj w y → s(x, w) = e ∨ s(w, y) = e)
    (he : s(x, w0) = e) : Wit G x w0 := by
  refine ⟨y, Ne.symm hxy, hna, fun w => ⟨fun hw => ?_, fun h => by subst h; exact ⟨h1, h2⟩⟩⟩
  rcases hall w hw.1 hw.2 with h | h
  · rw [← he] at h
    exact Sym2.congr_right.mp h
  · rw [← he, Sym2.eq_iff] at h
    rcases h with ⟨h3, _⟩ | ⟨h3, h4⟩
    · subst h3; exact (G.irrefl hw.1).elim
    · exact h3

lemma crit (hG : IsDiameter2Critical G) {u v : V} (huv : G.Adj u v) :
    TF G u v ∨ Wit G u v ∨ Wit G v u := by
  have hE := ediam2 G hG
  have hle : G.deleteEdges {s(u, v)} ≤ G := G.deleteEdges_le _
  have hadj : ∀ a b, (G.deleteEdges {s(u, v)}).Adj a b ↔ G.Adj a b ∧ ¬ s(a, b) = s(u, v) := by
    intro a b; rw [deleteEdges_adj, Set.mem_singleton_iff]
  have hd : (G.deleteEdges {s(u, v)}).diam ≠ 2 := hG.2 _ ((mem_edgeSet G).mpr huv)
  have hex : ∃ x y, ¬ (G.deleteEdges {s(u, v)}).edist x y ≤ 2 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    apply hd
    have h1 : (G.deleteEdges {s(u, v)}).ediam ≤ 2 := ediam_le_of_edist_le hc
    have h2 : G.ediam ≤ (G.deleteEdges {s(u, v)}).ediam := ediam_anti hle
    have h3 : (G.deleteEdges {s(u, v)}).ediam = 2 := le_antisymm h1 (hE ▸ h2)
    show (G.deleteEdges {s(u, v)}).ediam.toNat = 2
    rw [h3]; simp
  obtain ⟨x, y, hxy⟩ := hex
  have hG2 : G.edist x y ≤ 2 := hE ▸ edist_le_ediam
  rw [d2_iff] at hxy hG2
  simp only [not_or, not_exists, not_and] at hxy
  obtain ⟨hne, hna', hnw⟩ := hxy
  by_cases hA : G.Adj x y
  · have hs : s(x, y) = s(u, v) := by
      by_contra hc; exact hna' ((hadj x y).mpr ⟨hA, hc⟩)
    left
    refine ⟨huv, fun w hw => ?_⟩
    have a1 : (G.deleteEdges {s(u, v)}).Adj u w :=
      (hadj u w).mpr ⟨hw.1, fun hc => G.ne_of_adj hw.2 (Sym2.congr_right.mp hc)⟩
    have a2 : (G.deleteEdges {s(u, v)}).Adj w v :=
      (hadj w v).mpr ⟨hw.2, fun hc => G.ne_of_adj hw.1 (Sym2.congr_left.mp hc).symm⟩
    rcases Sym2.eq_iff.mp hs with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · subst hx; subst hy; exact hnw w a1 a2
    · subst hx; subst hy; exact hnw w a2.symm a1.symm
  · obtain ⟨w0, h1, h2⟩ : ∃ w, G.Adj x w ∧ G.Adj w y := by
      rcases hG2 with h | h | h
      · exact absurd h hne
      · exact absurd h hA
      · exact h
    have hall : ∀ w, G.Adj x w → G.Adj w y → s(x, w) = s(u, v) ∨ s(w, y) = s(u, v) := by
      intro w hw1 hw2
      by_contra hc
      simp only [not_or] at hc
      exact hnw w ((hadj x w).mpr ⟨hw1, hc.1⟩) ((hadj w y).mpr ⟨hw2, hc.2⟩)
    rcases hall w0 h1 h2 with he | he
    · have W := key G hne hA h1 h2 _ hall he
      rcases Sym2.eq_iff.mp he with ⟨hx, hw⟩ | ⟨hx, hw⟩
      · subst hx; subst hw; exact Or.inr (Or.inl W)
      · subst hx; subst hw; exact Or.inr (Or.inr W)
    · have hall' : ∀ w, G.Adj y w → G.Adj w x → s(y, w) = s(u, v) ∨ s(w, x) = s(u, v) := by
        intro w hw1 hw2
        exact (hall w hw2.symm hw1.symm).symm.imp (fun h => Sym2.eq_swap.trans h)
          (fun h => Sym2.eq_swap.trans h)
      have he' : s(y, w0) = s(u, v) := Sym2.eq_swap.trans he
      have W := key G (Ne.symm hne) (fun h => hA h.symm) h2.symm h1.symm _ hall' he'
      rcases Sym2.eq_iff.mp he' with ⟨hx, hw⟩ | ⟨hx, hw⟩
      · subst hx; subst hw; exact Or.inr (Or.inl W)
      · subst hx; subst hw; exact Or.inr (Or.inr W)

variable [DecidableRel G.Adj]

def t (u : V) : ℕ := (univ.filter (TF G u)).card
def o (u : V) : ℕ := (univ.filter (OU G u)).card

lemma core (u : V) (X : Finset V)
    (hX : ∀ v, OU G u v → ∀ y, y ≠ u → ¬G.Adj u y →
      (∀ w, (G.Adj u w ∧ G.Adj w y) ↔ w = v) → y ∉ X) :
    o G u + X.card ≤ Fintype.card V := by
  have : ∀ v ∈ univ.filter (OU G u),
      ∃ y, y ≠ u ∧ ¬G.Adj u y ∧ ∀ w, (G.Adj u w ∧ G.Adj w y) ↔ w = v :=
    fun v hv => (mem_filter.mp hv).2.2.2
  choose! f hf using this
  have hinj : Set.InjOn f (univ.filter (OU G u)) := by
    intro a ha b hb hab
    have hb' := ((hf b hb).2.2 b).mpr rfl
    rw [← hab] at hb'
    exact (((hf a ha).2.2 b).mp hb').symm
  have hdisj : Disjoint ((univ.filter (OU G u)).image f) X := by
    rw [Finset.disjoint_left]
    intro z hz
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hz
    exact hX v (mem_filter.mp hv).2 (f v) (hf v hv).1 (hf v hv).2.1 (hf v hv).2.2
  calc o G u + X.card = ((univ.filter (OU G u)).image f).card + X.card := by
        rw [card_image_of_injOn hinj]; rfl
    _ = (((univ.filter (OU G u)).image f) ∪ X).card := (card_union_of_disjoint hdisj).symm
    _ ≤ Fintype.card V := card_le_univ _

lemma I1 (u : V) : o G u + G.degree u + 1 ≤ Fintype.card V := by
  have hu : u ∉ G.neighborFinset u := by simp
  have := core G u (insert u (G.neighborFinset u)) (by
    intro v _ y hyu hna _ hy
    rcases mem_insert.mp hy with h | h
    · exact hyu h
    · exact hna ((mem_neighborFinset _ _ _).mp h))
  rw [card_insert_of_notMem hu, card_neighborFinset_eq_degree] at this
  omega

lemma I2 {u v : V} (htf : TF G u v) :
    o G u + G.degree u + G.degree v ≤ Fintype.card V := by
  have hdisj : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [mem_neighborFinset] at hz hz'
    exact htf.2 z ⟨hz, hz'.symm⟩
  have := core G u (G.neighborFinset u ∪ G.neighborFinset v) (by
    intro v' hv' y _ hna hun hy
    rcases mem_union.mp hy with h | h
    · exact hna ((mem_neighborFinset _ _ _).mp h)
    · have hv : v = v' := (hun v).mp ⟨htf.1, (mem_neighborFinset _ _ _).mp h⟩
      exact hv'.2.1 (hv ▸ htf))
  rw [card_union_of_disjoint hdisj, card_neighborFinset_eq_degree,
    card_neighborFinset_eq_degree] at this
  omega

lemma t_le (v : V) : t G v ≤ G.degree v := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  exact card_le_card (fun w hw => by
    simp only [mem_filter] at hw ⊢
    exact ⟨hw.1, hw.2.1⟩)

lemma edges (hG : IsDiameter2Critical G) :
    2 * G.edgeFinset.card ≤ ∑ u, t G u + 2 * ∑ u, o G u := by
  rw [← sum_degrees_eq_twice_card_edges]
  have hd : ∀ u, G.degree u = ∑ v, if G.Adj u v then 1 else 0 := by
    intro u
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]
  have ht : ∀ u, t G u = ∑ v, if TF G u v then 1 else 0 := fun u => card_filter _ _
  have ho : ∀ u, o G u = ∑ v, if OU G u v then 1 else 0 := fun u => card_filter _ _
  have hk : ∀ u v, (if G.Adj u v then 1 else 0) ≤
      (if TF G u v then 1 else 0) + (if OU G u v then 1 else 0) +
        (if OU G v u then 1 else 0) := by
    intro u v
    by_cases hA : G.Adj u v
    · rw [if_pos hA]
      by_cases hT : TF G u v
      · rw [if_pos hT]; omega
      · rcases crit G hG hA with h | h | h
        · exact absurd h hT
        · have h' : OU G u v := ⟨hA, hT, h⟩
          rw [if_pos h']; omega
        · have h' : OU G v u := ⟨hA.symm, fun h'' => hT (tf_symm G h''), h⟩
          rw [if_pos h']; omega
    · rw [if_neg hA]; exact Nat.zero_le _
  simp only [hd, ht, ho]
  calc ∑ u, ∑ v, (if G.Adj u v then 1 else 0)
      ≤ ∑ u, ∑ v, ((if TF G u v then 1 else 0) + (if OU G u v then 1 else 0) +
          (if OU G v u then 1 else 0)) :=
        sum_le_sum fun u _ => sum_le_sum fun v _ => hk u v
    _ = ∑ u, ∑ v, (if TF G u v then 1 else 0) + ∑ u, ∑ v, (if OU G u v then 1 else 0) +
          ∑ u, ∑ v, (if OU G v u then 1 else 0) := by simp only [sum_add_distrib]
    _ = ∑ u, ∑ v, (if TF G u v then 1 else 0) + 2 * ∑ u, ∑ v, (if OU G u v then 1 else 0) := by
        rw [Finset.sum_comm (f := fun u v => if OU G v u then 1 else 0)]; omega

lemma amgm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 2 ≤ a / b + b / a := by
  rw [div_add_div _ _ (ne_of_gt hb) (ne_of_gt ha), le_div_iff₀ (mul_pos hb ha)]
  nlinarith [sq_nonneg (a - b)]

lemma t_pos {u v : V} (h : TF G u v) : 0 < t G u :=
  Finset.card_pos.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, h⟩⟩

lemma sym :
    ∑ u, (t G u : ℝ) ≤ ∑ u, ∑ v, (if TF G u v then (t G v : ℝ) / t G u else 0) := by
  have hpt : ∀ u v, 2 * (if TF G u v then (1 : ℝ) else 0) ≤
      (if TF G u v then (t G v : ℝ) / t G u else 0) +
        (if TF G v u then (t G u : ℝ) / t G v else 0) := by
    intro u v
    by_cases h : TF G u v
    · have h' := tf_symm G h
      rw [if_pos h, if_pos h, if_pos h']
      have := amgm (a := (t G v : ℝ)) (b := (t G u : ℝ))
        (by exact_mod_cast t_pos G h') (by exact_mod_cast t_pos G h)
      linarith
    · have h' : ¬TF G v u := fun h'' => h (tf_symm G h'')
      rw [if_neg h, if_neg h, if_neg h']; simp
  have htu : ∀ u, (t G u : ℝ) = ∑ v, if TF G u v then (1 : ℝ) else 0 := by
    intro u; rw [Finset.sum_boole]; rfl
  have hsum := sum_le_sum fun u (_ : u ∈ univ) => sum_le_sum fun v (_ : v ∈ univ) => hpt u v
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [Finset.sum_comm (f := fun u v => if TF G v u then (t G u : ℝ) / t G v else 0)] at hsum
  have hL : ∑ u, (t G u : ℝ) = ∑ u, ∑ v, (if TF G u v then (1 : ℝ) else 0) :=
    sum_congr rfl fun u _ => htu u
  rw [hL]
  linarith

lemma three_le (hG : IsDiameter2Critical G) : 3 ≤ Fintype.card V := by
  have hE := ediam2 G hG
  have : Nontrivial V := nontrivial_of_diam_ne_zero (G := G) (by rw [hG.1]; decide)
  obtain ⟨x, y, hxy⟩ := exists_edist_eq_ediam_of_finite (G := G)
  rw [hE] at hxy
  have h2 := (d2_iff G x y).mp hxy.le
  have hne : x ≠ y := by rintro rfl; simp at hxy
  have hna : ¬G.Adj x y := fun h => by
    rw [edist_eq_one_iff_adj.mpr h] at hxy; norm_num at hxy
  obtain ⟨w, h1, h3⟩ : ∃ w, G.Adj x w ∧ G.Adj w y := by
    rcases h2 with h | h | h
    · exact absurd h hne
    · exact absurd h hna
    · exact h
  have : ({x, w, y} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, w, y, G.ne_of_adj h1, hne, G.ne_of_adj h3, rfl⟩
  rw [← this]; exact card_le_univ _

omit [Fintype V] [DecidableEq V] in
lemma small (E b : ℕ) (x y : ℝ) (h : 6 * (E : ℝ) ≤ x) (hb : x < 6 * ((b : ℝ) + 1))
    (hy : (b : ℝ) < y) : (E : ℝ) < y := by
  have hE : E ≤ b := by
    by_contra hc
    have : (b : ℝ) + 1 ≤ E := by exact_mod_cast (by omega : b + 1 ≤ E)
    linarith
  have : (E : ℝ) ≤ b := by exact_mod_cast hE
  linarith

omit [Fintype V] [DecidableEq V] in
lemma arith (E n : ℕ) (h3 : 3 ≤ n) (h : 6 * (E : ℝ) ≤ 2 * ((n : ℝ) * n) - n) :
    (E : ℝ) < 3 * n * (n - 1) / 8 := by
  rcases (by omega : n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n) with rfl | rfl | rfl | h6
  · push_cast at h ⊢; exact small E 2 _ _ h (by norm_num) (by norm_num)
  · push_cast at h ⊢; exact small E 4 _ _ h (by norm_num) (by norm_num)
  · push_cast at h ⊢; exact small E 7 _ _ h (by norm_num) (by norm_num)
  · have h6' : (6 : ℝ) ≤ n := by exact_mod_cast h6
    nlinarith [mul_nonneg (sub_nonneg.mpr h6') (by positivity : (0 : ℝ) ≤ n)]

end PB

open PB in
theorem plesnik_bound (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (G.edgeFinset.card : ℝ) < 3 * (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 8 := by
  have h3 := three_le G hG
  have hedge := edges G hG
  have hdeg := sum_degrees_eq_twice_card_edges G
  set n := Fintype.card V with hn
  set E := G.edgeFinset.card with hEdef
  have hEr : 2 * (E : ℝ) ≤ ∑ u, (t G u : ℝ) + 2 * ∑ u, (o G u : ℝ) := by exact_mod_cast hedge
  have hdegr : ∑ u, (G.degree u : ℝ) = 2 * E := by exact_mod_cast hdeg
  let c : V → ℝ := fun u => n - 1 - G.degree u - o G u
  have hc0 : ∀ u, 0 ≤ c u := fun u => by
    have h1 := I1 G u
    have : ((o G u + G.degree u + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
    push_cast at this; simp only [c]; linarith
  have hc1 : ∀ u v, TF G u v → (t G v : ℝ) - 1 ≤ c u := fun u v h => by
    have h1 := I2 G h
    have h2 := t_le G v
    have : ((o G u + G.degree u + G.degree v : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
    have h2' : (t G v : ℝ) ≤ G.degree v := by exact_mod_cast h2
    push_cast at this; simp only [c]; linarith
  have havg : ∀ u, ∑ v, (if TF G u v then ((t G v : ℝ) - 1) / t G u else 0) ≤ c u := by
    intro u
    by_cases h0 : t G u = 0
    · have hno : ∀ v, ¬TF G u v := fun v hv => by have := t_pos G hv; omega
      rw [sum_eq_zero (fun v _ => if_neg (hno v))]; exact hc0 u
    · have hpos : (0 : ℝ) < t G u := by exact_mod_cast Nat.pos_of_ne_zero h0
      calc ∑ v, (if TF G u v then ((t G v : ℝ) - 1) / t G u else 0)
          ≤ ∑ v, (if TF G u v then c u / t G u else 0) := sum_le_sum fun v _ => by
            split_ifs with h
            · gcongr; exact hc1 u v h
            · exact le_rfl
        _ = c u := by
            rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
            show (t G u : ℝ) * (c u / t G u) = c u
            rw [mul_comm, div_mul_cancel₀ _ hpos.ne']
  have hk : ∀ u, ∑ v, (if TF G u v then 1 / (t G u : ℝ) else 0) ≤ 1 ∧
      ∑ v, (if TF G u v then 1 / (t G u : ℝ) else 0) ≤ t G u := by
    intro u
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    show (t G u : ℝ) * (1 / t G u) ≤ 1 ∧ (t G u : ℝ) * (1 / t G u) ≤ t G u
    by_cases h0 : t G u = 0
    · simp [h0]
    · have hpos : (1 : ℝ) ≤ t G u := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      rw [mul_one_div_cancel (by positivity)]
      exact ⟨le_rfl, hpos⟩
  have hsplit : ∀ u, ∑ v, (if TF G u v then ((t G v : ℝ) - 1) / t G u else 0) =
      ∑ v, (if TF G u v then (t G v : ℝ) / t G u else 0) -
        ∑ v, (if TF G u v then 1 / (t G u : ℝ) else 0) := by
    intro u; rw [← sum_sub_distrib]; refine sum_congr rfl fun v _ => ?_
    split_ifs <;> simp [sub_div]
  have hsym := sym G
  have hK1 : ∑ u, ∑ v, (if TF G u v then 1 / (t G u : ℝ) else 0) ≤ n := by
    calc _ ≤ ∑ _u : V, (1 : ℝ) := sum_le_sum fun u _ => (hk u).1
      _ = n := by rw [sum_const, card_univ, nsmul_eq_mul, mul_one]
  have hK2 : ∑ u, ∑ v, (if TF G u v then 1 / (t G u : ℝ) else 0) ≤ ∑ u, (t G u : ℝ) :=
    sum_le_sum fun u _ => (hk u).2
  have hC : ∑ u, (t G u : ℝ) - ∑ u, ∑ v, (if TF G u v then 1 / (t G u : ℝ) else 0) ≤
      ∑ u, c u := by
    have := sum_le_sum fun u (_ : u ∈ univ) => havg u
    simp only [hsplit, sum_sub_distrib] at this
    linarith
  have hCsum : ∑ u, c u = (n : ℝ) * n - n - 2 * E - ∑ u, (o G u : ℝ) := by
    simp only [c, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hdegr]; ring
  have hfin : 6 * (E : ℝ) ≤ 2 * ((n : ℝ) * n) - n := by linarith
  exact arith E n h3 hfin

end Erdos742

#print axioms Erdos742.plesnik_bound
