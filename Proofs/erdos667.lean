import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open SimpleGraph Filter

namespace Erdos667

def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p → q ≤ (G.induce s).edgeSet.ncard

open Classical in
noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree m) n

noncomputable def c (p q : ℕ) : ℝ :=
  liminf (fun n : ℕ => Real.log (H p q n) / Real.log n) atTop

lemma log_mono_nat {a b : ℕ} (h : a ≤ b) : Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h)

lemma H_le (p q n : ℕ) : H p q n ≤ n := by
  classical
  unfold H
  exact Nat.findGreatest_le n

lemma ratio_le_one (p q n : ℕ) : Real.log (H p q n) / Real.log n ≤ 1 :=
  div_le_one_of_le₀ (log_mono_nat (H_le p q n)) (Real.log_natCast_nonneg _)

/-- If every `G`-edge inside `s` lies inside `t ⊆ s`, then `s` spans at most `C(|t|, 2)` edges. -/
lemma edge_le {n : ℕ} (G : SimpleGraph (Fin n)) (s t : Finset (Fin n)) (hts : t ⊆ s)
    (h : ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → a ∈ t ∧ b ∈ t) :
    (G.induce (s : Set (Fin n))).edgeSet.ncard ≤ t.card.choose 2 := by
  classical
  let f : ↥(t : Set (Fin n)) → ↥(s : Set (Fin n)) := fun x => ⟨x.1, hts x.2⟩
  have hsub : (G.induce (s : Set (Fin n))).edgeSet ⊆
      Sym2.map f '' (G.induce (t : Set (Fin n))).edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    have he' : G.Adj a.1 b.1 := he
    obtain ⟨ha, hb⟩ := h a.1 a.2 b.1 b.2 he'
    refine ⟨s(⟨a.1, ha⟩, ⟨b.1, hb⟩), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeSet]; exact he'
    · rfl
  calc (G.induce (s : Set (Fin n))).edgeSet.ncard
      ≤ (Sym2.map f '' (G.induce (t : Set (Fin n))).edgeSet).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (G.induce (t : Set (Fin n))).edgeSet.ncard := Set.ncard_image_le (Set.toFinite _)
    _ = (G.induce (t : Set (Fin n))).edgeFinset.card := by
        rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    _ ≤ (Fintype.card (t : Set (Fin n))).choose 2 := card_edgeFinset_le_card_choose_two
    _ = t.card.choose 2 := by simp

open Classical in
/-- In a `(r+2, C(r+1,2)+1)`-locally dense graph every vertex has at most `r` non-neighbours. -/
lemma nonadj_card {n r : ℕ} (G : SimpleGraph (Fin n))
    (hG : LocallyDense (r + 2) ((r + 2 - 1).choose 2 + 1) G) (v : Fin n) :
    (Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card ≤ r := by
  classical
  by_contra hc
  have hc' : r + 1 ≤ (Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card := by omega
  obtain ⟨N, hNsub, hNcard⟩ := Finset.exists_subset_card_eq hc'
  have hmem : ∀ u ∈ N, u ≠ v ∧ ¬ G.Adj v u := fun u hu => by
    simpa using hNsub hu
  have hvN : v ∉ N := fun hv => (hmem v hv).1 rfl
  have hcard : (insert v N).card = r + 2 := by
    rw [Finset.card_insert_of_notMem hvN, hNcard]
  have h1 := hG (insert v N) hcard
  have h2 := edge_le G (insert v N) N (Finset.subset_insert _ _) (by
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd hab G.irrefl
      · exact absurd hab (hmem b hb).2
    · rcases hb with rfl | hb
      · exact absurd hab.symm (hmem a ha).2
      · exact ⟨ha, hb⟩)
  rw [hNcard, show r + 2 - 1 = r + 1 by omega] at *
  omega

open Classical in
/-- Greedy clique: if every vertex has at most `d` non-neighbours, every `S` contains a clique
`I` with `|S| ≤ (d+1)|I|`. -/
lemma greedy {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ)
    (hd : ∀ v, (Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card ≤ d) :
    ∀ S : Finset (Fin n), ∃ I ⊆ S, G.IsClique (I : Set (Fin n)) ∧ S.card ≤ (d + 1) * I.card := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · exact ⟨∅, by simp, by simp, by simp⟩
  · set T := S.filter (fun u => G.Adj v u) with hT
    have hTS : T ⊂ S := Finset.filter_ssubset.2 ⟨v, hv, G.irrefl⟩
    obtain ⟨I, hIT, hIc, hIcard⟩ := ih T hTS
    have hvI : v ∉ I := fun h => G.irrefl (Finset.mem_filter.1 (hIT h)).2
    refine ⟨insert v I, ?_, ?_, ?_⟩
    · exact Finset.insert_subset hv (hIT.trans hTS.subset)
    · rw [Finset.coe_insert]
      exact hIc.insert (fun b hb _ => (Finset.mem_filter.1 (hIT hb)).2)
    · rw [Finset.card_insert_of_notMem hvI]
      have hsub : S ⊆ insert v (T ∪ Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)) := by
        intro u hu
        rw [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        by_cases huv : u = v
        · exact Or.inl huv
        · by_cases hadj : G.Adj v u
          · exact Or.inr (Or.inl ⟨hu, hadj⟩)
          · exact Or.inr (Or.inr ⟨Finset.mem_univ _, huv, hadj⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_insert_le v
        (T ∪ Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u))
      have h3 := Finset.card_union_le T (Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u))
      have h4 := hd v
      nlinarith

lemma H_lower {n r m : ℕ} (hm : ∀ k, n ≤ (r + 1) * k → m ≤ k) (hmn : m ≤ n) :
    m ≤ H (r + 2) ((r + 2 - 1).choose 2 + 1) n := by
  classical
  unfold H
  apply Nat.le_findGreatest hmn
  intro G hG hcf
  obtain ⟨I, -, hIc, hIcard⟩ := greedy G r (nonadj_card G hG) Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hIcard
  exact (hcf.mono (hm _ hIcard)) I ⟨hIc, rfl⟩

lemma ceil_facts (n r : ℕ) :
    (∀ k, n ≤ (r + 1) * k → (n + r) / (r + 1) ≤ k) ∧ (n + r) / (r + 1) ≤ n ∧
      n ≤ (r + 1) * ((n + r) / (r + 1)) := by
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).2 (by nlinarith))
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Nat.div_le_of_le_mul (by nlinarith)
  · have h1 := Nat.div_add_mod (n + r) (r + 1)
    have h2 := Nat.mod_lt (n + r) (show r + 1 > 0 by omega)
    nlinarith

lemma lower_ratio (r n : ℕ) (hn : 2 ≤ n) :
    1 - Real.log (r + 1) / Real.log n ≤
      Real.log (H (r + 2) ((r + 2 - 1).choose 2 + 1) n) / Real.log n := by
  obtain ⟨hk, hmn, hnm⟩ := ceil_facts n r
  have hH := H_lower (r := r) hk hmn
  set h := H (r + 2) ((r + 2 - 1).choose 2 + 1) n with hh
  have hnh : n ≤ (r + 1) * h := le_trans hnm (Nat.mul_le_mul_left _ hH)
  have hhpos : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · rw [h0] at hnh; omega
    · exact h0
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hlog : Real.log n ≤ Real.log (r + 1) + Real.log h := by
    rw [← Real.log_mul (ne_of_gt (by have := (Nat.cast_nonneg r : (0:ℝ) ≤ r); linarith)) (by exact_mod_cast hhpos.ne')]
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnh)
  rw [le_div_iff₀ hL]
  have : (1 - Real.log (r + 1) / Real.log n) * Real.log n = Real.log n - Real.log (r + 1) := by
    field_simp
  linarith

theorem erdos_667.variants.endpoint (p : ℕ) (hp : 2 ≤ p) :
    c p (Nat.choose (p - 1) 2 + 1) = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 2 := ⟨p - 2, by omega⟩
  unfold c
  apply Tendsto.liminf_eq
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun n : ℕ => 1 - Real.log (r + 1) / Real.log n) atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := Real.log (r + 1))).div_atTop hlog
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact lower_ratio r n hn
  · exact Eventually.of_forall (fun n => ratio_le_one _ _ n)

lemma H_mono (p : ℕ) {q q' : ℕ} (h : q ≤ q') (n : ℕ) : H p q n ≤ H p q' n := by
  classical
  unfold H
  apply Nat.findGreatest_mono_left
  intro m hm G hG
  exact hm G (fun s hs => le_trans h (hG s hs))

lemma ratio_nonneg (p q n : ℕ) : 0 ≤ Real.log (H p q n) / Real.log n :=
  div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

theorem erdos_667.variants.monotoneOn (p : ℕ) :
    MonotoneOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1)) := by
  intro q _ q' _ hqq'
  unfold c
  apply liminf_le_liminf
  · refine Eventually.of_forall (fun n => ?_)
    exact div_le_div_of_nonneg_right (log_mono_nat (H_mono p hqq' n))
      (Real.log_natCast_nonneg _)
  · exact isBoundedUnder_of ⟨0, fun n => ratio_nonneg p q n⟩
  · exact isCoboundedUnder_ge_of_le atTop (fun n => ratio_le_one p q' n)

end Erdos667

#print axioms Erdos667.erdos_667.variants.endpoint
#print axioms Erdos667.erdos_667.variants.monotoneOn
