import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Restated from the checkout
(FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean). -/
namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Check if a list of vertices forms an induced path in `G`. -/
def isInducedPath (G : SimpleGraph α) (l : List α) : Prop :=
  l.Nodup ∧ ∀ i j : Fin l.length, G.Adj (l.get i) (l.get j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- The path number of a graph: The number of vertices of a largest induced path of the graph. -/
noncomputable def path (G : SimpleGraph α) : ℕ :=
  open scoped Classical in
  let induced_paths := Finset.univ.filter (fun s : Finset α =>
    ∃ l : List α, l.toFinset = s ∧ isInducedPath G l)
  (induced_paths.image Finset.card).max.getD 0

/-- A uniform upper bound on the lengths of induced paths bounds `path`
(proof copied from the checkout). -/
theorem path_le_of_isInducedPath_length_le (G : SimpleGraph α) (k : ℕ)
    (h : ∀ l : List α, G.isInducedPath l → l.length ≤ k) : path G ≤ k := by
  classical
  unfold path
  let inducedPaths := Finset.univ.filter (fun s : Finset α ↦
    ∃ vertices : List α, vertices.toFinset = s ∧ G.isInducedPath vertices)
  change (inducedPaths.image Finset.card).max.getD 0 ≤ k
  have hmax : (inducedPaths.image Finset.card).max ≤ (k : WithBot ℕ) := by
    apply Finset.max_le
    intro cardinality hcardinality
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hcardinality
    obtain ⟨_, vertices, rfl, hvertices⟩ := Finset.mem_filter.mp hs
    rw [List.toFinset_card_of_nodup hvertices.1]
    exact WithBot.coe_le_coe.mpr (h vertices hvertices)
  cases hmaximum : (inducedPaths.image Finset.card).max with
  | bot => exact Nat.zero_le k
  | coe maximum =>
      have : maximum ≤ k := by
        rw [hmaximum] at hmax
        exact WithBot.coe_le_coe.mp hmax
      simpa [hmaximum, Option.getD] using this

/-- If `G` has no induced path on `k + 1` vertices, then `path G ≤ k`
(proof copied from the checkout). -/
theorem path_le_of_not_exists_inducedPath_succ (G : SimpleGraph α) (k : ℕ)
    (h : ¬ ∃ e : Fin (k + 1) → α, Function.Injective e ∧
      ∀ i j : Fin (k + 1), G.Adj (e i) (e j) ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val) : path G ≤ k := by
  classical
  apply path_le_of_isInducedPath_length_le G k
  intro l hl
  by_contra hlength
  have hprefix : k + 1 ≤ l.length := by omega
  apply h
  let e : Fin (k + 1) → α := fun i ↦ l.get ⟨i.val, lt_of_lt_of_le i.isLt hprefix⟩
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact congrArg (fun n : Fin l.length ↦ n.val) (hl.1.injective_get hij)
  · intro i j
    simpa only [e] using
      hl.2 ⟨i.val, lt_of_lt_of_le i.isLt hprefix⟩ ⟨j.val, lt_of_lt_of_le j.isLt hprefix⟩

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture34

open SimpleGraph

/-! The counterexample: vertex 0 is the centre `p4`, vertices 1..31 are the perfect
binary tree of depth 4 in heap order (root 1, children of `i` are `2i`, `2i+1`),
32, 33, 34 are `p3, p2, p1`, 35 is the hub and 36, 37, 38 are its pendant leaves.
`par i` is the parent of `i` in the tree rooted at 0, `dep i` the depth. -/
def par (i : ℕ) : ℕ :=
  if i = 1 then 0 else if i ≤ 31 then i / 2 else if i = 32 then 0
  else if i ≤ 35 then i - 1 else 35

def dep (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i < 2 then 1 else if i < 4 then 2 else if i < 8 then 3
  else if i < 16 then 4 else if i < 32 then 5 else if i ≤ 35 then i - 31 else 5

def G34 : SimpleGraph (Fin 39) where
  Adj a b := (a.val ≠ 0 ∧ par a.val = b.val) ∨ (b.val ≠ 0 ∧ par b.val = a.val)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun v h => by
    have key : ∀ v : Fin 39, ¬ (v.val ≠ 0 ∧ par v.val = v.val) := by decide
    rcases h with h | h <;> exact key v h⟩

instance : DecidableRel G34.Adj := fun a b =>
  inferInstanceAs (Decidable ((a.val ≠ 0 ∧ par a.val = b.val) ∨ (b.val ≠ 0 ∧ par b.val = a.val)))

lemma dep_par : ∀ v : Fin 39, v.val ≠ 0 → dep (par v.val) + 1 = dep v.val := by decide

lemma par_lt : ∀ v : Fin 39, par v.val < 39 := by decide

lemma dep_le : ∀ v : Fin 39, dep v.val ≤ 5 := by decide

lemma dep_zero : ∀ v : Fin 39, dep v.val = 0 → v = 0 := by decide

/-- Walks to the centre along parents. -/
lemma walk0 : ∀ n, ∀ v : Fin 39, dep v.val = n → ∃ p : G34.Walk v 0, p.length = n := by
  intro n
  induction n with
  | zero =>
    intro v hv
    have := dep_zero v hv
    subst this
    exact ⟨Walk.nil, rfl⟩
  | succ n ih =>
    intro v hv
    have hv0 : v.val ≠ 0 := by
      intro h0
      rw [h0] at hv
      simp [dep] at hv
    obtain ⟨p, hp⟩ := ih ⟨par v.val, par_lt v⟩ (by
      have := dep_par v hv0
      simp only
      omega)
    have hadj : G34.Adj v ⟨par v.val, par_lt v⟩ := Or.inl ⟨hv0, rfl⟩
    exact ⟨Walk.cons hadj p, by simp [hp]⟩

lemma conn : G34.Connected := by
  have reach : ∀ u : Fin 39, G34.Reachable u 0 := by
    intro u
    obtain ⟨p, _⟩ := walk0 _ u rfl
    exact ⟨p⟩
  exact Connected.mk (fun u v => (reach u).trans (reach v).symm)

/-- Potential lower bound along walks. -/
lemma pot (f : Fin 39 → ℕ) (hf : ∀ a b, G34.Adj a b → f b ≤ f a + 1) {u v : Fin 39}
    (p : G34.Walk u v) : f v ≤ f u + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have := hf _ _ h
    simp only [Walk.length_cons]
    omega

lemma dist_ge (f : Fin 39 → ℕ) (hf : ∀ a b, G34.Adj a b → f b ≤ f a + 1) (u v : Fin 39) :
    f v ≤ f u + G34.dist u v := by
  obtain ⟨p, hp⟩ := conn.exists_walk_length_eq_dist u v
  rw [← hp]
  exact pot f hf p

/-! Potentials. -/
def fdep (v : Fin 39) : ℕ := dep v.val

/-- distance from the hub 35 -/
def fhub (v : Fin 39) : ℕ :=
  if v.val = 0 then 4 else if v.val ≤ 31 then 4 + dep v.val
  else if v.val ≤ 35 then 35 - v.val else 1

/-- distance from the leaf 36 -/
def f36 (v : Fin 39) : ℕ :=
  if v.val = 0 then 5 else if v.val ≤ 31 then 5 + dep v.val
  else if v.val ≤ 35 then 36 - v.val else if v.val = 36 then 0 else 2

/-- a lower bound for the distance from the deep leaf 31 -/
def f31 (v : Fin 39) : ℕ :=
  if v.val ≤ 31 then 5 - dep v.val else 5 + dep v.val

lemma lip_dep : ∀ a b, G34.Adj a b → fdep b ≤ fdep a + 1 := by decide
lemma lip_hub : ∀ a b, G34.Adj a b → fhub b ≤ fhub a + 1 := by decide
lemma lip_36 : ∀ a b, G34.Adj a b → f36 b ≤ f36 a + 1 := by decide
lemma lip_31 : ∀ a b, G34.Adj a b → f31 b ≤ f31 a + 1 := by decide

lemma sum_dep : ∑ v : Fin 39, fdep v = 154 := by decide
lemma sum_hub : ∑ v : Fin 39, fhub v = 266 := by decide

lemma far : ∀ w : Fin 39, w ≠ 0 → 6 ≤ f36 w ∨ 6 ≤ f31 w := by decide

lemma ecc0 : G34.eccent 0 ≤ ((5 : ℕ) : ℕ∞) := by
  rw [eccent_le_iff]
  intro v
  obtain ⟨p, hp⟩ := walk0 _ v rfl
  calc G34.edist 0 v ≤ p.reverse.length := edist_le p.reverse
    _ ≤ ((5 : ℕ) : ℕ∞) := by
      rw [Walk.length_reverse, hp]
      exact_mod_cast dep_le v

lemma ecc_big (v : Fin 39) (hv : v ≠ 0) : ((6 : ℕ) : ℕ∞) ≤ G34.eccent v := by
  have key : ∀ w : Fin 39, 6 ≤ G34.dist v w → ((6 : ℕ) : ℕ∞) ≤ G34.eccent v := by
    intro w hw
    have h4 : (G34.dist v w : ℕ∞) ≤ G34.eccent v := by
      rw [(conn.preconnected v w).coe_dist_eq_edist]
      exact edist_le_eccent
    exact (Nat.cast_le.2 hw).trans h4
  rcases far v hv with h | h
  · apply key 36
    have h1 := dist_ge f36 lip_36 36 v
    have h2 : f36 36 = 0 := by decide
    rw [dist_comm]
    omega
  · apply key 31
    have h1 := dist_ge f31 lip_31 31 v
    have h2 : f31 31 = 0 := by decide
    rw [dist_comm]
    omega

lemma center_eq : G34.center = {0} := by
  ext v
  rw [mem_center_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hv
    have h1 := ecc_big v hv
    have h2 : G34.radius ≤ ((5 : ℕ) : ℕ∞) := radius_le_eccent.trans ecc0
    rw [← h] at h2
    have := Nat.cast_le.1 (h1.trans h2)
    omega
  · rintro rfl
    obtain ⟨u, hu⟩ := G34.exists_eccent_eq_radius
    by_cases hu0 : u = 0
    · subst hu0
      exact hu
    · exfalso
      have h1 := ecc_big u hu0
      have h2 : G34.eccent u ≤ ((5 : ℕ) : ℕ∞) := by
        rw [hu]
        exact radius_le_eccent.trans ecc0
      have := Nat.cast_le.1 (h1.trans h2)
      omega

lemma M_eq : {v | G34.degree v = G34.maxDegree} = ({35} : Set (Fin 39)) := by
  have hdeg : ∀ v, G34.degree v = (Finset.univ.filter (G34.Adj v)).card := by
    intro v
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have d1 : ∀ v : Fin 39, (Finset.univ.filter (G34.Adj v)).card ≤ 4 := by decide
  have d2 : (Finset.univ.filter (G34.Adj 35)).card = 4 := by decide
  have d3 : ∀ v : Fin 39, (Finset.univ.filter (G34.Adj v)).card = 4 → v = 35 := by decide
  have hmax : G34.maxDegree = 4 := by
    apply le_antisymm
    · apply G34.maxDegree_le_of_forall_degree_le
      intro v
      rw [hdeg]
      exact d1 v
    · have := G34.degree_le_maxDegree 35
      rw [hdeg, d2] at this
      exact this
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, hmax, hdeg]
  constructor
  · exact d3 v
  · rintro rfl
    exact d2

lemma mem_filter_gen {β : Type*} (p : β → Prop) (i : DecidablePred p) (s : Finset β) (a : β) :
    a ∈ @Finset.filter β p i s ↔ a ∈ s ∧ p a := Finset.mem_filter

lemma mem_toFinset_gen {β : Type*} (S : Set β) (i : Fintype S) (a : β) :
    a ∈ @Set.toFinset β S i ↔ a ∈ S := Set.mem_toFinset

lemma avg_core (s : Fin 39) (f : Fin 39 → ℕ) (hf : ∀ a b, G34.Adj a b → f b ≤ f a + 1)
    (hs : f s = 0) (n : ℕ) (hn : ∑ v, f v = n) (hpos : 0 < n)
    (T : Finset (Fin 39 × Fin 39)) (hT : ∀ p, p ∈ T ↔ p.1 = s ∧ G34.dist p.1 p.2 ≠ 0) :
    (n : ℝ) / 38 ≤ (∑ p ∈ T, (G34.dist p.1 p.2 : ℝ)) / (T.card : ℝ) := by
  have hsub : T ⊆ ({s} : Finset (Fin 39)) ×ˢ Finset.univ := by
    intro p hp
    rw [hT] at hp
    rw [Finset.mem_product, Finset.mem_singleton]
    exact ⟨hp.1, Finset.mem_univ _⟩
  have hsum : ∑ p ∈ T, (G34.dist p.1 p.2 : ℝ) = ∑ v, (G34.dist s v : ℝ) := by
    rw [Finset.sum_subset hsub]
    · rw [Finset.sum_product, Finset.sum_singleton]
    · intro p hp hpT
      have hp1 : p.1 = s := Finset.mem_singleton.1 (Finset.mem_product.1 hp).1
      have : G34.dist p.1 p.2 = 0 := by
        by_contra h
        exact hpT ((hT p).2 ⟨hp1, h⟩)
      simp [this]
  have hge : (n : ℝ) ≤ ∑ v, (G34.dist s v : ℝ) := by
    rw [← hn]
    push_cast
    apply Finset.sum_le_sum
    intro v _
    have := dist_ge f hf s v
    rw [hs] at this
    exact_mod_cast (by omega : f v ≤ G34.dist s v)
  have hcard : T.card ≤ 38 := by
    have hsub2 : T ⊆ (({s} : Finset (Fin 39)) ×ˢ Finset.univ).erase (s, s) := by
      intro p hp
      rw [Finset.mem_erase]
      refine ⟨?_, hsub hp⟩
      rintro rfl
      rw [hT] at hp
      exact hp.2 (by simp)
    have := Finset.card_le_card hsub2
    rw [Finset.card_erase_of_mem (by simp), Finset.card_product, Finset.card_singleton,
      Finset.card_univ, Fintype.card_fin] at this
    omega
  have hcpos : 0 < T.card := by
    rw [Finset.card_pos]
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    have : (0 : ℝ) < n := by exact_mod_cast hpos
    linarith
  rw [hsum, div_le_div_iff₀ (by norm_num) (by exact_mod_cast hcpos)]
  have hc : (T.card : ℝ) ≤ 38 := by exact_mod_cast hcard
  have h0 : (0 : ℝ) ≤ n := by positivity
  calc (n : ℝ) * T.card ≤ n * 38 := mul_le_mul_of_nonneg_left hc h0
    _ ≤ _ := by linarith

lemma avg_ge (S : Set (Fin 39)) (s : Fin 39) (hS : S = {s}) {i1 : Fintype S}
    {i2 : DecidablePred (fun p : Fin 39 × Fin 39 => G34.dist p.1 p.2 ≠ 0)}
    (f : Fin 39 → ℕ) (hf : ∀ a b, G34.Adj a b → f b ≤ f a + 1)
    (hs : f s = 0) (n : ℕ) (hn : ∑ v, f v = n) (hpos : 0 < n) :
    (n : ℝ) / 38 ≤
      (∑ p ∈ @Finset.filter _ (fun p : Fin 39 × Fin 39 => G34.dist p.1 p.2 ≠ 0) i2
          (@Set.toFinset _ S i1 ×ˢ Finset.univ), (G34.dist p.1 p.2 : ℝ)) /
        ((@Finset.filter _ (fun p : Fin 39 × Fin 39 => G34.dist p.1 p.2 ≠ 0) i2
          (@Set.toFinset _ S i1 ×ˢ Finset.univ)).card : ℝ) := by
  subst hS
  refine avg_core s f hf hs n hn hpos _ ?_
  intro p
  rw [mem_filter_gen, Finset.mem_product, mem_toFinset_gen, Set.mem_singleton_iff]
  simp

/-! The path bound: no induced path on 12 vertices. -/
def ext12 (e : Fin 12 → Fin 39) (n : ℕ) : Fin 39 := if h : n < 12 then e ⟨n, h⟩ else 0

lemma ext12_lt (e : Fin 12 → Fin 39) (n : ℕ) (h : n < 12) : ext12 e n = e ⟨n, h⟩ := by
  unfold ext12
  rw [dif_pos h]

lemma no_long (g : ℕ → Fin 39) (gadj : ∀ n, n < 11 → G34.Adj (g n) (g (n + 1)))
    (ginj : ∀ n, n < 10 → g (n + 1 + 1) ≠ g n) : False := by
  have upD : ∀ n, (g n).val ≠ 0 → par (g n).val = (g (n + 1)).val →
      dep (g (n + 1)).val + 1 = dep (g n).val := by
    intro n h1 h2
    have := dep_par (g n) h1
    rw [h2] at this
    exact this
  have downD : ∀ n, (g (n + 1)).val ≠ 0 → par (g (n + 1)).val = (g n).val →
      dep (g n).val + 1 = dep (g (n + 1)).val := by
    intro n h1 h2
    have := dep_par (g (n + 1)) h1
    rw [h2] at this
    exact this
  have fwd : ∀ n, n < 10 → ((g (n + 1)).val ≠ 0 ∧ par (g (n + 1)).val = (g n).val) →
      ((g (n + 1 + 1)).val ≠ 0 ∧ par (g (n + 1 + 1)).val = (g (n + 1)).val) := by
    intro n hn hd
    rcases gadj (n + 1) (by omega) with hu | hd2
    · exfalso
      apply ginj n hn
      apply Fin.ext
      rw [← hu.2, hd.2]
    · exact hd2
  have back : ∀ n, n < 10 →
      ((g (n + 1)).val ≠ 0 ∧ par (g (n + 1)).val = (g (n + 1 + 1)).val) →
      ((g n).val ≠ 0 ∧ par (g n).val = (g (n + 1)).val) := by
    intro n hn hu
    rcases gadj n (by omega) with hu' | hd
    · exact hu'
    · exfalso
      have h1 := fwd n hn hd
      have a1 := upD (n + 1) hu.1 hu.2
      have a2 := downD (n + 1) h1.1 h1.2
      omega
  rcases gadj 5 (by norm_num) with hu5 | hd5
  · have hu4 := back 4 (by norm_num) hu5
    have hu3 := back 3 (by norm_num) hu4
    have hu2 := back 2 (by norm_num) hu3
    have hu1 := back 1 (by norm_num) hu2
    have hu0 := back 0 (by norm_num) hu1
    have e0 : dep (g 1).val + 1 = dep (g 0).val := upD 0 hu0.1 hu0.2
    have e1 : dep (g 2).val + 1 = dep (g 1).val := upD 1 hu1.1 hu1.2
    have e2 : dep (g 3).val + 1 = dep (g 2).val := upD 2 hu2.1 hu2.2
    have e3 : dep (g 4).val + 1 = dep (g 3).val := upD 3 hu3.1 hu3.2
    have e4 : dep (g 5).val + 1 = dep (g 4).val := upD 4 hu4.1 hu4.2
    have e5 : dep (g 6).val + 1 = dep (g 5).val := upD 5 hu5.1 hu5.2
    have := dep_le (g 0)
    omega
  · have hd6 := fwd 5 (by norm_num) hd5
    have hd7 := fwd 6 (by norm_num) hd6
    have hd8 := fwd 7 (by norm_num) hd7
    have hd9 := fwd 8 (by norm_num) hd8
    have hd10 := fwd 9 (by norm_num) hd9
    have e5 : dep (g 5).val + 1 = dep (g 6).val := downD 5 hd5.1 hd5.2
    have e6 : dep (g 6).val + 1 = dep (g 7).val := downD 6 hd6.1 hd6.2
    have e7 : dep (g 7).val + 1 = dep (g 8).val := downD 7 hd7.1 hd7.2
    have e8 : dep (g 8).val + 1 = dep (g 9).val := downD 8 hd8.1 hd8.2
    have e9 : dep (g 9).val + 1 = dep (g 10).val := downD 9 hd9.1 hd9.2
    have e10 : dep (g 10).val + 1 = dep (g 11).val := downD 10 hd10.1 hd10.2
    have := dep_le (g 11)
    omega

lemma path_le : path G34 ≤ 11 := by
  apply path_le_of_not_exists_inducedPath_succ G34 11
  rintro ⟨e, he, hadj⟩
  apply no_long (ext12 e)
  · intro n hn
    rw [ext12_lt e n (by omega), ext12_lt e (n + 1) (by omega)]
    exact (hadj _ _).2 (Or.inl rfl)
  · intro n hn h
    rw [ext12_lt e (n + 1 + 1) (by omega), ext12_lt e n (by omega)] at h
    have := congrArg Fin.val (he h)
    simp at this
    omega

/--
WOWII [Conjecture 34](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\operatorname{path}(G) \ge \lceil \operatorname{dist}\_{\operatorname{avg}}(C, V)
+ \operatorname{dist}\_{\operatorname{avg}}(M, V) \rceil$. The conjecture is false.
-/
theorem conjecture34 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      let C : Set α := center G
      let M : Set α := {v | G.degree v = G.maxDegree}
      let distAvg (S : Set α) : ℝ :=
        open scoped Classical in
        let pairs := (S.toFinset ×ˢ Finset.univ).filter (fun p => G.dist p.1 p.2 ≠ 0)
        (∑ p ∈ pairs, (G.dist p.1 p.2 : ℝ)) / pairs.card
      Int.ceil (distAvg C + distAvg M) ≤ (path G : ℤ) := by
  intro hall
  have key := hall (Fin 39) G34 conn
  dsimp only at key
  have hkey := Int.ceil_le.1 key
  have hp : ((path G34 : ℕ) : ℝ) ≤ 11 := by
    have := path_le
    exact_mod_cast this
  have h3 := le_trans (add_le_add
    (avg_ge (center G34) 0 center_eq fdep lip_dep (by decide) 154 sum_dep (by norm_num))
    (avg_ge _ 35 M_eq fhub lip_hub (by decide) 266 sum_hub (by norm_num))) hkey
  norm_num at h3
  linarith

#print axioms conjecture34

end WrittenOnTheWallII.GraphConjecture34
