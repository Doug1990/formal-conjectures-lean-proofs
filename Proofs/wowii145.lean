import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def largestInducedTreeSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, s.card = n ∧ (G.induce (s : Set α)).IsTree }

noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

noncomputable def maxEccentricityVertices (G : SimpleGraph α) : Set α :=
  {v : α | G.eccent v = G.ediam}

noncomputable def distToSet (G : SimpleGraph α) (v : α) (S : Set α) : ℕ :=
  open scoped Classical in
  if h : S.toFinset.Nonempty then
    (S.toFinset.image (fun s => G.dist v s)).min' (Finset.Nonempty.image h _)
  else 0

noncomputable def eccSet (G : SimpleGraph α) (S : Set α) : ℕ :=
  let dists := Finset.univ.image (fun v => distToSet G v S)
  if h : dists.Nonempty then dists.max' h else 0

omit [DecidableEq α] in
lemma card_le_largestInducedTreeSize {G : SimpleGraph α} {s : Finset α}
    (hs : (G.induce (s : Set α)).IsTree) :
    s.card ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    intro n hn
    obtain ⟨t, rfl, _⟩ := hn
    exact Finset.card_le_univ t
  · exact ⟨s, rfl, hs⟩

omit [Fintype α] in
lemma IsTree.induce_insert_of_unique_adj {G : SimpleGraph α} {s : Finset α} {z a : α}
    (hT : (G.induce (s : Set α)).IsTree)
    (_hz : z ∉ s) (ha : a ∈ s) (hza : G.Adj z a)
    (huniq : ∀ ⦃b : α⦄, b ∈ s → G.Adj z b → b = a) :
    (G.induce ((insert z s : Finset α) : Set α)).IsTree := by
  classical
  constructor
  · have hsconn : (G.induce (s : Set α)).Preconnected := hT.connected.preconnected
    have hzconn : (G.induce ({z} : Set α)).Preconnected := .of_subsingleton
    have hconn := connected_induce_union (v := z) (w := a) (s := ({z} : Set α))
      (t := (s : Set α)) hzconn hsconn (by simp) (by simpa using ha) hza
    rw [Finset.coe_insert]
    simpa only [Set.singleton_union] using hconn
  · intro v c hc
    let e : G.induce ((insert z s : Finset α) : Set α) ↪g G :=
      SimpleGraph.Embedding.induce _
    let q : G.Walk (e v) (e v) := c.map e.toHom
    have hq : q.IsCycle := by
      dsimp [q]
      exact (Walk.isCycle_map_iff_of_injective e.injective).2 hc
    have hq_mem (w : α) (hw : w ∈ q.support) : w ∈ insert z s := by
      dsimp [q] at hw
      rw [Walk.support_map] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      change (w' : α) ∈ insert z s
      exact w'.property
    by_cases hzq : z ∈ q.support
    · let r : G.Walk z z := q.rotate z hzq
      have hr : r.IsCycle := by
        dsimp [r]
        exact hq.rotate hzq
      have hrsnd : r.snd ∈ q.support := by
        apply (q.mem_support_rotate_iff z hzq).mp
        simpa only [r] using r.getVert_mem_support 1
      have hrpenultimate : r.penultimate ∈ q.support := by
        apply (q.mem_support_rotate_iff z hzq).mp
        simpa only [r] using r.getVert_mem_support (r.length - 1)
      have hadj_snd : G.Adj z r.snd := r.adj_snd hr.not_nil
      have hadj_penultimate : G.Adj z r.penultimate :=
        (r.adj_penultimate hr.not_nil).symm
      have hsnd : r.snd ∈ s := by
        rcases Finset.mem_insert.mp (hq_mem _ hrsnd) with heq | hmem
        · exact (hadj_snd.ne heq.symm).elim
        · exact hmem
      have hpenultimate : r.penultimate ∈ s := by
        rcases Finset.mem_insert.mp (hq_mem _ hrpenultimate) with heq | hmem
        · exact (hadj_penultimate.ne heq.symm).elim
        · exact hmem
      exact hr.snd_ne_penultimate <|
        (huniq hsnd hadj_snd).trans (huniq hpenultimate hadj_penultimate).symm
    · have hqs : ∀ w ∈ q.support, w ∈ (s : Set α) := by
        intro w hw
        rcases Finset.mem_insert.mp (hq_mem w hw) with heq | hmem
        · subst w
          exact (hzq hw).elim
        · simpa using hmem
      let qi := q.induce (s : Set α) hqs
      have hqi : qi.IsCycle := by
        apply (Walk.isCycle_map_iff_of_injective
          (f := (SimpleGraph.Embedding.induce (G := G) (s : Set α)).toHom)
          (SimpleGraph.Embedding.induce (G := G) (s : Set α)).injective).mp
        rw [show qi.map (SimpleGraph.Embedding.induce (G := G) (s : Set α)).toHom = q by
          dsimp [qi]
          exact Walk.map_induce q hqs]
        exact hq
      exact hT.isAcyclic qi hqi

omit [Fintype α] in
lemma Walk.induce_support_isTree_of_length_eq_dist {G : SimpleGraph α} {u v : α}
    (p : G.Walk u v) (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by
  induction p with
  | @nil u =>
      have hset : (↑(Walk.nil : G.Walk u u).support.toFinset : Set α) = {u} := by
        ext
        simp
      have hsingle : (G.induce ({u} : Set α)).IsTree := by
        let : Nonempty ↥({u} : Set α) := ⟨⟨u, by simp⟩⟩
        let : Subsingleton ↥({u} : Set α) := ⟨fun a b => by
          apply Subtype.ext
          have ha : (a : α) = u := by
            simpa only [Set.mem_singleton_iff] using a.property
          have hb : (b : α) = u := by
            simpa only [Set.mem_singleton_iff] using b.property
          exact ha.trans hb.symm⟩
        exact IsTree.of_subsingleton
      rw [hset]
      exact hsingle
  | @cons u v w huv p ih =>
      have hptail : p.length = G.dist v w :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p huv)
      have hT := ih hptail
      have hpath : (p.cons huv).IsPath :=
        (p.cons huv).isPath_of_length_eq_dist hp
      have hu_not : u ∉ p.support.toFinset := by
        simpa using (List.nodup_cons.mp hpath.support_nodup).1
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj u b → b = v := by
        intro b hb hub
        have hbmem : b ∈ p.support := by simpa using hb
        obtain ⟨i, hi, hib⟩ := List.mem_iff_getElem.mp hbmem
        have hget : p.getVert i = b := by
          rw [← p.support_getElem_eq_getVert hi, hib]
        have hi_le : i ≤ p.length := by
          have hlen := p.length_support
          omega
        have hub' : G.Adj u (p.getVert i) := by simpa [hget] using hub
        let r : G.Walk u w := (p.drop i).cons hub'
        have hdistle : G.dist u w ≤ r.length := G.dist_le r
        have hlen : (p.cons huv).length ≤ r.length := by simpa [hp] using hdistle
        have hi0 : i = 0 := by
          simp only [Walk.length_cons, r, Walk.drop_length] at hlen
          omega
        subst i
        simpa using hget.symm
      have hsupp : (Walk.cons huv p).support.toFinset = insert u p.support.toFinset := by
        simp
      rw [hsupp]
      exact hT.induce_insert_of_unique_adj hu_not (by simp) huv huniq

end SimpleGraph

namespace W145

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

omit [Fintype α] in
lemma single_tree (x : α) : (G.induce (({x} : Finset α) : Set α)).IsTree := by
  have hs : ((({x} : Finset α)) : Set α) = {x} := by simp
  rw [hs]
  let : Nonempty ↥({x} : Set α) := ⟨⟨x, by simp⟩⟩
  let : Subsingleton ↥({x} : Set α) := ⟨fun a b => by
    apply Subtype.ext
    have ha : (a : α) = x := Set.mem_singleton_iff.mp a.property
    have hb : (b : α) = x := Set.mem_singleton_iff.mp b.property
    exact ha.trans hb.symm⟩
  exact IsTree.of_subsingleton

omit [Fintype α] in
lemma ins {s : Finset α} {z a : α} (hT : (G.induce (s : Set α)).IsTree) (hz : z ∉ s)
    (ha : a ∈ s) (hza : G.Adj z a) (hu : ∀ ⦃b : α⦄, b ∈ s → G.Adj z b → b = a) :
    (G.induce ((insert z s : Finset α) : Set α)).IsTree ∧ (insert z s).card = s.card + 1 :=
  ⟨hT.induce_insert_of_unique_adj hz ha hza hu, Finset.card_insert_of_notMem hz⟩

omit [Fintype α] [DecidableEq α] in
lemma L1 (hc : G.Connected) (c : α) {p q : α} (h : G.Adj p q) :
    G.dist c q ≤ G.dist c p + 1 := by
  calc G.dist c q ≤ G.dist c p + G.dist p q := hc.dist_triangle
    _ = G.dist c p + 1 := by rw [dist_eq_one_iff_adj.2 h]

omit [Fintype α] [DecidableEq α] in
lemma L4 (hc : G.Connected) (a b : α) {p q : α} (h : G.Adj p q) :
    G.dist a q ≤ G.dist a p + 1 ∧ G.dist a p ≤ G.dist a q + 1 ∧
    G.dist b q ≤ G.dist b p + 1 ∧ G.dist b p ≤ G.dist b q + 1 :=
  ⟨L1 hc a h, L1 hc a h.symm, L1 hc b h, L1 hc b h.symm⟩

lemma tree_ge (hc : G.Connected) (x y : α) : G.dist x y + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, hp, hl⟩ := hc.exists_path_of_dist x y
  have := card_le_largestInducedTreeSize (p.induce_support_isTree_of_length_eq_dist hl)
  rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support, hl] at this
  exact this

lemma sixA (hc : G.Connected) {a b u n1 m n3 : α}
    (hab : G.dist a b = 4) (hau : G.dist a u = 3) (hbu : G.dist b u = 3)
    (e1 : G.Adj a n1) (e2 : G.Adj n1 m) (e3 : G.Adj m n3) (e4 : G.Adj n3 b)
    (e5 : G.Adj u m) : 6 ≤ largestInducedTreeSize G := by
  have hba : G.dist b a = 4 := by rw [dist_comm]; exact hab
  have haa : G.dist a a = 0 := dist_self
  have hbb : G.dist b b = 0 := dist_self
  obtain ⟨p1, p2, p3, p4⟩ := L4 hc a b e1
  obtain ⟨q1, q2, q3, q4⟩ := L4 hc a b e2
  obtain ⟨r1, r2, r3, r4⟩ := L4 hc a b e3
  obtain ⟨s1, s2, s3, s4⟩ := L4 hc a b e4
  obtain ⟨w1, w2, w3, w4⟩ := L4 hc a b e5
  have t0 := single_tree (G := G) m
  obtain ⟨t1, c1⟩ := ins t0
    (by simp only [Finset.mem_singleton]; intro h; subst h; omega) (by simp) e2
    (by intro z hz _; simpa only [Finset.mem_singleton] using hz)
  obtain ⟨t2, c2⟩ := ins t1
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e1
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h
      all_goals first
        | exact h
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  obtain ⟨t3, c3⟩ := ins t2
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e3.symm
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h
      all_goals first
        | exact h
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  obtain ⟨t4, c4⟩ := ins t3
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e4.symm
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h
      all_goals first
        | exact h
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  obtain ⟨t5, c5⟩ := ins t4
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e5
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h | h
      all_goals first
        | exact h
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  have := card_le_largestInducedTreeSize t5
  have := Finset.card_singleton m
  omega

lemma sixB4 (hc : G.Connected) {a b u n1 m1 n3 m2 : α}
    (hab : G.dist a b = 4) (hau : G.dist a u = 3) (hbu : G.dist b u = 3)
    (e1 : G.Adj a n1) (e2 : G.Adj n1 m1) (e3 : G.Adj m1 u) (e4 : G.Adj u m2)
    (e5 : G.Adj m2 n3) (e6 : G.Adj n3 b) (h7 : G.Adj m1 m2)
    (hn1 : ¬ G.Adj m1 n3) (hn2 : ¬ G.Adj m2 n1) (hne : m1 ≠ m2) :
    6 ≤ largestInducedTreeSize G := by
  have hba : G.dist b a = 4 := by rw [dist_comm]; exact hab
  have haa : G.dist a a = 0 := dist_self
  have hbb : G.dist b b = 0 := dist_self
  obtain ⟨p1, p2, p3, p4⟩ := L4 hc a b e1
  obtain ⟨q1, q2, q3, q4⟩ := L4 hc a b e2
  obtain ⟨r1, r2, r3, r4⟩ := L4 hc a b e3
  obtain ⟨s1, s2, s3, s4⟩ := L4 hc a b e4
  obtain ⟨w1, w2, w3, w4⟩ := L4 hc a b e5
  obtain ⟨y1, y2, y3, y4⟩ := L4 hc a b e6
  have t0 := single_tree (G := G) m1
  obtain ⟨t1, c1⟩ := ins t0
    (by simp only [Finset.mem_singleton]; intro h; subst h; omega) (by simp) e2
    (by intro z hz _; simpa only [Finset.mem_singleton] using hz)
  obtain ⟨t2, c2⟩ := ins t1
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e1
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h
      all_goals first
        | exact h
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  obtain ⟨t3, c3⟩ := ins t2
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; first | exact hne h | exact hne h.symm | (subst h; omega)))
    (by simp) h7.symm
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h
      all_goals first
        | exact h
        | (subst z; exact absurd hz' hn2)
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  obtain ⟨t4, c4⟩ := ins t3
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e5.symm
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h
      all_goals first
        | exact h
        | (subst z; exact absurd hz'.symm hn1)
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  obtain ⟨t5, c5⟩ := ins t4
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e6.symm
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h | h
      all_goals first
        | exact h
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  have := card_le_largestInducedTreeSize t5
  have := Finset.card_singleton m1
  omega

lemma sixB5 (hc : G.Connected) {a b u n1 m1 n3 m2 : α}
    (hab : G.dist a b = 4) (hau : G.dist a u = 3) (hbu : G.dist b u = 3)
    (e1 : G.Adj a n1) (e2 : G.Adj n1 m1) (e3 : G.Adj m1 u) (e4 : G.Adj u m2)
    (e5 : G.Adj m2 n3) (e6 : G.Adj n3 b) (hm : ¬ G.Adj m1 m2)
    (hn1 : ¬ G.Adj m1 n3) (hn2 : ¬ G.Adj m2 n1) (hne : m1 ≠ m2) :
    6 ≤ largestInducedTreeSize G := by
  have hba : G.dist b a = 4 := by rw [dist_comm]; exact hab
  have haa : G.dist a a = 0 := dist_self
  have hbb : G.dist b b = 0 := dist_self
  obtain ⟨p1, p2, p3, p4⟩ := L4 hc a b e1
  obtain ⟨q1, q2, q3, q4⟩ := L4 hc a b e2
  obtain ⟨r1, r2, r3, r4⟩ := L4 hc a b e3
  obtain ⟨s1, s2, s3, s4⟩ := L4 hc a b e4
  obtain ⟨w1, w2, w3, w4⟩ := L4 hc a b e5
  obtain ⟨y1, y2, y3, y4⟩ := L4 hc a b e6
  have t0 := single_tree (G := G) u
  obtain ⟨t1, c1⟩ := ins t0
    (by simp only [Finset.mem_singleton]; intro h; subst h; omega) (by simp) e3
    (by intro z hz _; simpa only [Finset.mem_singleton] using hz)
  obtain ⟨t2, c2⟩ := ins t1
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e2
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h
      all_goals first
        | exact h
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  obtain ⟨t3, c3⟩ := ins t2
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e1
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h
      all_goals first
        | exact h
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  obtain ⟨t4, c4⟩ := ins t3
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; first | exact hne h | exact hne h.symm | (subst h; omega)))
    (by simp) e4.symm
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h
      all_goals first
        | exact h
        | (subst z; exact absurd hz' hn2)
        | (subst z; exact absurd hz'.symm hm)
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  obtain ⟨t5, c5⟩ := ins t4
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e5.symm
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h | h
      all_goals first
        | exact h
        | (subst z; exact absurd hz'.symm hn1)
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  obtain ⟨t6, c6⟩ := ins t5
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      repeat' constructor
      all_goals (intro h; subst h; omega))
    (by simp) e6.symm
    (by
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h | h | h
      all_goals first
        | exact h
        | (exfalso; subst z; obtain ⟨x1, x2, x3, x4⟩ := L4 hc a b hz'; omega))
  have := card_le_largestInducedTreeSize t6
  have := Finset.card_singleton u
  omega

omit [Fintype α] [DecidableEq α] in
lemma geo3 (hc : G.Connected) {u a : α} (h : G.dist u a = 3) :
    ∃ m n, G.Adj u m ∧ G.Adj m n ∧ G.Adj n a := by
  obtain ⟨p, -, hp⟩ := hc.exists_path_of_dist u a
  have h3 : p.length = 3 := hp.trans h
  refine ⟨p.getVert 1, p.getVert 2, ?_, ?_, ?_⟩
  · have := p.adj_getVert_succ (i := 0) (by omega)
    rwa [Walk.getVert_zero] at this
  · exact p.adj_getVert_succ (i := 1) (by omega)
  · have := p.adj_getVert_succ (i := 2) (by omega)
    have e : p.getVert (2 + 1) = a := by
      rw [show 2 + 1 = p.length by omega]; exact p.getVert_length
    rwa [e] at this

lemma six (hc : G.Connected) {a b u : α}
    (hab : G.dist a b = 4) (hau : G.dist a u = 3) (hbu : G.dist b u = 3) :
    6 ≤ largestInducedTreeSize G := by
  obtain ⟨m1, n1, f1, f2, f3⟩ := geo3 hc (by rw [dist_comm]; exact hau)
  obtain ⟨m2, n3, g1, g2, g3⟩ := geo3 hc (by rw [dist_comm]; exact hbu)
  by_cases c1 : G.Adj m1 n3
  · exact sixA hc hab hau hbu f3.symm f2.symm c1 g3 f1
  by_cases c2 : G.Adj m2 n1
  · exact sixA hc hab hau hbu f3.symm c2.symm g2 g3 g1
  by_cases c3 : m1 = m2
  · subst c3; exact absurd g2 c1
  by_cases c4 : G.Adj m1 m2
  · exact sixB4 hc hab hau hbu f3.symm f2.symm f1.symm g1 g2 g3 c4 c1 c2 c3
  · exact sixB5 hc hab hau hbu f3.symm f2.symm f1.symm g1 g2 g3 c4 c1 c2 c3

lemma eccSet_le {S : Set α} {k : ℕ} (hk : ∀ v, ∃ s ∈ S, G.dist v s ≤ k) :
    eccSet G S ≤ k := by
  dsimp only [eccSet]
  split_ifs with hd
  · apply Finset.max'_le
    intro d hd'
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hd'
    obtain ⟨s, hs, hvs⟩ := hk v
    dsimp only [distToSet]
    split_ifs with hS
    · exact (Finset.min'_le _ _ (Finset.mem_image.2 ⟨s, (by simpa using hs), rfl⟩)).trans hvs
    · exact Nat.zero_le _
  · exact Nat.zero_le _

end W145

namespace WrittenOnTheWallII.GraphConjecture145

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

noncomputable def localIndependenceMin (G : SimpleGraph α) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (indepNeighborsCard G)

theorem conjecture145 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hlMin : 0 < localIndependenceMin Gᶜ) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * localIndependenceMin Gᶜ := by
  set T := largestInducedTreeSize G with hT
  set L := localIndependenceMin Gᶜ with hL
  have hne : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.1 h
  obtain ⟨x, y, hxy⟩ := G.exists_dist_eq_diam
  set D := G.diam with hD
  have hed : G.ediam = (D : ℕ∞) := (ENat.natCast_toNat hne).symm
  have hedist : ∀ p q, G.edist p q = (G.dist p q : ℕ∞) :=
    fun p q => (h.preconnected p q).coe_dist_eq_edist.symm
  have memB : ∀ p q, G.dist p q = D → p ∈ maxEccentricityVertices G := by
    intro p q hpq
    show G.eccent p = G.ediam
    apply le_antisymm eccent_le_ediam
    calc G.ediam = (D : ℕ∞) := hed
      _ = G.edist p q := by rw [hedist, hpq]
      _ ≤ G.eccent p := edist_le_eccent
  have hxB := memB x y hxy
  have hyB := memB y x (by rw [dist_comm]; exact hxy)
  have hTD : D + 1 ≤ T := by
    have := W145.tree_ge h x y
    rw [hxy] at this
    exact this
  have hlt : ∀ u, u ∉ maxEccentricityVertices G → ∀ q, G.dist u q < D := by
    intro u hu q
    have h1 : G.eccent u < G.ediam := lt_of_le_of_ne eccent_le_ediam hu
    have h2 : (G.dist u q : ℕ∞) < (D : ℕ∞) := by
      rw [← hedist, ← hed]; exact lt_of_le_of_lt edist_le_eccent h1
    exact_mod_cast h2
  have key : ∀ u, ∃ b ∈ maxEccentricityVertices G, 2 * G.dist u b ≤ T * L := by
    intro u
    by_cases hu : u ∈ maxEccentricityVertices G
    · exact ⟨u, hu, by simp⟩
    have dx := hlt u hu x
    have dy := hlt u hu y
    by_cases hL2 : 2 ≤ L
    · refine ⟨x, hxB, ?_⟩
      have : T * 2 ≤ T * L := Nat.mul_le_mul_left T hL2
      omega
    have hL1 : L = 1 := by omega
    rw [hL1, mul_one]
    obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (indepNeighborsCard Gᶜ)
    have hv1 : (Gᶜ.induce (Gᶜ.neighborSet v)).indepNum ≤ 1 := by
      have e : localIndependenceMin Gᶜ = indepNeighborsCard Gᶜ v := hv
      have : indepNeighborsCard Gᶜ v ≤ 1 := by rw [← e, ← hL, hL1]
      exact this
    have hrad : ∀ c, G.dist v c ≤ 2 := by
      intro c
      by_cases hcv : c = v
      · subst hcv; simp
      by_cases hadj : G.Adj v c
      · rw [dist_eq_one_iff_adj.2 hadj]; omega
      obtain ⟨z, hz⟩ := exists_ne c
      obtain ⟨w, hcw⟩ : ∃ w, G.Adj c w := by
        obtain ⟨p⟩ := h.preconnected c z
        cases p with
        | nil => exact absurd rfl hz
        | cons hh _ => exact ⟨_, hh⟩
      by_cases hvw : G.Adj v w
      · calc G.dist v c ≤ G.dist v w + G.dist w c := h.dist_triangle
          _ ≤ 2 := by rw [dist_eq_one_iff_adj.2 hvw, dist_eq_one_iff_adj.2 hcw.symm]
      · exfalso
        have hwv : w ≠ v := by
          intro e; subst e; exact hadj hcw.symm
        have hcN : c ∈ Gᶜ.neighborSet v := by
          rw [mem_neighborSet, compl_adj]; exact ⟨Ne.symm hcv, hadj⟩
        have hwN : w ∈ Gᶜ.neighborSet v := by
          rw [mem_neighborSet, compl_adj]; exact ⟨Ne.symm hwv, hvw⟩
        have hcw' : c ≠ w := G.ne_of_adj hcw
        let Q : Finset (Gᶜ.neighborSet v) := {⟨c, hcN⟩, ⟨w, hwN⟩}
        have hQ : (Gᶜ.induce (Gᶜ.neighborSet v)).IsIndepSet (Q : Set _) := by
          intro p hp q hq hpq hadj'
          have hadj'' : Gᶜ.Adj p.1 q.1 := hadj'
          rw [compl_adj] at hadj''
          simp only [Q, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hp hq
          rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
          · exact hpq rfl
          · exact hadj''.2 hcw
          · exact hadj''.2 hcw.symm
          · exact hpq rfl
        have hcard : Q.card = 2 := by
          rw [Finset.card_pair]; intro e; exact hcw' (congrArg Subtype.val e)
        have := hQ.card_le_indepNum
        omega
    have hD4 : D ≤ 4 := by
      have := h.dist_triangle (u := x) (v := v) (w := y)
      have h1 := hrad x
      have h2 := hrad y
      rw [dist_comm] at h1
      omega
    by_cases hD3 : D ≤ 3
    · exact ⟨x, hxB, by omega⟩
    by_cases hx2 : G.dist u x ≤ 2
    · exact ⟨x, hxB, by omega⟩
    by_cases hy2 : G.dist u y ≤ 2
    · exact ⟨y, hyB, by omega⟩
    have h6 : 6 ≤ T := W145.six h (a := x) (b := y) (u := u) (by omega)
      (by rw [dist_comm]; omega) (by rw [dist_comm]; omega)
    exact ⟨x, hxB, by omega⟩
  have := W145.eccSet_le (G := G) (S := maxEccentricityVertices G) (k := T * L / 2)
    (fun u => by obtain ⟨b, hb, hb2⟩ := key u; exact ⟨b, hb, by omega⟩)
  omega

end WrittenOnTheWallII.GraphConjecture145

#print axioms WrittenOnTheWallII.GraphConjecture145.conjecture145
