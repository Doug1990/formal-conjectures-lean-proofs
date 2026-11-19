import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! WOWII 430a. Definitions restated from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean. -/

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α} [Fintype α] [DecidableEq α]

def IsDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

structure IsNIndepDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isIndep : G.IsIndepSet D
  isDominating : G.IsDominating D
  card_eq : D.card = n

noncomputable def indepDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsNIndepDominatingSet n D}

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture430a

open SimpleGraph

/-- The center of a finite graph. -/
noncomputable def centerFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.eccent v = G.radius

/-- DeLaViña's `N(S)`: the union of open vertex neighborhoods. This may
intersect `S`. -/
def setNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  Finset.univ.filter fun v => ∃ u ∈ S, G.Adj u v

/-- The exact rational Caro--Wei sum. -/
def caroWei {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  ∑ v : V, 1 / ((G.degree v + 1 : ℕ) : ℚ)

/-! The clique blow-up of `P₇` with blob orders (1,4,12,19,12,4,1) on `Fin 53`. -/
def bl (i : ℕ) : ℕ :=
  if i < 1 then 0 else if i < 5 then 1 else if i < 17 then 2 else if i < 36 then 3
  else if i < 48 then 4 else if i < 52 then 5 else 6

def G53 : SimpleGraph (Fin 53) where
  Adj a b := a ≠ b ∧ bl a.val ≤ bl b.val + 1 ∧ bl b.val ≤ bl a.val + 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel G53.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ bl a.val ≤ bl b.val + 1 ∧ bl b.val ≤ bl a.val + 1))

def repF (k : ℕ) : Fin 53 :=
  if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 5 else if k = 3 then 17
  else if k = 4 then 36 else if k = 5 then 48 else 52

def q17 (v : Fin 53) : Fin 53 :=
  if bl v.val < 3 then repF (bl v.val + 1) else if 3 < bl v.val then repF (bl v.val - 1) else 17

def h17 (v : Fin 53) : ℕ :=
  if v = 17 then 0 else if bl v.val < 3 then 3 - bl v.val
  else if 3 < bl v.val then bl v.val - 3 else 1

lemma hq17 : ∀ v, v ≠ 17 → G53.Adj v (q17 v) ∧ h17 (q17 v) + 1 = h17 v := by decide
lemma h17_0 : ∀ v, h17 v = 0 → v = 17 := by decide
lemma h17_le : ∀ v, h17 v ≤ 3 := by decide

lemma walkTo (t : Fin 53) (q : Fin 53 → Fin 53) (h : Fin 53 → ℕ)
    (hq : ∀ v, v ≠ t → G53.Adj v (q v) ∧ h (q v) + 1 = h v) (h0 : ∀ v, h v = 0 → v = t)
    (ht : h t = 0) :
    ∀ n v, h v = n → ∃ p : G53.Walk v t, p.length = n := by
  intro n
  induction n with
  | zero =>
    intro v hv
    have := h0 v hv
    subst this
    exact ⟨Walk.nil, rfl⟩
  | succ n ih =>
    intro v hv
    have hvt : v ≠ t := by
      rintro rfl
      omega
    obtain ⟨hadj, hh⟩ := hq v hvt
    obtain ⟨p, hp⟩ := ih (q v) (by omega)
    exact ⟨Walk.cons hadj p, by simp [hp]⟩

lemma walk17 (v : Fin 53) : ∃ p : G53.Walk v 17, p.length = h17 v :=
  walkTo 17 q17 h17 hq17 h17_0 (by decide) _ v rfl

lemma conn : G53.Connected := by
  have reach : ∀ u : Fin 53, G53.Reachable u 17 := by
    intro u
    obtain ⟨p, _⟩ := walk17 u
    exact ⟨p⟩
  exact Connected.mk (fun u v => (reach u).trans (reach v).symm)

lemma pot (f : Fin 53 → ℕ) (hf : ∀ a b, G53.Adj a b → f b ≤ f a + 1) {u v : Fin 53}
    (p : G53.Walk u v) : f v ≤ f u + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have := hf _ _ h
    simp only [Walk.length_cons]
    omega

lemma dist_ge (f : Fin 53 → ℕ) (hf : ∀ a b, G53.Adj a b → f b ≤ f a + 1) (u v : Fin 53) :
    f v ≤ f u + G53.dist u v := by
  obtain ⟨p, hp⟩ := conn.exists_walk_length_eq_dist u v
  rw [← hp]
  exact pot f hf p

def fb (v : Fin 53) : ℕ := bl v.val
def fb' (v : Fin 53) : ℕ := 6 - bl v.val

lemma lip_b : ∀ a b, G53.Adj a b → fb b ≤ fb a + 1 := by decide
lemma lip_b' : ∀ a b, G53.Adj a b → fb' b ≤ fb' a + 1 := by decide

lemma ecc17 : G53.eccent 17 ≤ ((3 : ℕ) : ℕ∞) := by
  rw [eccent_le_iff]
  intro v
  obtain ⟨p, hp⟩ := walk17 v
  calc G53.edist 17 v ≤ p.reverse.length := edist_le p.reverse
    _ ≤ ((3 : ℕ) : ℕ∞) := by
      rw [Walk.length_reverse, hp]
      exact_mod_cast h17_le v

lemma ecc_big (v : Fin 53) (hv : bl v.val ≠ 3) : ((4 : ℕ) : ℕ∞) ≤ G53.eccent v := by
  have key : ∀ w : Fin 53, 4 ≤ G53.dist v w → ((4 : ℕ) : ℕ∞) ≤ G53.eccent v := by
    intro w hw
    have h4 : (G53.dist v w : ℕ∞) ≤ G53.eccent v := by
      rw [(conn.preconnected v w).coe_dist_eq_edist]
      exact edist_le_eccent
    exact (Nat.cast_le.2 hw).trans h4
  have e1 : fb v = bl v.val := rfl
  have e2 : fb' v = 6 - bl v.val := rfl
  by_cases hc : bl v.val ≤ 2
  · apply key 52
    have h1 := dist_ge fb lip_b v 52
    have h2 : fb 52 = 6 := by decide
    omega
  · apply key 0
    have h1 := dist_ge fb' lip_b' v 0
    have h2 : fb' 0 = 6 := by decide
    omega

lemma mem_filter_gen {β : Type*} (p : β → Prop) (i : DecidablePred p) (s : Finset β) (a : β) :
    a ∈ @Finset.filter β p i s ↔ a ∈ s ∧ p a := Finset.mem_filter

lemma cen (v : Fin 53) (hv : v ∈ centerFinset G53) : bl v.val = 3 := by
  unfold centerFinset at hv
  have h1 := ((mem_filter_gen _ _ _ _).1 hv).2
  by_contra hne
  have h3 := ecc_big v hne
  have h2 : G53.radius ≤ ((3 : ℕ) : ℕ∞) := radius_le_eccent.trans ecc17
  rw [← h1] at h2
  have := Nat.cast_le.1 (h3.trans h2)
  omega

lemma nbhd (v : Fin 53) (hv : v ∈ setNeighborhood G53 (centerFinset G53)) :
    2 ≤ bl v.val ∧ bl v.val ≤ 4 := by
  unfold setNeighborhood at hv
  obtain ⟨-, u, hu, hadj⟩ := (mem_filter_gen _ _ _ _).1 hv
  have := cen u hu
  obtain ⟨_, h1, h2⟩ := hadj
  omega

lemma indepNum_induce_le {W : Type*} [Fintype W] (H : SimpleGraph W) (S : Set W) (k : ℕ)
    (h : ∀ t : Finset W, (↑t ⊆ S) → H.IsIndepSet (t : Set W) → t.card ≤ k) :
    (H.induce S).indepNum ≤ k := by
  obtain ⟨s, hs⟩ := (H.induce S).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  apply h
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun e => hxy (by rw [e])
    exact hs.isIndepSet (Finset.mem_coe.2 hx') (Finset.mem_coe.2 hy') hne

lemma gap (x y : Fin 53) (hxy : x ≠ y) (hn : ¬ G53.Adj x y) :
    bl x.val + 2 ≤ bl y.val ∨ bl y.val + 2 ≤ bl x.val := by
  by_contra h
  apply hn
  exact ⟨hxy, by omega, by omega⟩

lemma alpha_le :
    (G53.induce (setNeighborhood G53 (centerFinset G53) : Set (Fin 53))).indepNum ≤ 2 := by
  apply indepNum_induce_le
  intro t hsub hind
  by_contra hc
  have hc' : 2 < t.card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hc'
  have na := nbhd a (Finset.mem_coe.1 (hsub (Finset.mem_coe.2 ha)))
  have nb := nbhd b (Finset.mem_coe.1 (hsub (Finset.mem_coe.2 hb)))
  have nc := nbhd c (Finset.mem_coe.1 (hsub (Finset.mem_coe.2 hc)))
  have g1 := gap a b hab (hind (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hab)
  have g2 := gap a c hac (hind (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hc) hac)
  have g3 := gap b c hbc (hind (Finset.mem_coe.2 hb) (Finset.mem_coe.2 hc) hbc)
  omega

lemma dom_at (D : Finset (Fin 53)) (hdom : G53.IsDominating (D : Set (Fin 53))) (v : Fin 53) :
    ∃ x ∈ D, bl x.val ≤ bl v.val + 1 ∧ bl v.val ≤ bl x.val + 1 := by
  rcases hdom v with h | ⟨w, hw, hadj⟩
  · exact ⟨v, Finset.mem_coe.1 h, by omega, by omega⟩
  · exact ⟨w, Finset.mem_coe.1 hw, hadj.2.2, hadj.2.1⟩

def wit (v : Fin 53) : Fin 53 :=
  if bl v.val ≤ 1 then 0 else if bl v.val ≤ 4 then 17 else 52

lemma idom : 3 ≤ G53.indepDominationNumber := by
  unfold indepDominationNumber
  have k1 : ∀ x y : Fin 53, x ∈ ({0, 17, 52} : Finset (Fin 53)) →
      y ∈ ({0, 17, 52} : Finset (Fin 53)) → x ≠ y → ¬ G53.Adj x y := by decide
  have k2' : ∀ v : Fin 53, v = wit v ∨ G53.Adj v (wit v) := by decide
  have k3 : ∀ v : Fin 53, wit v ∈ ({0, 17, 52} : Finset (Fin 53)) := by
    intro v
    unfold wit
    split_ifs <;> simp
  have k2 : ∀ v : Fin 53, v ∈ ({0, 17, 52} : Finset (Fin 53)) ∨
      ∃ w ∈ ({0, 17, 52} : Finset (Fin 53)), G53.Adj v w := by
    intro v
    rcases k2' v with h | h
    · left
      rw [h]
      exact k3 v
    · exact Or.inr ⟨wit v, k3 v, h⟩
  have hD0 : G53.IsNIndepDominatingSet 3 ({0, 17, 52} : Finset (Fin 53)) := by
    refine ⟨?_, ?_, by decide⟩
    · intro x hx y hy hxy
      exact k1 x y (Finset.mem_coe.1 hx) (Finset.mem_coe.1 hy) hxy
    · intro v
      rcases k2 v with h | ⟨w, hw, h⟩
      · exact Or.inl (Finset.mem_coe.2 h)
      · exact Or.inr ⟨w, Finset.mem_coe.2 hw, h⟩
  have hne : ({n | ∃ D : Finset (Fin 53), G53.IsNIndepDominatingSet n D} : Set ℕ).Nonempty :=
    ⟨3, _, hD0⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  rw [← hD.card_eq]
  obtain ⟨x, hx, x1, x2⟩ := dom_at D hD.isDominating 0
  obtain ⟨y, hy, y1, y2⟩ := dom_at D hD.isDominating 17
  obtain ⟨z, hz, z1, z2⟩ := dom_at D hD.isDominating 52
  have b0 : bl (0 : Fin 53).val = 0 := by decide
  have b17 : bl (17 : Fin 53).val = 3 := by decide
  have b52 : bl (52 : Fin 53).val = 6 := by decide
  have hxy : x ≠ y := by
    rintro rfl
    omega
  have hxz : x ≠ z := by
    rintro rfl
    omega
  have hyz : y ≠ z := by
    rintro rfl
    omega
  have := Finset.two_lt_card_iff.2 ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
  omega

def dd (k : ℕ) : ℕ :=
  if k = 0 then 5 else if k = 1 then 17 else if k = 2 then 35 else if k = 3 then 43
  else if k = 4 then 35 else if k = 5 then 17 else 5

def nn (k : ℕ) : ℕ :=
  if k = 0 then 5117 else if k = 1 then 1505 else if k = 2 then 731 else if k = 3 then 595
  else if k = 4 then 731 else if k = 5 then 1505 else 5117

lemma cw : caroWei G53 < 2 := by
  have hd : ∀ v : Fin 53, G53.degree v + 1 = dd (bl v.val) := by
    intro v
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    revert v
    decide
  have ddne : ∀ v : Fin 53, dd (bl v.val) ≠ 0 := by decide
  have key1 : ∀ v : Fin 53, nn (bl v.val) * dd (bl v.val) = 25585 := by decide
  have hs : ∑ v : Fin 53, nn (bl v.val) = 51123 := by decide
  have hg : ∀ v : Fin 53, (1 : ℚ) / ((dd (bl v.val) : ℕ) : ℚ) =
      ((nn (bl v.val) : ℕ) : ℚ) * (1 / 25585) := by
    intro v
    have h2 : ((dd (bl v.val) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast ddne v
    have h1 := key1 v
    rw [← div_eq_mul_one_div, div_eq_div_iff h2 (by norm_num)]
    exact_mod_cast (show 1 * 25585 = nn (bl v.val) * dd (bl v.val) by rw [one_mul, h1])
  unfold caroWei
  simp only [hd, hg]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hs]
  norm_num

/--
WOWII Conjecture 430a asked whether every connected graph `G` of order
greater than three satisfies
`i(G) ≤ α(G[N(C)]) + 2 floor(CW(G)-1)`.
The answer is no, witnessed by a nonuniform `P₇` clique blow-up.
-/
theorem conjecture430a :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 3 < Fintype.card V →
        (G.indepDominationNumber : ℤ) ≤
          ((G.induce
            (setNeighborhood G (centerFinset G) : Set V)).indepNum : ℤ) +
            2 * ⌊caroWei G - 1⌋ := by
  intro hall
  have key := hall (Fin 53) G53 conn (by simp)
  have h1 := idom
  have h2 := alpha_le
  have h3 : ⌊caroWei G53 - 1⌋ < 1 := Int.floor_lt.2 (by
    have := cw
    push_cast
    linarith)
  omega

#print axioms conjecture430a

end WrittenOnTheWallII.GraphConjecture430a
