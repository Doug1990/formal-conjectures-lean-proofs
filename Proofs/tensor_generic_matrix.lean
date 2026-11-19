import Mathlib.Data.Holor
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Polynomial.Roots

namespace Arxiv.«0805.3777»

noncomputable scoped instance instTopologicalSpaceHolor {ds : List ℕ} :
    TopologicalSpace (Holor ℂ ds) :=
  inferInstanceAs <| TopologicalSpace (HolorIndex ds → ℂ)

def IsGenericRank (ds : List ℕ) (r : ℕ) : Prop :=
  ∃ U : Set (Holor ℂ ds), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank = r

lemma cprank_spec {ds : List ℕ} (x : Holor ℂ ds) : Holor.CPRankMax x.cprank x := by
  let := Classical.decPred fun n : ℕ => Holor.CPRankMax n x
  exact Nat.find_spec (p := fun n => Holor.CPRankMax n x) ⟨ds.prod, Holor.cprankMax_upper_bound x⟩

lemma cprank_le_of {ds : List ℕ} (x : Holor ℂ ds) (n : ℕ) (h : Holor.CPRankMax n x) :
    x.cprank ≤ n := by
  unfold Holor.cprank
  exact @Nat.find_min' _ (Classical.decPred _) _ _ h

/-- The index `[i, j]` of a 2-holor. -/
def idx {m n : ℕ} (i j : ℕ) (hi : i < m) (hj : j < n) : HolorIndex [m, n] :=
  ⟨[i, j], List.Forall₂.cons hi (List.Forall₂.cons hj List.Forall₂.nil)⟩

lemma ext_idx {m n : ℕ} {A B : Holor ℂ [m, n]}
    (h : ∀ i j (hi : i < m) (hj : j < n), A (idx i j hi hj) = B (idx i j hi hj)) : A = B := by
  refine funext fun t => ?_
  rcases t with ⟨l, hl⟩
  match l, hl with
  | [i, j], hl =>
    exact h i j (List.forall₂_cons.1 hl).1 (List.forall₂_cons.1 (List.forall₂_cons.1 hl).2).1
  | [], hl => cases hl
  | [_], hl => cases hl with | cons _ h2 => cases h2
  | _ :: _ :: _ :: _, hl => cases hl with | cons _ h2 => cases h2 with | cons _ h3 => cases h3

lemma holor_sum_apply {ds : List ℕ} {ι : Type} (s : Finset ι) (f : ι → Holor ℂ ds)
    (t : HolorIndex ds) : (∑ i ∈ s, f i) t = ∑ i ∈ s, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

lemma mul_idx {m n : ℕ} (x : Holor ℂ [m]) (y : Holor ℂ [n]) (i j : ℕ) (hi : i < m) (hj : j < n) :
    Holor.mul x y (idx i j hi hj) =
      x ⟨[i], List.Forall₂.cons hi List.Forall₂.nil⟩ * y ⟨[j], List.Forall₂.cons hj List.Forall₂.nil⟩ :=
  rfl

lemma vec_rank1 {d : ℕ} (y : Holor ℂ [d]) : Holor.CPRankMax1 y := by
  have h := Holor.CPRankMax1.cons y (fun _ => (1 : ℂ) : Holor ℂ []) (Holor.CPRankMax1.nil _)
  have e : (Holor.mul y (fun _ => (1 : ℂ) : Holor ℂ []) : Holor ℂ [d]) = y := by
    refine funext fun t => ?_
    show y _ * 1 = y t
    rw [mul_one]
    congr 1
    exact Subtype.ext (List.take_of_length_le (le_of_eq t.2.length_eq))
  rw [← e]
  exact h

/-- Row `i` of a 2-holor. -/
def rowv {m n : ℕ} (T : Holor ℂ [m, n]) (i : Fin m) : Holor ℂ [n] := fun t =>
  if h : t.1.headI < n then T (idx i t.1.headI i.2 h) else 0

/-- Column `j` of a 2-holor. -/
def colv {m n : ℕ} (T : Holor ℂ [m, n]) (j : Fin n) : Holor ℂ [m] := fun t =>
  if h : t.1.headI < m then T (idx t.1.headI j h j.2) else 0

lemma row_decomp {m n : ℕ} (T : Holor ℂ [m, n]) :
    T = ∑ i : Fin m, (Holor.mul (Holor.unitVec m i) (rowv T i) : Holor ℂ [m, n]) := by
  apply ext_idx
  intro i j hi hj
  rw [holor_sum_apply]
  simp only [mul_idx]
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp [Holor.unitVec, rowv, hj]
  · intro b _ hb
    have : (i : ℕ) ≠ b := fun h => hb (Fin.ext h.symm)
    simp [Holor.unitVec, this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma col_decomp {m n : ℕ} (T : Holor ℂ [m, n]) :
    T = ∑ j : Fin n, (Holor.mul (colv T j) (Holor.unitVec n j) : Holor ℂ [m, n]) := by
  apply ext_idx
  intro i j hi hj
  rw [holor_sum_apply]
  simp only [mul_idx]
  rw [Finset.sum_eq_single ⟨j, hj⟩]
  · simp [Holor.unitVec, colv, hi]
  · intro b _ hb
    have : (j : ℕ) ≠ b := fun h => hb (Fin.ext h.symm)
    simp [Holor.unitVec, this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma cprank_le_m {m n : ℕ} (T : Holor ℂ [m, n]) : T.cprank ≤ m := by
  have hs := Holor.cprankMax_sum (n := 1) Finset.univ
    (fun i : Fin m => (Holor.mul (Holor.unitVec m i) (rowv T i) : Holor ℂ [m, n]))
    (fun i _ => Holor.cprankMax_1 (Holor.CPRankMax1.cons _ _ (vec_rank1 _)))
  rw [Finset.card_univ, Fintype.card_fin, mul_one, ← row_decomp] at hs
  exact cprank_le_of _ _ hs

lemma cprank_le_n {m n : ℕ} (T : Holor ℂ [m, n]) : T.cprank ≤ n := by
  have hs := Holor.cprankMax_sum (n := 1) Finset.univ
    (fun j : Fin n => (Holor.mul (colv T j) (Holor.unitVec n j) : Holor ℂ [m, n]))
    (fun j _ => Holor.cprankMax_1 (Holor.CPRankMax1.cons _ _ (vec_rank1 _)))
  rw [Finset.card_univ, Fintype.card_fin, mul_one, ← col_decomp] at hs
  exact cprank_le_of _ _ hs

/-- Entries of a 1-holor as a function on ℕ. -/
def vecH {d : ℕ} (x : Holor ℂ [d]) (i : ℕ) : ℂ :=
  if h : i < d then x ⟨[i], List.Forall₂.cons h List.Forall₂.nil⟩ else 0

lemma decomp (m n r : ℕ) (T : Holor ℂ [m, n]) (h : Holor.CPRankMax r T) :
    ∃ u v : Fin r → ℕ → ℂ, ∀ i j (hi : i < m) (hj : j < n),
      T (idx i j hi hj) = ∑ l, u l i * v l j := by
  induction r generalizing T with
  | zero =>
    cases h
    exact ⟨fun _ _ => 0, fun _ _ => 0, fun i j hi hj => by
      rw [Finset.univ_eq_empty, Finset.sum_empty]; rfl⟩
  | succ r ih =>
    cases h with
    | succ _ x y hx hy =>
      obtain ⟨u, v, huv⟩ := ih y hy
      cases hx with
      | cons x' y' hy' =>
        refine ⟨Fin.cons (α := fun _ => ℕ → ℂ) (vecH x') u,
          Fin.cons (α := fun _ => ℕ → ℂ) (vecH y') v, ?_⟩
        intro i j hi hj
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [← huv i j hi hj]
        simp only [vecH, dif_pos hi, dif_pos hj]
        rfl

lemma lt_m {m n : ℕ} (a : Fin (min m n)) : (a : ℕ) < m := lt_of_lt_of_le a.2 (min_le_left _ _)
lemma lt_n {m n : ℕ} (a : Fin (min m n)) : (a : ℕ) < n := lt_of_lt_of_le a.2 (min_le_right _ _)

/-- The leading `min m n` square block. -/
def Sm {m n : ℕ} (T : Holor ℂ [m, n]) : Matrix (Fin (min m n)) (Fin (min m n)) ℂ :=
  Matrix.of fun a b => T (idx a.1 b.1 (lt_m a) (lt_n b))

lemma k_le {m n : ℕ} (T : Holor ℂ [m, n]) (hT : (Sm T).det ≠ 0) : min m n ≤ T.cprank := by
  obtain ⟨u, v, huv⟩ := decomp m n _ T (cprank_spec T)
  let B : Matrix (Fin (min m n)) (Fin T.cprank) ℂ := Matrix.of fun a l => u l a
  let C : Matrix (Fin T.cprank) (Fin (min m n)) ℂ := Matrix.of fun l b => v l b
  have hBC : Sm T = B * C := by
    ext a b
    rw [Matrix.mul_apply]
    exact huv _ _ _ _
  have h1 : (Sm T).rank = min m n := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hT)),
      Fintype.card_fin]
  calc min m n = (Sm T).rank := h1.symm
    _ = (B * C).rank := by rw [hBC]
    _ ≤ B.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin T.cprank) := Matrix.rank_le_card_width _
    _ = T.cprank := Fintype.card_fin _

lemma det_cont (m n : ℕ) : Continuous fun T : Holor ℂ [m, n] => (Sm T).det :=
  (continuous_matrix fun a b =>
    (continuous_apply (idx (m := m) (n := n) a.1 b.1 (lt_m a) (lt_n b))).congr
      fun _ => rfl).matrix_det

lemma dense_U (m n : ℕ) : Dense {T : Holor ℂ [m, n] | (Sm T).det ≠ 0} := by
  intro T
  let E : Holor ℂ [m, n] := fun t =>
    if t.1.headI = (t.1.drop 1).headI ∧ t.1.headI < min m n then 1 else 0
  let φ : ℂ → Holor ℂ [m, n] := fun c t => T t + c * E t
  have hφ : Continuous φ :=
    continuous_pi fun t => continuous_const.add (continuous_id.mul continuous_const)
  have h0 : φ 0 = T := by
    refine funext fun t => ?_
    show T t + 0 * E t = T t
    simp
  have hdet : ∀ c, (Sm (φ c)).det = (Matrix.charpoly (-(Sm T))).eval c := by
    intro c
    rw [Matrix.eval_charpoly]
    congr 1
    ext a b
    have e1 : Sm (φ c) a b = T (idx a.1 b.1 (lt_m a) (lt_n b)) +
        c * (if (a : ℕ) = b ∧ (a : ℕ) < min m n then 1 else 0) := rfl
    have e2 : Sm T a b = T (idx a.1 b.1 (lt_m a) (lt_n b)) := rfl
    rw [e1, Matrix.sub_apply, Matrix.neg_apply, e2, Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      rw [if_pos ⟨rfl, a.2⟩, if_pos rfl]
      ring
    · have : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
      rw [if_neg (fun h => this h.1), if_neg hab]
      ring
  have hmon : Matrix.charpoly (-(Sm T)) ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hR : {x | (Matrix.charpoly (-(Sm T))).IsRoot x}.Finite :=
    Polynomial.finite_setOfPred_isRoot hmon
  have hnhds : ({x | (Matrix.charpoly (-(Sm T))).IsRoot x} \ {0})ᶜ ∈ nhds (0 : ℂ) :=
    (hR.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hev : ∀ᶠ c in nhdsWithin (0 : ℂ) {0}ᶜ, φ c ∈ {T : Holor ℂ [m, n] | (Sm T).det ≠ 0} := by
    filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with c h1 h2
    show (Sm (φ c)).det ≠ 0
    rw [hdet]
    intro hc
    exact h1 ⟨hc, h2⟩
  have ht : Filter.Tendsto φ (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds T) := by
    rw [← h0]
    exact (hφ.tendsto 0).mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto ht hev

theorem isGenericRank_matrix (m n : ℕ) : IsGenericRank [m, n] (min m n) := by
  refine ⟨{T | (Sm T).det ≠ 0}, isOpen_compl_singleton.preimage (det_cont m n), dense_U m n, ?_⟩
  intro T hT
  exact le_antisymm (le_min (cprank_le_m T) (cprank_le_n T)) (k_le T hT)

end Arxiv.«0805.3777»

#print axioms Arxiv.«0805.3777».isGenericRank_matrix
